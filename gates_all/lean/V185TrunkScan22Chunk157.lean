import V185TrunkScan22Chunk156

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1401714 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1401714 : Nat := 118140960795 + 1401714 * 2 ^ 59
def prefixEnd_1401714 : Nat := 4983230072969 + 3 ^ 40 * 1401714 * 2
def baseEnd_1401714 : Nat := 479835348090956014152427

theorem tailTrace_1401714 : CollatzResearch.WordTrace tailWord_1401714 prefixEnd_1401714 479835348090956014152427 := by
  unfold tailWord_1401714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12781177410959261634301049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34083139762558031024802797 12781177410959261634301049)
  ·
    refine ⟨9585883058219446225725787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12781177410959261634301049 9585883058219446225725787)
    ·
      refine ⟨14378824587329169338588681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9585883058219446225725787 14378824587329169338588681)
      ·
        refine ⟨10784118440496877003941511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14378824587329169338588681 10784118440496877003941511)
        ·
          refine ⟨16176177660745315505912267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10784118440496877003941511 16176177660745315505912267)
          ·
            refine ⟨24264266491117973258868401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16176177660745315505912267 24264266491117973258868401)
            ·
              refine ⟨18198199868338479944151301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24264266491117973258868401 18198199868338479944151301)
              ·
                refine ⟨3412162475313464989528369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18198199868338479944151301 3412162475313464989528369)
                ·
                  refine ⟨2559121856485098742146277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3412162475313464989528369 2559121856485098742146277)
                  ·
                    refine ⟨479835348090956014152427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2559121856485098742146277 479835348090956014152427)
                    ·
                      rfl

theorem cell22_1401714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1401714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401714 prefixEnd_1401714 := by exact prefixLift 1401714
  have htrace : WordTrace (prefixWord ++ tailWord_1401714) baseStart_1401714 baseEnd_1401714 := by
    simpa [prefixWord, tailWord_1401714, baseEnd_1401714] using wordTrace_append hprefix tailTrace_1401714
  have hstable : (prefixWord ++ tailWord_1401714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401714).length < 2 ^ (prefixWord ++ tailWord_1401714).sum := by decide
  have hdescent : baseEnd_1401714 < baseStart_1401714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401718 : List Nat := [5, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_1401718 : Nat := 118140960795 + 1401718 * 2 ^ 59
def prefixEnd_1401718 : Nat := 4983230072969 + 3 ^ 40 * 1401718 * 2
def baseEnd_1401718 : Nat := 159945572457567112350805

theorem tailTrace_1401718 : CollatzResearch.WordTrace tailWord_1401718 prefixEnd_1401718 159945572457567112350805 := by
  unfold tailWord_1401718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3195303470988909701271863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34083237023881703480233205 3195303470988909701271863)
  ·
    refine ⟨4792955206483364551907795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3195303470988909701271863 4792955206483364551907795)
    ·
      refine ⟨7189432809725046827861693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4792955206483364551907795 7189432809725046827861693)
      ·
        refine ⟨2696037303646892560448135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7189432809725046827861693 2696037303646892560448135)
        ·
          refine ⟨4044055955470338840672203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696037303646892560448135 4044055955470338840672203)
          ·
            refine ⟨6066083933205508261008305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044055955470338840672203 6066083933205508261008305)
            ·
              refine ⟨4549562949904131195756229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6066083933205508261008305 4549562949904131195756229)
              ·
                refine ⟨853043053107024599204293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4549562949904131195756229 853043053107024599204293)
                ·
                  refine ⟨159945572457567112350805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 853043053107024599204293 159945572457567112350805)
                  ·
                    rfl

theorem cell22_1401718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_1401718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401718 prefixEnd_1401718 := by exact prefixLift 1401718
  have htrace : WordTrace (prefixWord ++ tailWord_1401718) baseStart_1401718 baseEnd_1401718 := by
    simpa [prefixWord, tailWord_1401718, baseEnd_1401718] using wordTrace_append hprefix tailTrace_1401718
  have hstable : (prefixWord ++ tailWord_1401718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401718).length < 2 ^ (prefixWord ++ tailWord_1401718).sum := by decide
  have hdescent : baseEnd_1401718 < baseStart_1401718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401733 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 2, 3]
def baseStart_1401733 : Nat := 118140960795 + 1401733 * 2 ^ 59
def prefixEnd_1401733 : Nat := 4983230072969 + 3 ^ 40 * 1401733 * 2
def baseEnd_1401733 : Nat := 479841852179246297927369

theorem tailTrace_1401733 : CollatzResearch.WordTrace tailWord_1401733 prefixEnd_1401733 479841852179246297927369 := by
  unfold tailWord_1401733
  simp only [CollatzResearch.WordTrace]
  refine ⟨51125402630768212782145853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34083601753845475188097235 51125402630768212782145853)
  ·
    refine ⟨19172025986538079793304695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51125402630768212782145853 19172025986538079793304695)
    ·
      refine ⟨28758038979807119689957043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19172025986538079793304695 28758038979807119689957043)
      ·
        refine ⟨43137058469710679534935565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28758038979807119689957043 43137058469710679534935565)
        ·
          refine ⟨16176396926141504825600837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43137058469710679534935565 16176396926141504825600837)
          ·
            refine ⟨3033074423651532154800157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16176396926141504825600837 3033074423651532154800157)
            ·
              refine ⟨1137402908869324558050059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3033074423651532154800157 1137402908869324558050059)
              ·
                refine ⟨1706104363303986837075089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137402908869324558050059 1706104363303986837075089)
                ·
                  refine ⟨1279578272477990127806317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706104363303986837075089 1279578272477990127806317)
                  ·
                    refine ⟨479841852179246297927369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279578272477990127806317 479841852179246297927369)
                    ·
                      rfl

theorem cell22_1401733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_1401733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401733 prefixEnd_1401733 := by exact prefixLift 1401733
  have htrace : WordTrace (prefixWord ++ tailWord_1401733) baseStart_1401733 baseEnd_1401733 := by
    simpa [prefixWord, tailWord_1401733, baseEnd_1401733] using wordTrace_append hprefix tailTrace_1401733
  have hstable : (prefixWord ++ tailWord_1401733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401733).length < 2 ^ (prefixWord ++ tailWord_1401733).sum := by decide
  have hdescent : baseEnd_1401733 < baseStart_1401733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401746 : List Nat := [3, 2, 3, 2, 2, 1, 1, 8]
def baseStart_1401746 : Nat := 118140960795 + 1401746 * 2 ^ 59
def prefixEnd_1401746 : Nat := 4983230072969 + 3 ^ 40 * 1401746 * 2
def baseEnd_1401746 : Nat := 53316255816102066372481

theorem tailTrace_1401746 : CollatzResearch.WordTrace tailWord_1401746 prefixEnd_1401746 53316255816102066372481 := by
  unfold tailWord_1401746
  simp only [CollatzResearch.WordTrace]
  refine ⟨12781469194930279000592273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34083917853147410668246061 12781469194930279000592273)
  ·
    refine ⟨9586101896197709250444205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12781469194930279000592273 9586101896197709250444205)
    ·
      refine ⟨3594788211074140968916577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9586101896197709250444205 3594788211074140968916577)
      ·
        refine ⟨2696091158305605726687433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3594788211074140968916577 2696091158305605726687433)
        ·
          refine ⟨2022068368729204295015575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2696091158305605726687433 2022068368729204295015575)
          ·
            refine ⟨3033102553093806442523363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022068368729204295015575 3033102553093806442523363)
            ·
              refine ⟨4549653829640709663785045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3033102553093806442523363 4549653829640709663785045)
              ·
                refine ⟨53316255816102066372481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4549653829640709663785045 53316255816102066372481)
                ·
                  rfl

theorem cell22_1401746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_1401746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401746 prefixEnd_1401746 := by exact prefixLift 1401746
  have htrace : WordTrace (prefixWord ++ tailWord_1401746) baseStart_1401746 baseEnd_1401746 := by
    simpa [prefixWord, tailWord_1401746, baseEnd_1401746] using wordTrace_append hprefix tailTrace_1401746
  have hstable : (prefixWord ++ tailWord_1401746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401746).length < 2 ^ (prefixWord ++ tailWord_1401746).sum := by decide
  have hdescent : baseEnd_1401746 < baseStart_1401746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401750 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1401750 : Nat := 118140960795 + 1401750 * 2 ^ 59
def prefixEnd_1401750 : Nat := 4983230072969 + 3 ^ 40 * 1401750 * 2
def baseEnd_1401750 : Nat := 479847671626663920252317

theorem tailTrace_1401750 : CollatzResearch.WordTrace tailWord_1401750 prefixEnd_1401750 479847671626663920252317 := by
  unfold tailWord_1401750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3195376416981664042844669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34084015114471083123676469 3195376416981664042844669)
  ·
    refine ⟨1198266156368124016066751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3195376416981664042844669 1198266156368124016066751)
    ·
      refine ⟨1797399234552186024100127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198266156368124016066751 1797399234552186024100127)
      ·
        refine ⟨2696098851828279036150191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797399234552186024100127 2696098851828279036150191)
        ·
          refine ⟨4044148277742418554225287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696098851828279036150191 4044148277742418554225287)
          ·
            refine ⟨6066222416613627831337931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044148277742418554225287 6066222416613627831337931)
            ·
              refine ⟨9099333624920441747006897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066222416613627831337931 9099333624920441747006897)
              ·
                refine ⟨6824500218690331310255173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9099333624920441747006897 6824500218690331310255173)
                ·
                  refine ⟨1279593791004437120672845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6824500218690331310255173 1279593791004437120672845)
                  ·
                    refine ⟨479847671626663920252317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279593791004437120672845 479847671626663920252317)
                    ·
                      rfl

theorem cell22_1401750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1401750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401750 prefixEnd_1401750 := by exact prefixLift 1401750
  have htrace : WordTrace (prefixWord ++ tailWord_1401750) baseStart_1401750 baseEnd_1401750 := by
    simpa [prefixWord, tailWord_1401750, baseEnd_1401750] using wordTrace_append hprefix tailTrace_1401750
  have hstable : (prefixWord ++ tailWord_1401750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401750).length < 2 ^ (prefixWord ++ tailWord_1401750).sum := by decide
  have hdescent : baseEnd_1401750 < baseStart_1401750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401829 : List Nat := [1, 3, 1, 6, 1, 2, 2, 2, 1, 3]
def baseStart_1401829 : Nat := 118140960795 + 1401829 * 2 ^ 59
def prefixEnd_1401829 : Nat := 4983230072969 + 3 ^ 40 * 1401829 * 2
def baseEnd_1401829 : Nat := 479874714941134047527075

theorem tailTrace_1401829 : CollatzResearch.WordTrace tailWord_1401829 prefixEnd_1401829 479874714941134047527075 := by
  unfold tailWord_1401829
  simp only [CollatzResearch.WordTrace]
  refine ⟨51128904038420421177640541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34085936025613614118427027 51128904038420421177640541)
  ·
    refine ⟨19173339014407657941615203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51128904038420421177640541 19173339014407657941615203)
    ·
      refine ⟨28760008521611486912422805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19173339014407657941615203 28760008521611486912422805)
      ·
        refine ⟨1348125399450538449019819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28760008521611486912422805 1348125399450538449019819)
        ·
          refine ⟨2022188099175807673529729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348125399450538449019819 2022188099175807673529729)
          ·
            refine ⟨1516641074381855755147297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022188099175807673529729 1516641074381855755147297)
            ·
              refine ⟨1137480805786391816360473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516641074381855755147297 1137480805786391816360473)
              ·
                refine ⟨853110604339793862270355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1137480805786391816360473 853110604339793862270355)
                ·
                  refine ⟨1279665906509690793405533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853110604339793862270355 1279665906509690793405533)
                  ·
                    refine ⟨479874714941134047527075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279665906509690793405533 479874714941134047527075)
                    ·
                      rfl

theorem cell22_1401829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_1401829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401829 prefixEnd_1401829 := by exact prefixLift 1401829
  have htrace : WordTrace (prefixWord ++ tailWord_1401829) baseStart_1401829 baseEnd_1401829 := by
    simpa [prefixWord, tailWord_1401829, baseEnd_1401829] using wordTrace_append hprefix tailTrace_1401829
  have hstable : (prefixWord ++ tailWord_1401829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401829).length < 2 ^ (prefixWord ++ tailWord_1401829).sum := by decide
  have hdescent : baseEnd_1401829 < baseStart_1401829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401849 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_1401849 : Nat := 118140960795 + 1401849 * 2 ^ 59
def prefixEnd_1401849 : Nat := 4983230072969 + 3 ^ 40 * 1401849 * 2
def baseEnd_1401849 : Nat := 479881561349860662027013

theorem tailTrace_1401849 : CollatzResearch.WordTrace tailWord_1401849 prefixEnd_1401849 479881561349860662027013 := by
  unfold tailWord_1401849
  simp only [CollatzResearch.WordTrace]
  refine ⟨51129633498347964593368601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34086422332231976395579067 51129633498347964593368601)
  ·
    refine ⟨38347225123760973445026451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51129633498347964593368601 38347225123760973445026451)
    ·
      refine ⟨57520837685641460167539677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38347225123760973445026451 57520837685641460167539677)
      ·
        refine ⟨21570314132115547562827379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57520837685641460167539677 21570314132115547562827379)
        ·
          refine ⟨32355471198173321344241069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21570314132115547562827379 32355471198173321344241069)
          ·
            refine ⟨12133301699314995504090401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32355471198173321344241069 12133301699314995504090401)
            ·
              refine ⟨9099976274486246628067801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12133301699314995504090401 9099976274486246628067801)
              ·
                refine ⟨6824982205864684971050851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9099976274486246628067801 6824982205864684971050851)
                ·
                  refine ⟨10237473308797027456576277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6824982205864684971050851 10237473308797027456576277)
                  ·
                    refine ⟨479881561349860662027013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10237473308797027456576277 479881561349860662027013)
                    ·
                      rfl

theorem cell22_1401849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_1401849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401849 prefixEnd_1401849 := by exact prefixLift 1401849
  have htrace : WordTrace (prefixWord ++ tailWord_1401849) baseStart_1401849 baseEnd_1401849 := by
    simpa [prefixWord, tailWord_1401849, baseEnd_1401849] using wordTrace_append hprefix tailTrace_1401849
  have hstable : (prefixWord ++ tailWord_1401849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401849).length < 2 ^ (prefixWord ++ tailWord_1401849).sum := by decide
  have hdescent : baseEnd_1401849 < baseStart_1401849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401866 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_1401866 : Nat := 118140960795 + 1401866 * 2 ^ 59
def prefixEnd_1401866 : Nat := 4983230072969 + 3 ^ 40 * 1401866 * 2
def baseEnd_1401866 : Nat := 479887380797278284351961

theorem tailTrace_1401866 : CollatzResearch.WordTrace tailWord_1401866 prefixEnd_1401866 479887380797278284351961 := by
  unfold tailWord_1401866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12782563384821594124184363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34086835692857584331158301 12782563384821594124184363)
  ·
    refine ⟨19173845077232391186276545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12782563384821594124184363 19173845077232391186276545)
    ·
      refine ⟨14380383807924293389707409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19173845077232391186276545 14380383807924293389707409)
      ·
        refine ⟨10785287855943220042280557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14380383807924293389707409 10785287855943220042280557)
        ·
          refine ⟨4044482945978707515855209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10785287855943220042280557 4044482945978707515855209)
          ·
            refine ⟨3033362209484030636891407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4044482945978707515855209 3033362209484030636891407)
            ·
              refine ⟨4550043314226045955337111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3033362209484030636891407 4550043314226045955337111)
              ·
                refine ⟨6825064971339068933005667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550043314226045955337111 6825064971339068933005667)
                ·
                  refine ⟨10237597457008603399508501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6825064971339068933005667 10237597457008603399508501)
                  ·
                    refine ⟨479887380797278284351961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10237597457008603399508501 479887380797278284351961)
                    ·
                      rfl

theorem cell22_1401866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_1401866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401866 prefixEnd_1401866 := by exact prefixLift 1401866
  have htrace : WordTrace (prefixWord ++ tailWord_1401866) baseStart_1401866 baseEnd_1401866 := by
    simpa [prefixWord, tailWord_1401866, baseEnd_1401866] using wordTrace_append hprefix tailTrace_1401866
  have hstable : (prefixWord ++ tailWord_1401866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401866).length < 2 ^ (prefixWord ++ tailWord_1401866).sum := by decide
  have hdescent : baseEnd_1401866 < baseStart_1401866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401913 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 3, 3]
def baseStart_1401913 : Nat := 118140960795 + 1401913 * 2 ^ 59
def prefixEnd_1401913 : Nat := 4983230072969 + 3 ^ 40 * 1401913 * 2
def baseEnd_1401913 : Nat := 479903469857785828426817

theorem tailTrace_1401913 : CollatzResearch.WordTrace tailWord_1401913 prefixEnd_1401913 479903469857785828426817 := by
  unfold tailWord_1401913
  simp only [CollatzResearch.WordTrace]
  refine ⟨51131967770116103523698393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34087978513410735682465595 51131967770116103523698393)
  ·
    refine ⟨38348975827587077642773795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51131967770116103523698393 38348975827587077642773795)
    ·
      refine ⟨57523463741380616464160693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38348975827587077642773795 57523463741380616464160693)
      ·
        refine ⟨5392824725754432793515065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57523463741380616464160693 5392824725754432793515065)
        ·
          refine ⟨4044618544315824595136299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5392824725754432793515065 4044618544315824595136299)
          ·
            refine ⟨6066927816473736892704449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044618544315824595136299 6066927816473736892704449)
            ·
              refine ⟨4550195862355302669528337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6066927816473736892704449 4550195862355302669528337)
              ·
                refine ⟨3412646896766477002146253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4550195862355302669528337 3412646896766477002146253)
                ·
                  refine ⟨1279742586287428875804845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3412646896766477002146253 1279742586287428875804845)
                  ·
                    refine ⟨479903469857785828426817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279742586287428875804845 479903469857785828426817)
                    ·
                      rfl

theorem cell22_1401913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_1401913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401913 prefixEnd_1401913 := by exact prefixLift 1401913
  have htrace : WordTrace (prefixWord ++ tailWord_1401913) baseStart_1401913 baseEnd_1401913 := by
    simpa [prefixWord, tailWord_1401913, baseEnd_1401913] using wordTrace_append hprefix tailTrace_1401913
  have hstable : (prefixWord ++ tailWord_1401913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401913).length < 2 ^ (prefixWord ++ tailWord_1401913).sum := by decide
  have hdescent : baseEnd_1401913 < baseStart_1401913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401930 : List Nat := [3, 1, 2, 1, 1, 2, 5, 3, 1, 3]
def baseStart_1401930 : Nat := 118140960795 + 1401930 * 2 ^ 59
def prefixEnd_1401930 : Nat := 4983230072969 + 3 ^ 40 * 1401930 * 2
def baseEnd_1401930 : Nat := 479909289305203450751765

theorem tailTrace_1401930 : CollatzResearch.WordTrace tailWord_1401930 prefixEnd_1401930 479909289305203450751765 := by
  unfold tailWord_1401930
  simp only [CollatzResearch.WordTrace]
  refine ⟨12783146952763628856766811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34088391874036343618044829 12783146952763628856766811)
  ·
    refine ⟨19174720429145443285150217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12783146952763628856766811 19174720429145443285150217)
    ·
      refine ⟨14381040321859082463862663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19174720429145443285150217 14381040321859082463862663)
      ·
        refine ⟨21571560482788623695793995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14381040321859082463862663 21571560482788623695793995)
        ·
          refine ⟨32357340724182935543690993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21571560482788623695793995 32357340724182935543690993)
          ·
            refine ⟨24268005543137201657768245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32357340724182935543690993 24268005543137201657768245)
            ·
              refine ⟨2275125519669112655415773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24268005543137201657768245 2275125519669112655415773)
              ·
                refine ⟨853172069875917245780915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2275125519669112655415773 853172069875917245780915)
                ·
                  refine ⟨1279758104813875868671373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853172069875917245780915 1279758104813875868671373)
                  ·
                    refine ⟨479909289305203450751765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279758104813875868671373 479909289305203450751765)
                    ·
                      rfl

theorem cell22_1401930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_1401930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401930 prefixEnd_1401930 := by exact prefixLift 1401930
  have htrace : WordTrace (prefixWord ++ tailWord_1401930) baseStart_1401930 baseEnd_1401930 := by
    simpa [prefixWord, tailWord_1401930, baseEnd_1401930] using wordTrace_append hprefix tailTrace_1401930
  have hstable : (prefixWord ++ tailWord_1401930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401930).length < 2 ^ (prefixWord ++ tailWord_1401930).sum := by decide
  have hdescent : baseEnd_1401930 < baseStart_1401930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401956 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1401956 : Nat := 118140960795 + 1401956 * 2 ^ 59
def prefixEnd_1401956 : Nat := 4983230072969 + 3 ^ 40 * 1401956 * 2
def baseEnd_1401956 : Nat := 479918189636548049601685

theorem tailTrace_1401956 : CollatzResearch.WordTrace tailWord_1401956 prefixEnd_1401956 479918189636548049601685 := by
  unfold tailWord_1401956
  simp only [CollatzResearch.WordTrace]
  refine ⟨25566768054480160933756861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34089024072640214578342481 25566768054480160933756861)
  ·
    refine ⟨9587538020430060350158823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25566768054480160933756861 9587538020430060350158823)
    ·
      refine ⟨14381307030645090525238235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9587538020430060350158823 14381307030645090525238235)
      ·
        refine ⟨21571960545967635787857353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14381307030645090525238235 21571960545967635787857353)
        ·
          refine ⟨16178970409475726840893015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21571960545967635787857353 16178970409475726840893015)
          ·
            refine ⟨24268455614213590261339523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16178970409475726840893015 24268455614213590261339523)
            ·
              refine ⟨36402683421320385392009285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24268455614213590261339523 36402683421320385392009285)
              ·
                refine ⟨6825503141497572261001741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36402683421320385392009285 6825503141497572261001741)
                ·
                  refine ⟨2559563678061589597875653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6825503141497572261001741 2559563678061589597875653)
                  ·
                    refine ⟨479918189636548049601685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2559563678061589597875653 479918189636548049601685)
                    ·
                      rfl

theorem cell22_1401956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1401956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401956 prefixEnd_1401956 := by exact prefixLift 1401956
  have htrace : WordTrace (prefixWord ++ tailWord_1401956) baseStart_1401956 baseEnd_1401956 := by
    simpa [prefixWord, tailWord_1401956, baseEnd_1401956] using wordTrace_append hprefix tailTrace_1401956
  have hstable : (prefixWord ++ tailWord_1401956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401956).length < 2 ^ (prefixWord ++ tailWord_1401956).sum := by decide
  have hdescent : baseEnd_1401956 < baseStart_1401956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401960 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 5]
def baseStart_1401960 : Nat := 118140960795 + 1401960 * 2 ^ 59
def prefixEnd_1401960 : Nat := 4983230072969 + 3 ^ 40 * 1401960 * 2
def baseEnd_1401960 : Nat := 159973186306097790833891

theorem tailTrace_1401960 : CollatzResearch.WordTrace tailWord_1401960 prefixEnd_1401960 159973186306097790833891 := by
  unfold tailWord_1401960
  simp only [CollatzResearch.WordTrace]
  refine ⟨25566841000472915275329667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34089121333963887033772889 25566841000472915275329667)
  ·
    refine ⟨38350261500709372912994501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25566841000472915275329667 38350261500709372912994501)
    ·
      refine ⟨7190674031383007421186469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38350261500709372912994501 7190674031383007421186469)
      ·
        refine ⟨1348251380884313891472463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7190674031383007421186469 1348251380884313891472463)
        ·
          refine ⟨2022377071326470837208695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348251380884313891472463 2022377071326470837208695)
          ·
            refine ⟨3033565606989706255813043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022377071326470837208695 3033565606989706255813043)
            ·
              refine ⟨4550348410484559383719565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3033565606989706255813043 4550348410484559383719565)
              ·
                refine ⟨1706380653931709768894837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4550348410484559383719565 1706380653931709768894837)
                ·
                  refine ⟨159973186306097790833891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1706380653931709768894837 159973186306097790833891)
                  ·
                    rfl

theorem cell22_1401960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_1401960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401960 prefixEnd_1401960 := by exact prefixLift 1401960
  have htrace : WordTrace (prefixWord ++ tailWord_1401960) baseStart_1401960 baseEnd_1401960 := by
    simpa [prefixWord, tailWord_1401960, baseEnd_1401960] using wordTrace_append hprefix tailTrace_1401960
  have hstable : (prefixWord ++ tailWord_1401960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401960).length < 2 ^ (prefixWord ++ tailWord_1401960).sum := by decide
  have hdescent : baseEnd_1401960 < baseStart_1401960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402003 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 2, 3]
def baseStart_1402003 : Nat := 118140960795 + 1402003 * 2 ^ 59
def prefixEnd_1402003 : Nat := 4983230072969 + 3 ^ 40 * 1402003 * 2
def baseEnd_1402003 : Nat := 479934278697055593676541

theorem tailTrace_1402003 : CollatzResearch.WordTrace tailWord_1402003 prefixEnd_1402003 479934278697055593676541 := by
  unfold tailWord_1402003
  simp only [CollatzResearch.WordTrace]
  refine ⟨51135250339790048894474663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34090166893193365929649775 51135250339790048894474663)
  ·
    refine ⟨76702875509685073341711995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51135250339790048894474663 76702875509685073341711995)
    ·
      refine ⟨115054313264527610012567993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76702875509685073341711995 115054313264527610012567993)
      ·
        refine ⟨86290734948395707509425995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115054313264527610012567993 86290734948395707509425995)
        ·
          refine ⟨129436102422593561264138993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86290734948395707509425995 129436102422593561264138993)
          ·
            refine ⟨97077076816945170948104245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129436102422593561264138993 97077076816945170948104245)
            ·
              refine ⟨9100975951588609776384773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97077076816945170948104245 9100975951588609776384773)
              ·
                refine ⟨1706432990922864333072145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9100975951588609776384773 1706432990922864333072145)
                ·
                  refine ⟨1279824743192148249804109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706432990922864333072145 1279824743192148249804109)
                  ·
                    refine ⟨479934278697055593676541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279824743192148249804109 479934278697055593676541)
                    ·
                      rfl

theorem cell22_1402003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 3].length) (baseStart_1402003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402003 prefixEnd_1402003 := by exact prefixLift 1402003
  have htrace : WordTrace (prefixWord ++ tailWord_1402003) baseStart_1402003 baseEnd_1402003 := by
    simpa [prefixWord, tailWord_1402003, baseEnd_1402003] using wordTrace_append hprefix tailTrace_1402003
  have hstable : (prefixWord ++ tailWord_1402003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402003).length < 2 ^ (prefixWord ++ tailWord_1402003).sum := by decide
  have hdescent : baseEnd_1402003 < baseStart_1402003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402020 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_1402020 : Nat := 118140960795 + 1402020 * 2 ^ 59
def prefixEnd_1402020 : Nat := 4983230072969 + 3 ^ 40 * 1402020 * 2
def baseEnd_1402020 : Nat := 479940098144473216001489

theorem tailTrace_1402020 : CollatzResearch.WordTrace tailWord_1402020 prefixEnd_1402020 479940098144473216001489 := by
  unfold tailWord_1402020
  simp only [CollatzResearch.WordTrace]
  refine ⟨25567935190364230398921757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34090580253818973865229009 25567935190364230398921757)
  ·
    refine ⟨9587975696386586399595659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25567935190364230398921757 9587975696386586399595659)
    ·
      refine ⟨14381963544579879599393489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9587975696386586399595659 14381963544579879599393489)
      ·
        refine ⟨10786472658434909699545117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14381963544579879599393489 10786472658434909699545117)
        ·
          refine ⟨4044927246913091137329419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10786472658434909699545117 4044927246913091137329419)
          ·
            refine ⟨6067390870369636705994129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044927246913091137329419 6067390870369636705994129)
            ·
              refine ⟨4550543152777227529495597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6067390870369636705994129 4550543152777227529495597)
              ·
                refine ⟨1706453682291460323560849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4550543152777227529495597 1706453682291460323560849)
                ·
                  refine ⟨1279840261718595242670637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706453682291460323560849 1279840261718595242670637)
                  ·
                    refine ⟨479940098144473216001489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279840261718595242670637 479940098144473216001489)
                    ·
                      rfl

theorem cell22_1402020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_1402020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402020 prefixEnd_1402020 := by exact prefixLift 1402020
  have htrace : WordTrace (prefixWord ++ tailWord_1402020) baseStart_1402020 baseEnd_1402020 := by
    simpa [prefixWord, tailWord_1402020, baseEnd_1402020] using wordTrace_append hprefix tailTrace_1402020
  have hstable : (prefixWord ++ tailWord_1402020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402020).length < 2 ^ (prefixWord ++ tailWord_1402020).sum := by decide
  have hdescent : baseEnd_1402020 < baseStart_1402020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402123 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 6]
def baseStart_1402123 : Nat := 118140960795 + 1402123 * 2 ^ 59
def prefixEnd_1402123 : Nat := 4983230072969 + 3 ^ 40 * 1402123 * 2
def baseEnd_1402123 : Nat := 159991785716471760225391

theorem tailTrace_1402123 : CollatzResearch.WordTrace tailWord_1402123 prefixEnd_1402123 159991785716471760225391 := by
  unfold tailWord_1402123
  simp only [CollatzResearch.WordTrace]
  refine ⟨51139627099355309388843023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34093084732903539592562015 51139627099355309388843023)
  ·
    refine ⟨76709440649032964083264535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51139627099355309388843023 76709440649032964083264535)
    ·
      refine ⟨115064160973549446124896803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76709440649032964083264535 115064160973549446124896803)
      ·
        refine ⟨172596241460324169187345205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115064160973549446124896803 172596241460324169187345205)
        ·
          refine ⟨16180897636905390861313613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172596241460324169187345205 16180897636905390861313613)
          ·
            refine ⟨6067836613839521572992605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16180897636905390861313613 6067836613839521572992605)
            ·
              refine ⟨2275438730189820589872227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6067836613839521572992605 2275438730189820589872227)
              ·
                refine ⟨3413158095284730884808341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275438730189820589872227 3413158095284730884808341)
                ·
                  refine ⟨159991785716471760225391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3413158095284730884808341 159991785716471760225391)
                  ·
                    rfl

theorem cell22_1402123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 6].length) (baseStart_1402123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402123 prefixEnd_1402123 := by exact prefixLift 1402123
  have htrace : WordTrace (prefixWord ++ tailWord_1402123) baseStart_1402123 baseEnd_1402123 := by
    simpa [prefixWord, tailWord_1402123, baseEnd_1402123] using wordTrace_append hprefix tailTrace_1402123
  have hstable : (prefixWord ++ tailWord_1402123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402123).length < 2 ^ (prefixWord ++ tailWord_1402123).sum := by decide
  have hdescent : baseEnd_1402123 < baseStart_1402123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402172 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_1402172 : Nat := 118140960795 + 1402172 * 2 ^ 59
def prefixEnd_1402172 : Nat := 4983230072969 + 3 ^ 40 * 1402172 * 2
def baseEnd_1402172 : Nat := 479992130850795486201023

theorem tailTrace_1402172 : CollatzResearch.WordTrace tailWord_1402172 prefixEnd_1402172 479992130850795486201023 := by
  unfold tailWord_1402172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25570707138088895378688385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34094276184118527171584513 25570707138088895378688385)
  ·
    refine ⟨19178030353566671534016289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25570707138088895378688385 19178030353566671534016289)
    ·
      refine ⟨14383522765175003650512217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19178030353566671534016289 14383522765175003650512217)
      ·
        refine ⟨10787642073881252737884163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14383522765175003650512217 10787642073881252737884163)
        ·
          refine ⟨16181463110821879106826245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10787642073881252737884163 16181463110821879106826245)
          ·
            refine ⟨3034024333279102332529921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16181463110821879106826245 3034024333279102332529921)
            ·
              refine ⟨2275518249959326749397441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3034024333279102332529921 2275518249959326749397441)
              ·
                refine ⟨1706638687469495062048081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275518249959326749397441 1706638687469495062048081)
                ·
                  refine ⟨1279979015602121296536061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706638687469495062048081 1279979015602121296536061)
                  ·
                    refine ⟨479992130850795486201023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279979015602121296536061 479992130850795486201023)
                    ·
                      rfl

theorem cell22_1402172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_1402172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402172 prefixEnd_1402172 := by exact prefixLift 1402172
  have htrace : WordTrace (prefixWord ++ tailWord_1402172) baseStart_1402172 baseEnd_1402172 := by
    simpa [prefixWord, tailWord_1402172, baseEnd_1402172] using wordTrace_append hprefix tailTrace_1402172
  have hstable : (prefixWord ++ tailWord_1402172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402172).length < 2 ^ (prefixWord ++ tailWord_1402172).sum := by decide
  have hdescent : baseEnd_1402172 < baseStart_1402172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402189 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1402189 : Nat := 118140960795 + 1402189 * 2 ^ 59
def prefixEnd_1402189 : Nat := 4983230072969 + 3 ^ 40 * 1402189 * 2
def baseEnd_1402189 : Nat := 479997950298213108525971

theorem tailTrace_1402189 : CollatzResearch.WordTrace tailWord_1402189 prefixEnd_1402189 479997950298213108525971 := by
  unfold tailWord_1402189
  simp only [CollatzResearch.WordTrace]
  refine ⟨51142034317116202660745621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34094689544744135107163747 51142034317116202660745621)
  ·
    refine ⟨2397282858614821999722451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51142034317116202660745621 2397282858614821999722451)
    ·
      refine ⟨3595924287922232999583677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397282858614821999722451 3595924287922232999583677)
      ·
        refine ⟨1348471607970837374843879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3595924287922232999583677 1348471607970837374843879)
        ·
          refine ⟨2022707411956256062265819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348471607970837374843879 2022707411956256062265819)
          ·
            refine ⟨3034061117934384093398729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022707411956256062265819 3034061117934384093398729)
            ·
              refine ⟨2275545838450788070049047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3034061117934384093398729 2275545838450788070049047)
              ·
                refine ⟨3413318757676182105073571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275545838450788070049047 3413318757676182105073571)
                ·
                  refine ⟨5119978136514273157610357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3413318757676182105073571 5119978136514273157610357)
                  ·
                    refine ⟨479997950298213108525971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5119978136514273157610357 479997950298213108525971)
                    ·
                      rfl

theorem cell22_1402189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1402189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402189 prefixEnd_1402189 := by exact prefixLift 1402189
  have htrace : WordTrace (prefixWord ++ tailWord_1402189) baseStart_1402189 baseEnd_1402189 := by
    simpa [prefixWord, tailWord_1402189, baseEnd_1402189] using wordTrace_append hprefix tailTrace_1402189
  have hstable : (prefixWord ++ tailWord_1402189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402189).length < 2 ^ (prefixWord ++ tailWord_1402189).sum := by decide
  have hdescent : baseEnd_1402189 < baseStart_1402189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402200 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 3, 3]
def baseStart_1402200 : Nat := 118140960795 + 1402200 * 2 ^ 59
def prefixEnd_1402200 : Nat := 4983230072969 + 3 ^ 40 * 1402200 * 2
def baseEnd_1402200 : Nat := 480001715823012746500937

theorem tailTrace_1402200 : CollatzResearch.WordTrace tailWord_1402200 prefixEnd_1402200 480001715823012746500937 := by
  unfold tailWord_1402200
  simp only [CollatzResearch.WordTrace]
  refine ⟨25571217760038175769698027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34094957013384234359597369 25571217760038175769698027)
  ·
    refine ⟨38356826640057263654547041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25571217760038175769698027 38356826640057263654547041)
    ·
      refine ⟨28767619980042947740910281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38356826640057263654547041 28767619980042947740910281)
      ·
        refine ⟨21575714985032210805682711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28767619980042947740910281 21575714985032210805682711)
        ·
          refine ⟨32363572477548316208524067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21575714985032210805682711 32363572477548316208524067)
          ·
            refine ⟨48545358716322474312786101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32363572477548316208524067 48545358716322474312786101)
            ·
              refine ⟨4551127379655231966823697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48545358716322474312786101 4551127379655231966823697)
              ·
                refine ⟨3413345534741423975117773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4551127379655231966823697 3413345534741423975117773)
                ·
                  refine ⟨1280004575528033990669165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3413345534741423975117773 1280004575528033990669165)
                  ·
                    refine ⟨480001715823012746500937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280004575528033990669165 480001715823012746500937)
                    ·
                      rfl

theorem cell22_1402200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_1402200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402200 prefixEnd_1402200 := by exact prefixLift 1402200
  have htrace : WordTrace (prefixWord ++ tailWord_1402200) baseStart_1402200 baseEnd_1402200 := by
    simpa [prefixWord, tailWord_1402200, baseEnd_1402200] using wordTrace_append hprefix tailTrace_1402200
  have hstable : (prefixWord ++ tailWord_1402200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402200).length < 2 ^ (prefixWord ++ tailWord_1402200).sum := by decide
  have hdescent : baseEnd_1402200 < baseStart_1402200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402213 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 7]
def baseStart_1402213 : Nat := 118140960795 + 1402213 * 2 ^ 59
def prefixEnd_1402213 : Nat := 4983230072969 + 3 ^ 40 * 1402213 * 2
def baseEnd_1402213 : Nat := 160002055329561681975299

theorem tailTrace_1402213 : CollatzResearch.WordTrace tailWord_1402213 prefixEnd_1402213 160002055329561681975299 := by
  unfold tailWord_1402213
  simp only [CollatzResearch.WordTrace]
  refine ⟨51142909669029254759619293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34095273112686169839746195 51142909669029254759619293)
  ·
    refine ⟨19178591125885970534857235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51142909669029254759619293 19178591125885970534857235)
    ·
      refine ⟨28767886688828955802285853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19178591125885970534857235 28767886688828955802285853)
      ·
        refine ⟨10787957508310858425857195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28767886688828955802285853 10787957508310858425857195)
        ·
          refine ⟨16181936262466287638785793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10787957508310858425857195 16181936262466287638785793)
          ·
            refine ⟨12136452196849715729089345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16181936262466287638785793 12136452196849715729089345)
            ·
              refine ⟨9102339147637286796817009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12136452196849715729089345 9102339147637286796817009)
              ·
                refine ⟨6826754360727965097612757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9102339147637286796817009 6826754360727965097612757)
                ·
                  refine ⟨160002055329561681975299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6826754360727965097612757 160002055329561681975299)
                  ·
                    rfl

theorem cell22_1402213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_1402213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402213 prefixEnd_1402213 := by exact prefixLift 1402213
  have htrace : WordTrace (prefixWord ++ tailWord_1402213) baseStart_1402213 baseEnd_1402213 := by
    simpa [prefixWord, tailWord_1402213, baseEnd_1402213] using wordTrace_append hprefix tailTrace_1402213
  have hstable : (prefixWord ++ tailWord_1402213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402213).length < 2 ^ (prefixWord ++ tailWord_1402213).sum := by decide
  have hdescent : baseEnd_1402213 < baseStart_1402213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402247 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 5]
def baseStart_1402247 : Nat := 118140960795 + 1402247 * 2 ^ 59
def prefixEnd_1402247 : Nat := 4983230072969 + 3 ^ 40 * 1402247 * 2
def baseEnd_1402247 : Nat := 160005934961173430191931

theorem tailTrace_1402247 : CollatzResearch.WordTrace tailWord_1402247 prefixEnd_1402247 160005934961173430191931 := by
  unfold tailWord_1402247
  simp only [CollatzResearch.WordTrace]
  refine ⟨51144149750906078566356995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34096099833937385710904663 51144149750906078566356995)
  ·
    refine ⟨76716224626359117849535493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51144149750906078566356995 76716224626359117849535493)
    ·
      refine ⟨14384292117442334596787905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76716224626359117849535493 14384292117442334596787905)
      ·
        refine ⟨10788219088081750947590929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14384292117442334596787905 10788219088081750947590929)
        ·
          refine ⟨8091164316061313210693197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10788219088081750947590929 8091164316061313210693197)
          ·
            refine ⟨3034186618522992454009949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8091164316061313210693197 3034186618522992454009949)
            ·
              refine ⟨1137819981946122170253731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3034186618522992454009949 1137819981946122170253731)
              ·
                refine ⟨1706729972919183255380597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137819981946122170253731 1706729972919183255380597)
                ·
                  refine ⟨160005934961173430191931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1706729972919183255380597 160005934961173430191931)
                  ·
                    rfl

theorem cell22_1402247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 5].length) (baseStart_1402247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402247 prefixEnd_1402247 := by exact prefixLift 1402247
  have htrace : WordTrace (prefixWord ++ tailWord_1402247) baseStart_1402247 baseEnd_1402247 := by
    simpa [prefixWord, tailWord_1402247, baseEnd_1402247] using wordTrace_append hprefix tailTrace_1402247
  have hstable : (prefixWord ++ tailWord_1402247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402247).length < 2 ^ (prefixWord ++ tailWord_1402247).sum := by decide
  have hdescent : baseEnd_1402247 < baseStart_1402247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402268 : List Nat := [2, 2, 3, 4, 1, 2, 1, 3, 1, 3]
def baseStart_1402268 : Nat := 118140960795 + 1402268 * 2 ^ 59
def prefixEnd_1402268 : Nat := 4983230072969 + 3 ^ 40 * 1402268 * 2
def baseEnd_1402268 : Nat := 480024993612683235800729

theorem tailTrace_1402268 : CollatzResearch.WordTrace tailWord_1402268 prefixEnd_1402268 480024993612683235800729 := by
  unfold tailWord_1402268
  simp only [CollatzResearch.WordTrace]
  refine ⟨25572457841914999576435729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34096610455886666101914305 25572457841914999576435729)
  ·
    refine ⟨19179343381436249682326797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25572457841914999576435729 19179343381436249682326797)
    ·
      refine ⟨7192253768038593630872549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19179343381436249682326797 7192253768038593630872549)
      ·
        refine ⟨1348547581507236305788603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7192253768038593630872549 1348547581507236305788603)
        ·
          refine ⟨2022821372260854458682905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348547581507236305788603 2022821372260854458682905)
          ·
            refine ⟨1517116029195640844012179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022821372260854458682905 1517116029195640844012179)
            ·
              refine ⟨2275674043793461266018269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517116029195640844012179 2275674043793461266018269)
              ·
                refine ⟨853377766422547974756851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2275674043793461266018269 853377766422547974756851)
                ·
                  refine ⟨1280066649633821962135277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853377766422547974756851 1280066649633821962135277)
                  ·
                    refine ⟨480024993612683235800729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280066649633821962135277 480024993612683235800729)
                    ·
                      rfl

theorem cell22_1402268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_1402268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402268 prefixEnd_1402268 := by exact prefixLift 1402268
  have htrace : WordTrace (prefixWord ++ tailWord_1402268) baseStart_1402268 baseEnd_1402268 := by
    simpa [prefixWord, tailWord_1402268, baseEnd_1402268] using wordTrace_append hprefix tailTrace_1402268
  have hstable : (prefixWord ++ tailWord_1402268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402268).length < 2 ^ (prefixWord ++ tailWord_1402268).sum := by decide
  have hdescent : baseEnd_1402268 < baseStart_1402268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402288 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_1402288 : Nat := 118140960795 + 1402288 * 2 ^ 59
def prefixEnd_1402288 : Nat := 4983230072969 + 3 ^ 40 * 1402288 * 2
def baseEnd_1402288 : Nat := 480031840021409850300667

theorem tailTrace_1402288 : CollatzResearch.WordTrace tailWord_1402288 prefixEnd_1402288 480031840021409850300667 := by
  unfold tailWord_1402288
  simp only [CollatzResearch.WordTrace]
  refine ⟨25572822571878771284299759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34097096762505028379066345 25572822571878771284299759)
  ·
    refine ⟨38359233857818156926449639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25572822571878771284299759 38359233857818156926449639)
    ·
      refine ⟨57538850786727235389674459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38359233857818156926449639 57538850786727235389674459)
      ·
        refine ⟨86308276180090853084511689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57538850786727235389674459 86308276180090853084511689)
        ·
          refine ⟨64731207135068139813383767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86308276180090853084511689 64731207135068139813383767)
          ·
            refine ⟨97096810702602209720075651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64731207135068139813383767 97096810702602209720075651)
            ·
              refine ⟨145645216053903314580113477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97096810702602209720075651 145645216053903314580113477)
              ·
                refine ⟨27308478010106871483771277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145645216053903314580113477 27308478010106871483771277)
                ·
                  refine ⟨10240679253790076806414229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27308478010106871483771277 10240679253790076806414229)
                  ·
                    refine ⟨480031840021409850300667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10240679253790076806414229 480031840021409850300667)
                    ·
                      rfl

theorem cell22_1402288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_1402288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402288 prefixEnd_1402288 := by exact prefixLift 1402288
  have htrace : WordTrace (prefixWord ++ tailWord_1402288) baseStart_1402288 baseEnd_1402288 := by
    simpa [prefixWord, tailWord_1402288, baseEnd_1402288] using wordTrace_append hprefix tailTrace_1402288
  have hstable : (prefixWord ++ tailWord_1402288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402288).length < 2 ^ (prefixWord ++ tailWord_1402288).sum := by decide
  have hdescent : baseEnd_1402288 < baseStart_1402288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402350 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1402350 : Nat := 118140960795 + 1402350 * 2 ^ 59
def prefixEnd_1402350 : Nat := 4983230072969 + 3 ^ 40 * 1402350 * 2
def baseEnd_1402350 : Nat := 480053063888462355250477

theorem tailTrace_1402350 : CollatzResearch.WordTrace tailWord_1402350 prefixEnd_1402350 480053063888462355250477 := by
  unfold tailWord_1402350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6393488308691615894669563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34098604313021951438237669 6393488308691615894669563)
  ·
    refine ⟨9590232463037423842004345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6393488308691615894669563 9590232463037423842004345)
    ·
      refine ⟨7192674347278067881503259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9590232463037423842004345 7192674347278067881503259)
      ·
        refine ⟨10789011520917101822254889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7192674347278067881503259 10789011520917101822254889)
        ·
          refine ⟨8091758640687826366691167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10789011520917101822254889 8091758640687826366691167)
          ·
            refine ⟨12137637961031739550036751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8091758640687826366691167 12137637961031739550036751)
            ·
              refine ⟨18206456941547609325055127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12137637961031739550036751 18206456941547609325055127)
              ·
                refine ⟨27309685412321413987582691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18206456941547609325055127 27309685412321413987582691)
                ·
                  refine ⟨40964528118482120981374037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27309685412321413987582691 40964528118482120981374037)
                  ·
                    refine ⟨480053063888462355250477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40964528118482120981374037 480053063888462355250477)
                    ·
                      rfl

theorem cell22_1402350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1402350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402350 prefixEnd_1402350 := by exact prefixLift 1402350
  have htrace : WordTrace (prefixWord ++ tailWord_1402350) baseStart_1402350 baseEnd_1402350 := by
    simpa [prefixWord, tailWord_1402350, baseEnd_1402350] using wordTrace_append hprefix tailTrace_1402350
  have hstable : (prefixWord ++ tailWord_1402350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402350).length < 2 ^ (prefixWord ++ tailWord_1402350).sum := by decide
  have hdescent : baseEnd_1402350 < baseStart_1402350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402369 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1402369 : Nat := 118140960795 + 1402369 * 2 ^ 59
def prefixEnd_1402369 : Nat := 4983230072969 + 3 ^ 40 * 1402369 * 2
def baseEnd_1402369 : Nat := 480059567976752639025419

theorem tailTrace_1402369 : CollatzResearch.WordTrace tailWord_1402369 prefixEnd_1402369 480059567976752639025419 := by
  unfold tailWord_1402369
  simp only [CollatzResearch.WordTrace]
  refine ⟨51148599456464093402298161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34099066304309395601532107 51148599456464093402298161)
  ·
    refine ⟨38361449592348070051723621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51148599456464093402298161 38361449592348070051723621)
    ·
      refine ⟨7192771798565263134698179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38361449592348070051723621 7192771798565263134698179)
      ·
        refine ⟨10789157697847894702047269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7192771798565263134698179 10789157697847894702047269)
        ·
          refine ⟨2022967068346480256633863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10789157697847894702047269 2022967068346480256633863)
          ·
            refine ⟨3034450602519720384950795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022967068346480256633863 3034450602519720384950795)
            ·
              refine ⟨4551675903779580577426193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034450602519720384950795 4551675903779580577426193)
              ·
                refine ⟨3413756927834685433069645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4551675903779580577426193 3413756927834685433069645)
                ·
                  refine ⟨1280158847938007037401117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3413756927834685433069645 1280158847938007037401117)
                  ·
                    refine ⟨480059567976752639025419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280158847938007037401117 480059567976752639025419)
                    ·
                      rfl

theorem cell22_1402369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1402369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402369 prefixEnd_1402369 := by exact prefixLift 1402369
  have htrace : WordTrace (prefixWord ++ tailWord_1402369) baseStart_1402369 baseEnd_1402369 := by
    simpa [prefixWord, tailWord_1402369, baseEnd_1402369] using wordTrace_append hprefix tailTrace_1402369
  have hstable : (prefixWord ++ tailWord_1402369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402369).length < 2 ^ (prefixWord ++ tailWord_1402369).sum := by decide
  have hdescent : baseEnd_1402369 < baseStart_1402369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402442 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_1402442 : Nat := 118140960795 + 1402442 * 2 ^ 59
def prefixEnd_1402442 : Nat := 4983230072969 + 3 ^ 40 * 1402442 * 2
def baseEnd_1402442 : Nat := 480084557368604781950195

theorem tailTrace_1402442 : CollatzResearch.WordTrace tailWord_1402442 prefixEnd_1402442 480084557368604781950195 := by
  unfold tailWord_1402442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12787815496299906717426395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34100841323466417913137053 12787815496299906717426395)
  ·
    refine ⟨19181723244449860076139593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12787815496299906717426395 19181723244449860076139593)
    ·
      refine ⟨14386292433337395057104695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19181723244449860076139593 14386292433337395057104695)
      ·
        refine ⟨21579438650006092585657043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14386292433337395057104695 21579438650006092585657043)
        ·
          refine ⟨32369157975009138878485565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21579438650006092585657043 32369157975009138878485565)
          ·
            refine ⟨12138434240628427079432087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32369157975009138878485565 12138434240628427079432087)
            ·
              refine ⟨18207651360942640619148131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12138434240628427079432087 18207651360942640619148131)
              ·
                refine ⟨27311477041413960928722197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18207651360942640619148131 27311477041413960928722197)
                ·
                  refine ⟨1280225486316279418533853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27311477041413960928722197 1280225486316279418533853)
                  ·
                    refine ⟨480084557368604781950195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280225486316279418533853 480084557368604781950195)
                    ·
                      rfl

theorem cell22_1402442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_1402442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402442 prefixEnd_1402442 := by exact prefixLift 1402442
  have htrace : WordTrace (prefixWord ++ tailWord_1402442) baseStart_1402442 baseEnd_1402442 := by
    simpa [prefixWord, tailWord_1402442, baseEnd_1402442] using wordTrace_append hprefix tailTrace_1402442
  have hstable : (prefixWord ++ tailWord_1402442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402442).length < 2 ^ (prefixWord ++ tailWord_1402442).sum := by decide
  have hdescent : baseEnd_1402442 < baseStart_1402442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402444 : List Nat := [2, 2, 1, 3, 1, 3, 3, 3, 4]
def baseStart_1402444 : Nat := 118140960795 + 1402444 * 2 ^ 59
def prefixEnd_1402444 : Nat := 4983230072969 + 3 ^ 40 * 1402444 * 2
def baseEnd_1402444 : Nat := 160028414003159147800063

theorem tailTrace_1402444 : CollatzResearch.WordTrace tailWord_1402444 prefixEnd_1402444 160028414003159147800063 := by
  unfold tailWord_1402444
  simp only [CollatzResearch.WordTrace]
  refine ⟨25575667465596190605639193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34100889954128254140852257 25575667465596190605639193)
  ·
    refine ⟨19181750599197142954229395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25575667465596190605639193 19181750599197142954229395)
    ·
      refine ⟨28772625898795714431344093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19181750599197142954229395 28772625898795714431344093)
      ·
        refine ⟨10789734712048392911754035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28772625898795714431344093 10789734712048392911754035)
        ·
          refine ⟨16184602068072589367631053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10789734712048392911754035 16184602068072589367631053)
          ·
            refine ⟨6069225775527221012861645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16184602068072589367631053 6069225775527221012861645)
            ·
              refine ⟨2275959665822707879823117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6069225775527221012861645 2275959665822707879823117)
              ·
                refine ⟨853484874683515454933669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2275959665822707879823117 853484874683515454933669)
                ·
                  refine ⟨160028414003159147800063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 853484874683515454933669 160028414003159147800063)
                  ·
                    rfl

theorem cell22_1402444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_1402444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402444 prefixEnd_1402444 := by exact prefixLift 1402444
  have htrace : WordTrace (prefixWord ++ tailWord_1402444) baseStart_1402444 baseEnd_1402444 := by
    simpa [prefixWord, tailWord_1402444, baseEnd_1402444] using wordTrace_append hprefix tailTrace_1402444
  have hstable : (prefixWord ++ tailWord_1402444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402444).length < 2 ^ (prefixWord ++ tailWord_1402444).sum := by decide
  have hdescent : baseEnd_1402444 < baseStart_1402444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402455 : List Nat := [1, 1, 3, 2, 2, 3, 10]
def baseStart_1402455 : Nat := 118140960795 + 1402455 * 2 ^ 59
def prefixEnd_1402455 : Nat := 4983230072969 + 3 ^ 40 * 1402455 * 2
def baseEnd_1402455 : Nat := 17781074353121373384265

theorem tailTrace_1402455 : CollatzResearch.WordTrace tailWord_1402455 prefixEnd_1402455 17781074353121373384265 := by
  unfold tailWord_1402455
  simp only [CollatzResearch.WordTrace]
  refine ⟨51151736134152530089928819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34101157422768353393285879 51151736134152530089928819)
  ·
    refine ⟨76727604201228795134893229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51151736134152530089928819 76727604201228795134893229)
    ·
      refine ⟨28772851575460798175584961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76727604201228795134893229 28772851575460798175584961)
      ·
        refine ⟨21579638681595598631688721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28772851575460798175584961 21579638681595598631688721)
        ·
          refine ⟨16184729011196698973766541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21579638681595598631688721 16184729011196698973766541)
          ·
            refine ⟨6069273379198762115162453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16184729011196698973766541 6069273379198762115162453)
            ·
              refine ⟨17781074353121373384265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6069273379198762115162453 17781074353121373384265)
              ·
                rfl

theorem cell22_1402455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 10].length) (baseStart_1402455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402455 prefixEnd_1402455 := by exact prefixLift 1402455
  have htrace : WordTrace (prefixWord ++ tailWord_1402455) baseStart_1402455 baseEnd_1402455 := by
    simpa [prefixWord, tailWord_1402455, baseEnd_1402455] using wordTrace_append hprefix tailTrace_1402455
  have hstable : (prefixWord ++ tailWord_1402455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402455).length < 2 ^ (prefixWord ++ tailWord_1402455).sum := by decide
  have hdescent : baseEnd_1402455 < baseStart_1402455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402472 : List Nat := [2, 1, 4, 3, 1, 1, 1, 9]
def baseStart_1402472 : Nat := 118140960795 + 1402472 * 2 ^ 59
def prefixEnd_1402472 : Nat := 4983230072969 + 3 ^ 40 * 1402472 * 2
def baseEnd_1402472 : Nat := 53343869664632744855567

theorem tailTrace_1402472 : CollatzResearch.WordTrace tailWord_1402472 prefixEnd_1402472 53343869664632744855567 := by
  unfold tailWord_1402472
  simp only [CollatzResearch.WordTrace]
  refine ⟨25576178087545470996648835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34101570783393961328865113 25576178087545470996648835)
  ·
    refine ⟨38364267131318206494973253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25576178087545470996648835 38364267131318206494973253)
    ·
      refine ⟨7193300087122163717807485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38364267131318206494973253 7193300087122163717807485)
      ·
        refine ⟨2697487532670811394177807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7193300087122163717807485 2697487532670811394177807)
        ·
          refine ⟨4046231299006217091266711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2697487532670811394177807 4046231299006217091266711)
          ·
            refine ⟨6069346948509325636900067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046231299006217091266711 6069346948509325636900067)
            ·
              refine ⟨9104020422763988455350101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069346948509325636900067 9104020422763988455350101)
              ·
                refine ⟨53343869664632744855567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9104020422763988455350101 53343869664632744855567)
                ·
                  rfl

theorem cell22_1402472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 9].length) (baseStart_1402472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402472 prefixEnd_1402472 := by exact prefixLift 1402472
  have htrace : WordTrace (prefixWord ++ tailWord_1402472) baseStart_1402472 baseEnd_1402472 := by
    simpa [prefixWord, tailWord_1402472, baseEnd_1402472] using wordTrace_append hprefix tailTrace_1402472
  have hstable : (prefixWord ++ tailWord_1402472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402472).length < 2 ^ (prefixWord ++ tailWord_1402472).sum := by decide
  have hdescent : baseEnd_1402472 < baseStart_1402472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402487 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 5, 3]
def baseStart_1402487 : Nat := 118140960795 + 1402487 * 2 ^ 59
def prefixEnd_1402487 : Nat := 4983230072969 + 3 ^ 40 * 1402487 * 2
def baseEnd_1402487 : Nat := 480099961788239664575057

theorem tailTrace_1402487 : CollatzResearch.WordTrace tailWord_1402487 prefixEnd_1402487 480099961788239664575057 := by
  unfold tailWord_1402487
  simp only [CollatzResearch.WordTrace]
  refine ⟨51152903270036599555093715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34101935513357733036729143 51152903270036599555093715)
  ·
    refine ⟨76729354905054899332640573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51152903270036599555093715 76729354905054899332640573)
    ·
      refine ⟨28773508089395587249740215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76729354905054899332640573 28773508089395587249740215)
      ·
        refine ⟨43160262134093380874610323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28773508089395587249740215 43160262134093380874610323)
        ·
          refine ⟨64740393201140071311915485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43160262134093380874610323 64740393201140071311915485)
          ·
            refine ⟨24277647450427526741968307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64740393201140071311915485 24277647450427526741968307)
            ·
              refine ⟨36416471175641290112952461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24277647450427526741968307 36416471175641290112952461)
              ·
                refine ⟨13656176690865483792357173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36416471175641290112952461 13656176690865483792357173)
                ·
                  refine ⟨1280266564768639105533485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13656176690865483792357173 1280266564768639105533485)
                  ·
                    refine ⟨480099961788239664575057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280266564768639105533485 480099961788239664575057)
                    ·
                      rfl

theorem cell22_1402487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_1402487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402487 prefixEnd_1402487 := by exact prefixLift 1402487
  have htrace : WordTrace (prefixWord ++ tailWord_1402487) baseStart_1402487 baseEnd_1402487 := by
    simpa [prefixWord, tailWord_1402487, baseEnd_1402487] using wordTrace_append hprefix tailTrace_1402487
  have hstable : (prefixWord ++ tailWord_1402487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402487).length < 2 ^ (prefixWord ++ tailWord_1402487).sum := by decide
  have hdescent : baseEnd_1402487 < baseStart_1402487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402532 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1402532 : Nat := 118140960795 + 1402532 * 2 ^ 59
def prefixEnd_1402532 : Nat := 4983230072969 + 3 ^ 40 * 1402532 * 2
def baseEnd_1402532 : Nat := 480115366207874547199919

theorem tailTrace_1402532 : CollatzResearch.WordTrace tailWord_1402532 prefixEnd_1402532 480115366207874547199919 := by
  unfold tailWord_1402532
  simp only [CollatzResearch.WordTrace]
  refine ⟨25577272277436786120240925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34103029703249048160321233 25577272277436786120240925)
  ·
    refine ⟨9591477104038794795090347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25577272277436786120240925 9591477104038794795090347)
    ·
      refine ⟨14387215656058192192635521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9591477104038794795090347 14387215656058192192635521)
      ·
        refine ⟨10790411742043644144476641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14387215656058192192635521 10790411742043644144476641)
        ·
          refine ⟨8092808806532733108357481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10790411742043644144476641 8092808806532733108357481)
          ·
            refine ⟨6069606604899549831268111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8092808806532733108357481 6069606604899549831268111)
            ·
              refine ⟨9104409907349324746902167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069606604899549831268111 9104409907349324746902167)
              ·
                refine ⟨13656614861023987120353251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9104409907349324746902167 13656614861023987120353251)
                ·
                  refine ⟨20484922291535980680529877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13656614861023987120353251 20484922291535980680529877)
                  ·
                    refine ⟨480115366207874547199919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20484922291535980680529877 480115366207874547199919)
                    ·
                      rfl

theorem cell22_1402532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1402532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402532 prefixEnd_1402532 := by exact prefixLift 1402532
  have htrace : WordTrace (prefixWord ++ tailWord_1402532) baseStart_1402532 baseEnd_1402532 := by
    simpa [prefixWord, tailWord_1402532, baseEnd_1402532] using wordTrace_append hprefix tailTrace_1402532
  have hstable : (prefixWord ++ tailWord_1402532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402532).length < 2 ^ (prefixWord ++ tailWord_1402532).sum := by decide
  have hdescent : baseEnd_1402532 < baseStart_1402532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402547 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 3, 4]
def baseStart_1402547 : Nat := 118140960795 + 1402547 * 2 ^ 59
def prefixEnd_1402547 : Nat := 4983230072969 + 3 ^ 40 * 1402547 * 2
def baseEnd_1402547 : Nat := 480120501014419508074873

theorem tailTrace_1402547 : CollatzResearch.WordTrace tailWord_1402547 prefixEnd_1402547 480120501014419508074873 := by
  unfold tailWord_1402547
  simp only [CollatzResearch.WordTrace]
  refine ⟨51155091649819229802277895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34103394433212819868185263 51155091649819229802277895)
  ·
    refine ⟨76732637474728844703416843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51155091649819229802277895 76732637474728844703416843)
    ·
      refine ⟨115098956212093267055125265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76732637474728844703416843 115098956212093267055125265)
      ·
        refine ⟨86324217159069950291343949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115098956212093267055125265 86324217159069950291343949)
        ·
          refine ⟨32371581434651231359253981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86324217159069950291343949 32371581434651231359253981)
          ·
            refine ⟨12139343037994211759720243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32371581434651231359253981 12139343037994211759720243)
            ·
              refine ⟨18209014556991317639580365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12139343037994211759720243 18209014556991317639580365)
              ·
                refine ⟨6828380458871744114842637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18209014556991317639580365 6828380458871744114842637)
                ·
                  refine ⟨2560642672076904043065989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6828380458871744114842637 2560642672076904043065989)
                  ·
                    refine ⟨480120501014419508074873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2560642672076904043065989 480120501014419508074873)
                    ·
                      rfl

theorem cell22_1402547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 4].length) (baseStart_1402547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402547 prefixEnd_1402547 := by exact prefixLift 1402547
  have htrace : WordTrace (prefixWord ++ tailWord_1402547) baseStart_1402547 baseEnd_1402547 := by
    simpa [prefixWord, tailWord_1402547, baseEnd_1402547] using wordTrace_append hprefix tailTrace_1402547
  have hstable : (prefixWord ++ tailWord_1402547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402547).length < 2 ^ (prefixWord ++ tailWord_1402547).sum := by decide
  have hdescent : baseEnd_1402547 < baseStart_1402547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402592 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_1402592 : Nat := 118140960795 + 1402592 * 2 ^ 59
def prefixEnd_1402592 : Nat := 4983230072969 + 3 ^ 40 * 1402592 * 2
def baseEnd_1402592 : Nat := 480135905434054390699735

theorem tailTrace_1402592 : CollatzResearch.WordTrace tailWord_1402592 prefixEnd_1402592 480135905434054390699735 := by
  unfold tailWord_1402592
  simp only [CollatzResearch.WordTrace]
  refine ⟨25578366467328101243833015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34104488623104134991777353 25578366467328101243833015)
  ·
    refine ⟨38367549700992151865749523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25578366467328101243833015 38367549700992151865749523)
    ·
      refine ⟨57551324551488227798624285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38367549700992151865749523 57551324551488227798624285)
      ·
        refine ⟨21581746706808085424484107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57551324551488227798624285 21581746706808085424484107)
        ·
          refine ⟨32372620060212128136726161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21581746706808085424484107 32372620060212128136726161)
          ·
            refine ⟨24279465045159096102544621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32372620060212128136726161 24279465045159096102544621)
            ·
              refine ⟨9104799391934661038454233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24279465045159096102544621 9104799391934661038454233)
              ·
                refine ⟨6828599543950995778840675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9104799391934661038454233 6828599543950995778840675)
                ·
                  refine ⟨10242899315926493668261013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6828599543950995778840675 10242899315926493668261013)
                  ·
                    refine ⟨480135905434054390699735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10242899315926493668261013 480135905434054390699735)
                    ·
                      rfl

theorem cell22_1402592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_1402592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402592 prefixEnd_1402592 := by exact prefixLift 1402592
  have htrace : WordTrace (prefixWord ++ tailWord_1402592) baseStart_1402592 baseEnd_1402592 := by
    simpa [prefixWord, tailWord_1402592, baseEnd_1402592] using wordTrace_append hprefix tailTrace_1402592
  have hstable : (prefixWord ++ tailWord_1402592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402592).length < 2 ^ (prefixWord ++ tailWord_1402592).sum := by decide
  have hdescent : baseEnd_1402592 < baseStart_1402592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402607 : List Nat := [1, 1, 2, 1, 5, 1, 3, 8]
def baseStart_1402607 : Nat := 118140960795 + 1402607 * 2 ^ 59
def prefixEnd_1402607 : Nat := 4983230072969 + 3 ^ 40 * 1402607 * 2
def baseEnd_1402607 : Nat := 53349004471177705730521

theorem tailTrace_1402607 : CollatzResearch.WordTrace tailWord_1402607 prefixEnd_1402607 53349004471177705730521 := by
  unfold tailWord_1402607
  simp only [CollatzResearch.WordTrace]
  refine ⟨51157280029601860049462075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34104853353067906699641383 51157280029601860049462075)
  ·
    refine ⟨76735920044402790074193113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51157280029601860049462075 76735920044402790074193113)
    ·
      refine ⟨57551940033302092555644835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76735920044402790074193113 57551940033302092555644835)
      ·
        refine ⟨86327910049953138833467253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57551940033302092555644835 86327910049953138833467253)
        ·
          refine ⟨8093241567183106765637555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86327910049953138833467253 8093241567183106765637555)
          ·
            refine ⟨12139862350774660148456333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093241567183106765637555 12139862350774660148456333)
            ·
              refine ⟨4552448381540497555671125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12139862350774660148456333 4552448381540497555671125)
              ·
                refine ⟨53349004471177705730521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4552448381540497555671125 53349004471177705730521)
                ·
                  rfl

theorem cell22_1402607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 8].length) (baseStart_1402607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402607 prefixEnd_1402607 := by exact prefixLift 1402607
  have htrace : WordTrace (prefixWord ++ tailWord_1402607) baseStart_1402607 baseEnd_1402607 := by
    simpa [prefixWord, tailWord_1402607, baseEnd_1402607] using wordTrace_append hprefix tailTrace_1402607
  have hstable : (prefixWord ++ tailWord_1402607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402607).length < 2 ^ (prefixWord ++ tailWord_1402607).sum := by decide
  have hdescent : baseEnd_1402607 < baseStart_1402607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402626 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1402626 : Nat := 118140960795 + 1402626 * 2 ^ 59
def prefixEnd_1402626 : Nat := 4983230072969 + 3 ^ 40 * 1402626 * 2
def baseEnd_1402626 : Nat := 480147544328889635349631

theorem tailTrace_1402626 : CollatzResearch.WordTrace tailWord_1402626 prefixEnd_1402626 480147544328889635349631 := by
  unfold tailWord_1402626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12789493254133256573600933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34105315344355350862935821 12789493254133256573600933)
  ·
    refine ⟨2398029985149985607550175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12789493254133256573600933 2398029985149985607550175)
    ·
      refine ⟨3597044977724978411325263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398029985149985607550175 3597044977724978411325263)
      ·
        refine ⟨5395567466587467616987895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3597044977724978411325263 5395567466587467616987895)
        ·
          refine ⟨8093351199881201425481843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5395567466587467616987895 8093351199881201425481843)
          ·
            refine ⟨12140026799821802138222765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093351199881201425481843 12140026799821802138222765)
            ·
              refine ⟨4552510049933175801833537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12140026799821802138222765 4552510049933175801833537)
              ·
                refine ⟨3414382537449881851375153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552510049933175801833537 3414382537449881851375153)
                ·
                  refine ⟨2560786903087411388531365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3414382537449881851375153 2560786903087411388531365)
                  ·
                    refine ⟨480147544328889635349631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2560786903087411388531365 480147544328889635349631)
                    ·
                      rfl

theorem cell22_1402626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1402626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402626 prefixEnd_1402626 := by exact prefixLift 1402626
  have htrace : WordTrace (prefixWord ++ tailWord_1402626) baseStart_1402626 baseEnd_1402626 := by
    simpa [prefixWord, tailWord_1402626, baseEnd_1402626] using wordTrace_append hprefix tailTrace_1402626
  have hstable : (prefixWord ++ tailWord_1402626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402626).length < 2 ^ (prefixWord ++ tailWord_1402626).sum := by decide
  have hdescent : baseEnd_1402626 < baseStart_1402626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402639 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 3, 3]
def baseStart_1402639 : Nat := 118140960795 + 1402639 * 2 ^ 59
def prefixEnd_1402639 : Nat := 4983230072969 + 3 ^ 40 * 1402639 * 2
def baseEnd_1402639 : Nat := 480151994494561934774591

theorem tailTrace_1402639 : CollatzResearch.WordTrace tailWord_1402639 prefixEnd_1402639 480151994494561934774591 := by
  unfold tailWord_1402639
  simp only [CollatzResearch.WordTrace]
  refine ⟨51158447165485929514626971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34105631443657286343084647 51158447165485929514626971)
  ·
    refine ⟨76737670748228894271940457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51158447165485929514626971 76737670748228894271940457)
    ·
      refine ⟨57553253061171670703955343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76737670748228894271940457 57553253061171670703955343)
      ·
        refine ⟨86329879591757506055933015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57553253061171670703955343 86329879591757506055933015)
        ·
          refine ⟨129494819387636259083899523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86329879591757506055933015 129494819387636259083899523)
          ·
            refine ⟨194242229081454388625849285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129494819387636259083899523 194242229081454388625849285)
            ·
              refine ⟨36420417952772697867346741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194242229081454388625849285 36420417952772697867346741)
              ·
                refine ⟨3414414183072440425063757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36420417952772697867346741 3414414183072440425063757)
                ·
                  refine ⟨1280405318652165159398909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3414414183072440425063757 1280405318652165159398909)
                  ·
                    refine ⟨480151994494561934774591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280405318652165159398909 480151994494561934774591)
                    ·
                      rfl

theorem cell22_1402639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_1402639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402639 prefixEnd_1402639 := by exact prefixLift 1402639
  have htrace : WordTrace (prefixWord ++ tailWord_1402639) baseStart_1402639 baseEnd_1402639 := by
    simpa [prefixWord, tailWord_1402639, baseEnd_1402639] using wordTrace_append hprefix tailTrace_1402639
  have hstable : (prefixWord ++ tailWord_1402639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402639).length < 2 ^ (prefixWord ++ tailWord_1402639).sum := by decide
  have hdescent : baseEnd_1402639 < baseStart_1402639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402686 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_1402686 : Nat := 118140960795 + 1402686 * 2 ^ 59
def prefixEnd_1402686 : Nat := 4983230072969 + 3 ^ 40 * 1402686 * 2
def baseEnd_1402686 : Nat := 160056027851689826283149

theorem tailTrace_1402686 : CollatzResearch.WordTrace tailWord_1402686 prefixEnd_1402686 160056027851689826283149 := by
  unfold tailWord_1402686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6395020174539457067698489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34106774264210437694391941 6395020174539457067698489)
  ·
    refine ⟨4796265130904592800773867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6395020174539457067698489 4796265130904592800773867)
    ·
      refine ⟨7194397696356889201160801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4796265130904592800773867 7194397696356889201160801)
      ·
        refine ⟨5395798272267666900870601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7194397696356889201160801 5395798272267666900870601)
        ·
          refine ⟨4046848704200750175652951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5395798272267666900870601 4046848704200750175652951)
          ·
            refine ⟨6070273056301125263479427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046848704200750175652951 6070273056301125263479427)
            ·
              refine ⟨9105409584451687895219141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6070273056301125263479427 9105409584451687895219141)
              ·
                refine ⟨1707264297084691480353589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9105409584451687895219141 1707264297084691480353589)
                ·
                  refine ⟨160056027851689826283149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1707264297084691480353589 160056027851689826283149)
                  ·
                    rfl

theorem cell22_1402686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_1402686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402686 prefixEnd_1402686 := by exact prefixLift 1402686
  have htrace : WordTrace (prefixWord ++ tailWord_1402686) baseStart_1402686 baseEnd_1402686 := by
    simpa [prefixWord, tailWord_1402686, baseEnd_1402686] using wordTrace_append hprefix tailTrace_1402686
  have hstable : (prefixWord ++ tailWord_1402686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402686).length < 2 ^ (prefixWord ++ tailWord_1402686).sum := by decide
  have hdescent : baseEnd_1402686 < baseStart_1402686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402701 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1402701 : Nat := 118140960795 + 1402701 * 2 ^ 59
def prefixEnd_1402701 : Nat := 4983230072969 + 3 ^ 40 * 1402701 * 2
def baseEnd_1402701 : Nat := 480173218361614439724401

theorem tailTrace_1402701 : CollatzResearch.WordTrace tailWord_1402701 prefixEnd_1402701 480173218361614439724401 := by
  unfold tailWord_1402701
  simp only [CollatzResearch.WordTrace]
  refine ⟨51160708491261314103383957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34107138994174209402255971 51160708491261314103383957)
  ·
    refine ⟨2398158210527874098596123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51160708491261314103383957 2398158210527874098596123)
    ·
      refine ⟨3597237315791811147894185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398158210527874098596123 3597237315791811147894185)
      ·
        refine ⟨2697927986843858360920639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3597237315791811147894185 2697927986843858360920639)
        ·
          refine ⟨4046891980265787541380959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2697927986843858360920639 4046891980265787541380959)
          ·
            refine ⟨6070337970398681312071439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046891980265787541380959 6070337970398681312071439)
            ·
              refine ⟨9105506955598021968107159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6070337970398681312071439 9105506955598021968107159)
              ·
                refine ⟨13658260433397032952160739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9105506955598021968107159 13658260433397032952160739)
                ·
                  refine ⟨20487390650095549428241109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13658260433397032952160739 20487390650095549428241109)
                  ·
                    refine ⟨480173218361614439724401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20487390650095549428241109 480173218361614439724401)
                    ·
                      rfl

theorem cell22_1402701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1402701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402701 prefixEnd_1402701 := by exact prefixLift 1402701
  have htrace : WordTrace (prefixWord ++ tailWord_1402701) baseStart_1402701 baseEnd_1402701 := by
    simpa [prefixWord, tailWord_1402701, baseEnd_1402701] using wordTrace_append hprefix tailTrace_1402701
  have hstable : (prefixWord ++ tailWord_1402701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402701).length < 2 ^ (prefixWord ++ tailWord_1402701).sum := by decide
  have hdescent : baseEnd_1402701 < baseStart_1402701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402714 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_1402714 : Nat := 118140960795 + 1402714 * 2 ^ 59
def prefixEnd_1402714 : Nat := 4983230072969 + 3 ^ 40 * 1402714 * 2
def baseEnd_1402714 : Nat := 160059222842428913049787

theorem tailTrace_1402714 : CollatzResearch.WordTrace tailWord_1402714 prefixEnd_1402714 160059222842428913049787 := by
  unfold tailWord_1402714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12790295660053554330901799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34107455093476144882404797 12790295660053554330901799)
  ·
    refine ⟨19185443490080331496352699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12790295660053554330901799 19185443490080331496352699)
    ·
      refine ⟨28778165235120497244529049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19185443490080331496352699 28778165235120497244529049)
      ·
        refine ⟨21583623926340372933396787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28778165235120497244529049 21583623926340372933396787)
        ·
          refine ⟨32375435889510559400095181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21583623926340372933396787 32375435889510559400095181)
          ·
            refine ⟨12140788458566459775035693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32375435889510559400095181 12140788458566459775035693)
            ·
              refine ⟨4552795671962422415638385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12140788458566459775035693 4552795671962422415638385)
              ·
                refine ⟨3414596753971816811728789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552795671962422415638385 3414596753971816811728789)
                ·
                  refine ⟨160059222842428913049787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3414596753971816811728789 160059222842428913049787)
                  ·
                    rfl

theorem cell22_1402714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_1402714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402714 prefixEnd_1402714 := by exact prefixLift 1402714
  have htrace : WordTrace (prefixWord ++ tailWord_1402714) baseStart_1402714 baseEnd_1402714 := by
    simpa [prefixWord, tailWord_1402714, baseEnd_1402714] using wordTrace_append hprefix tailTrace_1402714
  have hstable : (prefixWord ++ tailWord_1402714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402714).length < 2 ^ (prefixWord ++ tailWord_1402714).sum := by decide
  have hdescent : baseEnd_1402714 < baseStart_1402714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402733 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_1402733 : Nat := 118140960795 + 1402733 * 2 ^ 59
def prefixEnd_1402733 : Nat := 4983230072969 + 3 ^ 40 * 1402733 * 2
def baseEnd_1402733 : Nat := 480184172615577022924303

theorem tailTrace_1402733 : CollatzResearch.WordTrace tailWord_1402733 prefixEnd_1402733 480184172615577022924303 := by
  unfold tailWord_1402733
  simp only [CollatzResearch.WordTrace]
  refine ⟨51161875627145383568548853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34107917084763589045699235 51161875627145383568548853)
  ·
    refine ⟨4796425840044879709551455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51161875627145383568548853 4796425840044879709551455)
    ·
      refine ⟨7194638760067319564327183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4796425840044879709551455 7194638760067319564327183)
      ·
        refine ⟨10791958140100979346490775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7194638760067319564327183 10791958140100979346490775)
        ·
          refine ⟨16187937210151469019736163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10791958140100979346490775 16187937210151469019736163)
          ·
            refine ⟨24281905815227203529604245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16187937210151469019736163 24281905815227203529604245)
            ·
              refine ⟨1138214335088775165450199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24281905815227203529604245 1138214335088775165450199)
              ·
                refine ⟨1707321502633162748175299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138214335088775165450199 1707321502633162748175299)
                ·
                  refine ⟨2560982253949744122262949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707321502633162748175299 2560982253949744122262949)
                  ·
                    refine ⟨480184172615577022924303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2560982253949744122262949 480184172615577022924303)
                    ·
                      rfl

theorem cell22_1402733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_1402733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402733 prefixEnd_1402733 := by exact prefixLift 1402733
  have htrace : WordTrace (prefixWord ++ tailWord_1402733) baseStart_1402733 baseEnd_1402733 := by
    simpa [prefixWord, tailWord_1402733, baseEnd_1402733] using wordTrace_append hprefix tailTrace_1402733
  have hstable : (prefixWord ++ tailWord_1402733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402733).length < 2 ^ (prefixWord ++ tailWord_1402733).sum := by decide
  have hdescent : baseEnd_1402733 < baseStart_1402733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402932 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1402932 : Nat := 118140960795 + 1402932 * 2 ^ 59
def prefixEnd_1402932 : Nat := 4983230072969 + 3 ^ 40 * 1402932 * 2
def baseEnd_1402932 : Nat := 480252294382406837198693

theorem tailTrace_1402932 : CollatzResearch.WordTrace tailWord_1402932 prefixEnd_1402932 480252294382406837198693 := by
  unfold tailWord_1402932
  simp only [CollatzResearch.WordTrace]
  refine ⟨25584566876712220277521525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34112755835616293703362033 25584566876712220277521525)
  ·
    refine ⟨2398553144691770651017643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25584566876712220277521525 2398553144691770651017643)
    ·
      refine ⟨3597829717037655976526465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398553144691770651017643 3597829717037655976526465)
      ·
        refine ⟨2698372287778241982394849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3597829717037655976526465 2698372287778241982394849)
        ·
          refine ⟨2023779215833681486796137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698372287778241982394849 2023779215833681486796137)
          ·
            refine ⟨1517834411875261115097103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2023779215833681486796137 1517834411875261115097103)
            ·
              refine ⟨2276751617812891672645655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517834411875261115097103 2276751617812891672645655)
              ·
                refine ⟨3415127426719337508968483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276751617812891672645655 3415127426719337508968483)
                ·
                  refine ⟨5122691140079006263452725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415127426719337508968483 5122691140079006263452725)
                  ·
                    refine ⟨480252294382406837198693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5122691140079006263452725 480252294382406837198693)
                    ·
                      rfl

theorem cell22_1402932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1402932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402932 prefixEnd_1402932 := by exact prefixLift 1402932
  have htrace : WordTrace (prefixWord ++ tailWord_1402932) baseStart_1402932 baseEnd_1402932 := by
    simpa [prefixWord, tailWord_1402932, baseEnd_1402932] using wordTrace_append hprefix tailTrace_1402932
  have hstable : (prefixWord ++ tailWord_1402932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402932).length < 2 ^ (prefixWord ++ tailWord_1402932).sum := by decide
  have hdescent : baseEnd_1402932 < baseStart_1402932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402943 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 3, 3]
def baseStart_1402943 : Nat := 118140960795 + 1402943 * 2 ^ 59
def prefixEnd_1402943 : Nat := 4983230072969 + 3 ^ 40 * 1402943 * 2
def baseEnd_1402943 : Nat := 480256059907206475173659

theorem tailTrace_1402943 : CollatzResearch.WordTrace tailWord_1402943 prefixEnd_1402943 480256059907206475173659 := by
  unfold tailWord_1402943
  simp only [CollatzResearch.WordTrace]
  refine ⟨51169534956384589433693483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34113023304256392955795655 51169534956384589433693483)
  ·
    refine ⟨76754302434576884150540225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51169534956384589433693483 76754302434576884150540225)
    ·
      refine ⟨57565726825932663112905169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76754302434576884150540225 57565726825932663112905169)
      ·
        refine ⟨43174295119449497334678877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57565726825932663112905169 43174295119449497334678877)
        ·
          refine ⟨16190360669793561500504579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43174295119449497334678877 16190360669793561500504579)
          ·
            refine ⟨24285541004690342250756869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16190360669793561500504579 24285541004690342250756869)
            ·
              refine ⟨4553538938379439172016913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24285541004690342250756869 4553538938379439172016913)
              ·
                refine ⟨3415154203784579379012685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4553538938379439172016913 3415154203784579379012685)
                ·
                  refine ⟨1280682826419217267129757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3415154203784579379012685 1280682826419217267129757)
                  ·
                    refine ⟨480256059907206475173659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280682826419217267129757 480256059907206475173659)
                    ·
                      rfl

theorem cell22_1402943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_1402943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402943 prefixEnd_1402943 := by exact prefixLift 1402943
  have htrace : WordTrace (prefixWord ++ tailWord_1402943) baseStart_1402943 baseEnd_1402943 := by
    simpa [prefixWord, tailWord_1402943, baseEnd_1402943] using wordTrace_append hprefix tailTrace_1402943
  have hstable : (prefixWord ++ tailWord_1402943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402943).length < 2 ^ (prefixWord ++ tailWord_1402943).sum := by decide
  have hdescent : baseEnd_1402943 < baseStart_1402943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402945 : List Nat := [1, 2, 5, 1, 2, 3, 2, 6]
def baseStart_1402945 : Nat := 118140960795 + 1402945 * 2 ^ 59
def prefixEnd_1402945 : Nat := 4983230072969 + 3 ^ 40 * 1402945 * 2
def baseEnd_1402945 : Nat := 53361860505342126291517

theorem tailTrace_1402945 : CollatzResearch.WordTrace tailWord_1402945 prefixEnd_1402945 53361860505342126291517 := by
  unfold tailWord_1402945
  simp only [CollatzResearch.WordTrace]
  refine ⟨51169607902377343775266289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34113071934918229183510859 51169607902377343775266289)
  ·
    refine ⟨38377205926783007831449717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51169607902377343775266289 38377205926783007831449717)
    ·
      refine ⟨3597863055635906984198411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38377205926783007831449717 3597863055635906984198411)
      ·
        refine ⟨5396794583453860476297617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3597863055635906984198411 5396794583453860476297617)
        ·
          refine ⟨4047595937590395357223213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5396794583453860476297617 4047595937590395357223213)
          ·
            refine ⟨1517848476596398258958705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4047595937590395357223213 1517848476596398258958705)
            ·
              refine ⟨1138386357447298694219029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517848476596398258958705 1138386357447298694219029)
              ·
                refine ⟨53361860505342126291517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1138386357447298694219029 53361860505342126291517)
                ·
                  rfl

theorem cell22_1402945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 6].length) (baseStart_1402945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402945 prefixEnd_1402945 := by exact prefixLift 1402945
  have htrace : WordTrace (prefixWord ++ tailWord_1402945) baseStart_1402945 baseEnd_1402945 := by
    simpa [prefixWord, tailWord_1402945, baseEnd_1402945] using wordTrace_append hprefix tailTrace_1402945
  have hstable : (prefixWord ++ tailWord_1402945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402945).length < 2 ^ (prefixWord ++ tailWord_1402945).sum := by decide
  have hdescent : baseEnd_1402945 < baseStart_1402945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402956 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 7]
def baseStart_1402956 : Nat := 118140960795 + 1402956 * 2 ^ 59
def prefixEnd_1402956 : Nat := 4983230072969 + 3 ^ 40 * 1402956 * 2
def baseEnd_1402956 : Nat := 160086836690959591532873

theorem tailTrace_1402956 : CollatzResearch.WordTrace tailWord_1402956 prefixEnd_1402956 160086836690959591532873 := by
  unfold tailWord_1402956
  simp only [CollatzResearch.WordTrace]
  refine ⟨25585004552668746326958361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34113339403558328435944481 25585004552668746326958361)
  ·
    refine ⟨19188753414501559745218771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25585004552668746326958361 19188753414501559745218771)
    ·
      refine ⟨28783130121752339617828157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19188753414501559745218771 28783130121752339617828157)
      ·
        refine ⟨10793673795657127356685559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28783130121752339617828157 10793673795657127356685559)
        ·
          refine ⟨16190510693485691035028339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10793673795657127356685559 16190510693485691035028339)
          ·
            refine ⟨24285766040228536552542509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16190510693485691035028339 24285766040228536552542509)
            ·
              refine ⟨9107162265085701207203441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24285766040228536552542509 9107162265085701207203441)
              ·
                refine ⟨6830371698814275905402581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9107162265085701207203441 6830371698814275905402581)
                ·
                  refine ⟨160086836690959591532873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6830371698814275905402581 160086836690959591532873)
                  ·
                    rfl

theorem cell22_1402956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_1402956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1402956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1402956 prefixEnd_1402956 := by exact prefixLift 1402956
  have htrace : WordTrace (prefixWord ++ tailWord_1402956) baseStart_1402956 baseEnd_1402956 := by
    simpa [prefixWord, tailWord_1402956, baseEnd_1402956] using wordTrace_append hprefix tailTrace_1402956
  have hstable : (prefixWord ++ tailWord_1402956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402956).length < 2 ^ (prefixWord ++ tailWord_1402956).sum := by decide
  have hdescent : baseEnd_1402956 < baseStart_1402956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403028 : List Nat := [2, 4, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1403028 : Nat := 118140960795 + 1403028 * 2 ^ 59
def prefixEnd_1403028 : Nat := 4983230072969 + 3 ^ 40 * 1403028 * 2
def baseEnd_1403028 : Nat := 480285157144294586798399

theorem tailTrace_1403028 : CollatzResearch.WordTrace tailWord_1403028 prefixEnd_1403028 480285157144294586798399 := by
  unfold tailWord_1403028
  simp only [CollatzResearch.WordTrace]
  refine ⟨25586317580538324475268869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34115090107384432633691825 25586317580538324475268869)
  ·
    refine ⟨4797434546350935839112913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25586317580538324475268869 4797434546350935839112913)
    ·
      refine ⟨3598075909763201879334685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4797434546350935839112913 3598075909763201879334685)
      ·
        refine ⟨1349278466161200704750507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3598075909763201879334685 1349278466161200704750507)
        ·
          refine ⟨2023917699241801057125761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349278466161200704750507 2023917699241801057125761)
          ·
            refine ⟨1517938274431350792844321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2023917699241801057125761 1517938274431350792844321)
            ·
              refine ⟨1138453705823513094633241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517938274431350792844321 1138453705823513094633241)
              ·
                refine ⟨853840279367634820974931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138453705823513094633241 853840279367634820974931)
                ·
                  refine ⟨1280760419051452231462397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853840279367634820974931 1280760419051452231462397)
                  ·
                    refine ⟨480285157144294586798399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280760419051452231462397 480285157144294586798399)
                    ·
                      rfl

theorem cell22_1403028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1403028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403028 prefixEnd_1403028 := by exact prefixLift 1403028
  have htrace : WordTrace (prefixWord ++ tailWord_1403028) baseStart_1403028 baseEnd_1403028 := by
    simpa [prefixWord, tailWord_1403028, baseEnd_1403028] using wordTrace_append hprefix tailTrace_1403028
  have hstable : (prefixWord ++ tailWord_1403028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403028).length < 2 ^ (prefixWord ++ tailWord_1403028).sum := by decide
  have hdescent : baseEnd_1403028 < baseStart_1403028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403033 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 4, 3]
def baseStart_1403033 : Nat := 118140960795 + 1403033 * 2 ^ 59
def prefixEnd_1403033 : Nat := 4983230072969 + 3 ^ 40 * 1403033 * 2
def baseEnd_1403033 : Nat := 480286868746476240423383

theorem tailTrace_1403033 : CollatzResearch.WordTrace tailWord_1403033 prefixEnd_1403033 480286868746476240423383 := by
  unfold tailWord_1403033
  simp only [CollatzResearch.WordTrace]
  refine ⟨51172817526058534804469753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34115211684039023202979835 51172817526058534804469753)
  ·
    refine ⟨38379613144543901103352315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51172817526058534804469753 38379613144543901103352315)
    ·
      refine ⟨57569419716815851655028473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38379613144543901103352315 57569419716815851655028473)
      ·
        refine ⟨43177064787611888741271355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57569419716815851655028473 43177064787611888741271355)
        ·
          refine ⟨64765597181417833111907033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43177064787611888741271355 64765597181417833111907033)
          ·
            refine ⟨48574197886063374833930275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64765597181417833111907033 48574197886063374833930275)
            ·
              refine ⟨72861296829095062250895413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48574197886063374833930275 72861296829095062250895413)
              ·
                refine ⟨6830746577727662086021445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72861296829095062250895413 6830746577727662086021445)
                ·
                  refine ⟨1280764983323936641129021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6830746577727662086021445 1280764983323936641129021)
                  ·
                    refine ⟨480286868746476240423383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280764983323936641129021 480286868746476240423383)
                    ·
                      rfl

theorem cell22_1403033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_1403033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403033 prefixEnd_1403033 := by exact prefixLift 1403033
  have htrace : WordTrace (prefixWord ++ tailWord_1403033) baseStart_1403033 baseEnd_1403033 := by
    simpa [prefixWord, tailWord_1403033, baseEnd_1403033] using wordTrace_append hprefix tailTrace_1403033
  have hstable : (prefixWord ++ tailWord_1403033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403033).length < 2 ^ (prefixWord ++ tailWord_1403033).sum := by decide
  have hdescent : baseEnd_1403033 < baseStart_1403033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403172 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_1403172 : Nat := 118140960795 + 1403172 * 2 ^ 59
def prefixEnd_1403172 : Nat := 4983230072969 + 3 ^ 40 * 1403172 * 2
def baseEnd_1403172 : Nat := 480334451287126211197957

theorem tailTrace_1403172 : CollatzResearch.WordTrace tailWord_1403172 prefixEnd_1403172 480334451287126211197957 := by
  unfold tailWord_1403172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25588943636277480771889885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34118591515036641029186513 25588943636277480771889885)
  ·
    refine ⟨9595853863604055289458707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25588943636277480771889885 9595853863604055289458707)
    ·
      refine ⟨14393780795406082934188061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9595853863604055289458707 14393780795406082934188061)
      ·
        refine ⟨5397667798277281100320523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14393780795406082934188061 5397667798277281100320523)
        ·
          refine ⟨8096501697415921650480785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5397667798277281100320523 8096501697415921650480785)
          ·
            refine ⟨6072376273061941237860589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8096501697415921650480785 6072376273061941237860589)
            ·
              refine ⟨2277141102398227964197721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6072376273061941237860589 2277141102398227964197721)
              ·
                refine ⟨1707855826798670973148291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277141102398227964197721 1707855826798670973148291)
                ·
                  refine ⟨2561783740198006459722437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707855826798670973148291 2561783740198006459722437)
                  ·
                    refine ⟨480334451287126211197957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2561783740198006459722437 480334451287126211197957)
                    ·
                      rfl

theorem cell22_1403172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_1403172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403172 prefixEnd_1403172 := by exact prefixLift 1403172
  have htrace : WordTrace (prefixWord ++ tailWord_1403172) baseStart_1403172 baseEnd_1403172 := by
    simpa [prefixWord, tailWord_1403172, baseEnd_1403172] using wordTrace_append hprefix tailTrace_1403172
  have hstable : (prefixWord ++ tailWord_1403172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403172).length < 2 ^ (prefixWord ++ tailWord_1403172).sum := by decide
  have hdescent : baseEnd_1403172 < baseStart_1403172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403183 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 1, 6]
def baseStart_1403183 : Nat := 118140960795 + 1403183 * 2 ^ 59
def prefixEnd_1403183 : Nat := 4983230072969 + 3 ^ 40 * 1403183 * 2
def baseEnd_1403183 : Nat := 480338216811925849172923

theorem tailTrace_1403183 : CollatzResearch.WordTrace tailWord_1403183 prefixEnd_1403183 480338216811925849172923 := by
  unfold tailWord_1403183
  simp only [CollatzResearch.WordTrace]
  refine ⟨51178288475515110422430203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34118858983676740281620135 51178288475515110422430203)
  ·
    refine ⟨76767432713272665633645305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51178288475515110422430203 76767432713272665633645305)
    ·
      refine ⟨57575574534954499225233979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76767432713272665633645305 57575574534954499225233979)
      ·
        refine ⟨86363361802431748837850969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57575574534954499225233979 86363361802431748837850969)
        ·
          refine ⟨64772521351823811628388227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86363361802431748837850969 64772521351823811628388227)
          ·
            refine ⟨97158782027735717442582341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64772521351823811628388227 97158782027735717442582341)
            ·
              refine ⟨18217271630200447020484189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97158782027735717442582341 18217271630200447020484189)
              ·
                refine ⟨6831476861325167632681571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18217271630200447020484189 6831476861325167632681571)
                ·
                  refine ⟨10247215291987751449022357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6831476861325167632681571 10247215291987751449022357)
                  ·
                    refine ⟨480338216811925849172923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10247215291987751449022357 480338216811925849172923)
                    ·
                      rfl

theorem cell22_1403183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_1403183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403183 prefixEnd_1403183 := by exact prefixLift 1403183
  have htrace : WordTrace (prefixWord ++ tailWord_1403183) baseStart_1403183 baseEnd_1403183 := by
    simpa [prefixWord, tailWord_1403183, baseEnd_1403183] using wordTrace_append hprefix tailTrace_1403183
  have hstable : (prefixWord ++ tailWord_1403183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403183).length < 2 ^ (prefixWord ++ tailWord_1403183).sum := by decide
  have hdescent : baseEnd_1403183 < baseStart_1403183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403232 : List Nat := [2, 1, 1, 3, 5, 1, 3, 6]
def baseStart_1403232 : Nat := 118140960795 + 1403232 * 2 ^ 59
def prefixEnd_1403232 : Nat := 4983230072969 + 3 ^ 40 * 1403232 * 2
def baseEnd_1403232 : Nat := 53372776723700672744197

theorem tailTrace_1403232 : CollatzResearch.WordTrace tailWord_1403232 prefixEnd_1403232 53372776723700672744197 := by
  unfold tailWord_1403232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25590037826168795895481975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34120050434891727860642633 25590037826168795895481975)
  ·
    refine ⟨38385056739253193843222963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25590037826168795895481975 38385056739253193843222963)
    ·
      refine ⟨57577585108879790764834445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38385056739253193843222963 57577585108879790764834445)
      ·
        refine ⟨21591594415829921536812917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57577585108879790764834445 21591594415829921536812917)
        ·
          refine ⟨2024211976484055144076211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21591594415829921536812917 2024211976484055144076211)
          ·
            refine ⟨3036317964726082716114317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024211976484055144076211 3036317964726082716114317)
            ·
              refine ⟨1138619236772281018542869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3036317964726082716114317 1138619236772281018542869)
              ·
                refine ⟨53372776723700672744197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1138619236772281018542869 53372776723700672744197)
                ·
                  rfl

theorem cell22_1403232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 6].length) (baseStart_1403232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403232 prefixEnd_1403232 := by exact prefixLift 1403232
  have htrace : WordTrace (prefixWord ++ tailWord_1403232) baseStart_1403232 baseEnd_1403232 := by
    simpa [prefixWord, tailWord_1403232, baseEnd_1403232] using wordTrace_append hprefix tailTrace_1403232
  have hstable : (prefixWord ++ tailWord_1403232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403232).length < 2 ^ (prefixWord ++ tailWord_1403232).sum := by decide
  have hdescent : baseEnd_1403232 < baseStart_1403232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403234 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1403234 : Nat := 118140960795 + 1403234 * 2 ^ 59
def prefixEnd_1403234 : Nat := 4983230072969 + 3 ^ 40 * 1403234 * 2
def baseEnd_1403234 : Nat := 480355675154178716147767

theorem tailTrace_1403234 : CollatzResearch.WordTrace tailWord_1403234 prefixEnd_1403234 480355675154178716147767 := by
  unfold tailWord_1403234
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795037149582586533134189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34120099065553564088357837 12795037149582586533134189)
  ·
    refine ⟨4798138931093469949925321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12795037149582586533134189 4798138931093469949925321)
    ·
      refine ⟨3598604198320102462443991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4798138931093469949925321 3598604198320102462443991)
      ·
        refine ⟨5397906297480153693665987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3598604198320102462443991 5397906297480153693665987)
        ·
          refine ⟨8096859446220230540498981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5397906297480153693665987 8096859446220230540498981)
          ·
            refine ⟨1518161146166293226343559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8096859446220230540498981 1518161146166293226343559)
            ·
              refine ⟨2277241719249439839515339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518161146166293226343559 2277241719249439839515339)
              ·
                refine ⟨3415862578874159759273009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277241719249439839515339 3415862578874159759273009)
                ·
                  refine ⟨2561896934155619819454757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3415862578874159759273009 2561896934155619819454757)
                  ·
                    refine ⟨480355675154178716147767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2561896934155619819454757 480355675154178716147767)
                    ·
                      rfl

theorem cell22_1403234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1403234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403234 prefixEnd_1403234 := by exact prefixLift 1403234
  have htrace : WordTrace (prefixWord ++ tailWord_1403234) baseStart_1403234 baseEnd_1403234 := by
    simpa [prefixWord, tailWord_1403234, baseEnd_1403234] using wordTrace_append hprefix tailTrace_1403234
  have hstable : (prefixWord ++ tailWord_1403234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403234).length < 2 ^ (prefixWord ++ tailWord_1403234).sum := by decide
  have hdescent : baseEnd_1403234 < baseStart_1403234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403243 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 9]
def baseStart_1403243 : Nat := 118140960795 + 1403243 * 2 ^ 59
def prefixEnd_1403243 : Nat := 4983230072969 + 3 ^ 40 * 1403243 * 2
def baseEnd_1403243 : Nat := 160119585346035230890913

theorem tailTrace_1403243 : CollatzResearch.WordTrace tailWord_1403243 prefixEnd_1403243 160119585346035230890913 := by
  unfold tailWord_1403243
  simp only [CollatzResearch.WordTrace]
  refine ⟨51180476855297740669614383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34120317903531827113076255 51180476855297740669614383)
  ·
    refine ⟨76770715282946611004421575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51180476855297740669614383 76770715282946611004421575)
    ·
      refine ⟨115156072924419916506632363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76770715282946611004421575 115156072924419916506632363)
      ·
        refine ⟨172734109386629874759948545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115156072924419916506632363 172734109386629874759948545)
        ·
          refine ⟨129550582039972406069961409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172734109386629874759948545 129550582039972406069961409)
          ·
            refine ⟨97162936529979304552471057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129550582039972406069961409 97162936529979304552471057)
            ·
              refine ⟨72872202397484478414353293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97162936529979304552471057 72872202397484478414353293)
              ·
                refine ⟨27327075899056679405382485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72872202397484478414353293 27327075899056679405382485)
                ·
                  refine ⟨160119585346035230890913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27327075899056679405382485 160119585346035230890913)
                  ·
                    rfl

theorem cell22_1403243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 9].length) (baseStart_1403243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403243 prefixEnd_1403243 := by exact prefixLift 1403243
  have htrace : WordTrace (prefixWord ++ tailWord_1403243) baseStart_1403243 baseEnd_1403243 := by
    simpa [prefixWord, tailWord_1403243, baseEnd_1403243] using wordTrace_append hprefix tailTrace_1403243
  have hstable : (prefixWord ++ tailWord_1403243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403243).length < 2 ^ (prefixWord ++ tailWord_1403243).sum := by decide
  have hdescent : baseEnd_1403243 < baseStart_1403243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403260 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 5]
def baseStart_1403260 : Nat := 118140960795 + 1403260 * 2 ^ 59
def prefixEnd_1403260 : Nat := 4983230072969 + 3 ^ 40 * 1403260 * 2
def baseEnd_1403260 : Nat := 160121525161841104999229

theorem tailTrace_1403260 : CollatzResearch.WordTrace tailWord_1403260 prefixEnd_1403260 160121525161841104999229 := by
  unfold tailWord_1403260
  simp only [CollatzResearch.WordTrace]
  refine ⟨25590548448118076286491617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34120731264157435048655489 25590548448118076286491617)
  ·
    refine ⟨19192911336088557214868713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25590548448118076286491617 19192911336088557214868713)
    ·
      refine ⟨14394683502066417911151535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19192911336088557214868713 14394683502066417911151535)
      ·
        refine ⟨21592025253099626866727303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14394683502066417911151535 21592025253099626866727303)
        ·
          refine ⟨32388037879649440300090955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21592025253099626866727303 32388037879649440300090955)
          ·
            refine ⟨48582056819474160450136433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32388037879649440300090955 48582056819474160450136433)
            ·
              refine ⟨36436542614605620337602325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48582056819474160450136433 36436542614605620337602325)
              ·
                refine ⟨1707962935059638453325109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36436542614605620337602325 1707962935059638453325109)
                ·
                  refine ⟨160121525161841104999229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1707962935059638453325109 160121525161841104999229)
                  ·
                    rfl

theorem cell22_1403260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_1403260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403260 prefixEnd_1403260 := by exact prefixLift 1403260
  have htrace : WordTrace (prefixWord ++ tailWord_1403260) baseStart_1403260 baseEnd_1403260 := by
    simpa [prefixWord, tailWord_1403260, baseEnd_1403260] using wordTrace_append hprefix tailTrace_1403260
  have hstable : (prefixWord ++ tailWord_1403260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403260).length < 2 ^ (prefixWord ++ tailWord_1403260).sum := by decide
  have hdescent : baseEnd_1403260 < baseStart_1403260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403275 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 2, 5]
def baseStart_1403275 : Nat := 118140960795 + 1403275 * 2 ^ 59
def prefixEnd_1403275 : Nat := 4983230072969 + 3 ^ 40 * 1403275 * 2
def baseEnd_1403275 : Nat := 480369710292068275872641

theorem tailTrace_1403275 : CollatzResearch.WordTrace tailWord_1403275 prefixEnd_1403275 480369710292068275872641 := by
  unfold tailWord_1403275
  simp only [CollatzResearch.WordTrace]
  refine ⟨51181643991181810134779279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34121095994121206756519519 51181643991181810134779279)
  ·
    refine ⟨76772465986772715202168919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51181643991181810134779279 76772465986772715202168919)
    ·
      refine ⟨115158698980159072803253379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76772465986772715202168919 115158698980159072803253379)
      ·
        refine ⟨172738048470238609204880069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115158698980159072803253379 172738048470238609204880069)
        ·
          refine ⟨32388384088169739225915013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172738048470238609204880069 32388384088169739225915013)
          ·
            refine ⟨6072822016531826104859065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32388384088169739225915013 6072822016531826104859065)
            ·
              refine ⟨4554616512398869578644299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6072822016531826104859065 4554616512398869578644299)
              ·
                refine ⟨6831924768598304367966449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4554616512398869578644299 6831924768598304367966449)
                ·
                  refine ⟨5123943576448728275974837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6831924768598304367966449 5123943576448728275974837)
                  ·
                    refine ⟨480369710292068275872641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5123943576448728275974837 480369710292068275872641)
                    ·
                      rfl

theorem cell22_1403275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_1403275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403275 prefixEnd_1403275 := by exact prefixLift 1403275
  have htrace : WordTrace (prefixWord ++ tailWord_1403275) baseStart_1403275 baseEnd_1403275 := by
    simpa [prefixWord, tailWord_1403275, baseEnd_1403275] using wordTrace_append hprefix tailTrace_1403275
  have hstable : (prefixWord ++ tailWord_1403275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403275).length < 2 ^ (prefixWord ++ tailWord_1403275).sum := by decide
  have hdescent : baseEnd_1403275 < baseStart_1403275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403322 : List Nat := [3, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_1403322 : Nat := 118140960795 + 1403322 * 2 ^ 59
def prefixEnd_1403322 : Nat := 4983230072969 + 3 ^ 40 * 1403322 * 2
def baseEnd_1403322 : Nat := 160128599784191939982499

theorem tailTrace_1403322 : CollatzResearch.WordTrace tailWord_1403322 prefixEnd_1403322 160128599784191939982499 := by
  unfold tailWord_1403322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795839555502884290435055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34122238814674358107826813 12795839555502884290435055)
  ·
    refine ⟨19193759333254326435652583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12795839555502884290435055 19193759333254326435652583)
    ·
      refine ⟨28790638999881489653478875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19193759333254326435652583 28790638999881489653478875)
      ·
        refine ⟨43185958499822234480218313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28790638999881489653478875 43185958499822234480218313)
        ·
          refine ⟨32389468874866675860163735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43185958499822234480218313 32389468874866675860163735)
          ·
            refine ⟨48584203312300013790245603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32389468874866675860163735 48584203312300013790245603)
            ·
              refine ⟨72876304968450020685368405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48584203312300013790245603 72876304968450020685368405)
              ·
                refine ⟨854019198849023679906661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 72876304968450020685368405 854019198849023679906661)
                ·
                  refine ⟨160128599784191939982499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854019198849023679906661 160128599784191939982499)
                  ·
                    rfl

theorem cell22_1403322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_1403322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403322 prefixEnd_1403322 := by exact prefixLift 1403322
  have htrace : WordTrace (prefixWord ++ tailWord_1403322) baseStart_1403322 baseEnd_1403322 := by
    simpa [prefixWord, tailWord_1403322, baseEnd_1403322] using wordTrace_append hprefix tailTrace_1403322
  have hstable : (prefixWord ++ tailWord_1403322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403322).length < 2 ^ (prefixWord ++ tailWord_1403322).sum := by decide
  have hdescent : baseEnd_1403322 < baseStart_1403322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403373 : List Nat := [1, 5, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1403373 : Nat := 118140960795 + 1403373 * 2 ^ 59
def prefixEnd_1403373 : Nat := 4983230072969 + 3 ^ 40 * 1403373 * 2
def baseEnd_1403373 : Nat := 160134419231609562307447

theorem tailTrace_1403373 : CollatzResearch.WordTrace tailWord_1403373 prefixEnd_1403373 160134419231609562307447 := by
  unfold tailWord_1403373
  simp only [CollatzResearch.WordTrace]
  refine ⟨51185218344826772871846773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34123478896551181914564515 51185218344826772871846773)
  ·
    refine ⟨4798614219827509956735635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51185218344826772871846773 4798614219827509956735635)
    ·
      refine ⟨7197921329741264935103453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4798614219827509956735635 7197921329741264935103453)
      ·
        refine ⟨2699220498652974350663795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7197921329741264935103453 2699220498652974350663795)
        ·
          refine ⟨4048830747979461525995693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2699220498652974350663795 4048830747979461525995693)
          ·
            refine ⟨1518311530492298072248385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4048830747979461525995693 1518311530492298072248385)
            ·
              refine ⟨1138733647869223554186289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518311530492298072248385 1138733647869223554186289)
              ·
                refine ⟨854050235901917665639717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138733647869223554186289 854050235901917665639717)
                ·
                  refine ⟨160134419231609562307447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854050235901917665639717 160134419231609562307447)
                  ·
                    rfl

theorem cell22_1403373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1403373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403373 prefixEnd_1403373 := by exact prefixLift 1403373
  have htrace : WordTrace (prefixWord ++ tailWord_1403373) baseStart_1403373 baseEnd_1403373 := by
    simpa [prefixWord, tailWord_1403373, baseEnd_1403373] using wordTrace_append hprefix tailTrace_1403373
  have hstable : (prefixWord ++ tailWord_1403373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403373).length < 2 ^ (prefixWord ++ tailWord_1403373).sum := by decide
  have hdescent : baseEnd_1403373 < baseStart_1403373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403416 : List Nat := [2, 1, 2, 3, 3, 1, 1, 5, 1, 3]
def baseStart_1403416 : Nat := 118140960795 + 1403416 * 2 ^ 59
def prefixEnd_1403416 : Nat := 4983230072969 + 3 ^ 40 * 1403416 * 2
def baseEnd_1403416 : Nat := 480417977473590908097209

theorem tailTrace_1403416 : CollatzResearch.WordTrace tailWord_1403416 prefixEnd_1403416 480417977473590908097209 := by
  unfold tailWord_1403416
  simp only [CollatzResearch.WordTrace]
  refine ⟨25593393341835495607831051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34124524455780660810441401 25593393341835495607831051)
  ·
    refine ⟨38390090012753243411746577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25593393341835495607831051 38390090012753243411746577)
    ·
      refine ⟨28792567509564932558809933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38390090012753243411746577 28792567509564932558809933)
      ·
        refine ⟨10797212816086849709553725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28792567509564932558809933 10797212816086849709553725)
        ·
          refine ⟨4048954806032568641082647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10797212816086849709553725 4048954806032568641082647)
          ·
            refine ⟨6073432209048852961623971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4048954806032568641082647 6073432209048852961623971)
            ·
              refine ⟨9110148313573279442435957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073432209048852961623971 9110148313573279442435957)
              ·
                refine ⟨854076404397494947728371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9110148313573279442435957 854076404397494947728371)
                ·
                  refine ⟨1281114606596242421592557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854076404397494947728371 1281114606596242421592557)
                  ·
                    refine ⟨480417977473590908097209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1281114606596242421592557 480417977473590908097209)
                    ·
                      rfl

theorem cell22_1403416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_1403416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403416 prefixEnd_1403416 := by exact prefixLift 1403416
  have htrace : WordTrace (prefixWord ++ tailWord_1403416) baseStart_1403416 baseEnd_1403416 := by
    simpa [prefixWord, tailWord_1403416, baseEnd_1403416] using wordTrace_append hprefix tailTrace_1403416
  have hstable : (prefixWord ++ tailWord_1403416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403416).length < 2 ^ (prefixWord ++ tailWord_1403416).sum := by decide
  have hdescent : baseEnd_1403416 < baseStart_1403416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403427 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 2, 5]
def baseStart_1403427 : Nat := 118140960795 + 1403427 * 2 ^ 59
def prefixEnd_1403427 : Nat := 4983230072969 + 3 ^ 40 * 1403427 * 2
def baseEnd_1403427 : Nat := 480421742998390546072175

theorem tailTrace_1403427 : CollatzResearch.WordTrace tailWord_1403427 prefixEnd_1403427 480421742998390546072175 := by
  unfold tailWord_1403427
  simp only [CollatzResearch.WordTrace]
  refine ⟨51187187886631140094312535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34124791924420760062875023 51187187886631140094312535)
  ·
    refine ⟨76780781829946710141468803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51187187886631140094312535 76780781829946710141468803)
    ·
      refine ⟨115171172744920065212203205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76780781829946710141468803 115171172744920065212203205)
      ·
        refine ⟨21594594889672512227288101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115171172744920065212203205 21594594889672512227288101)
        ·
          refine ⟨4048986541813596042616519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21594594889672512227288101 4048986541813596042616519)
          ·
            refine ⟨6073479812720394063924779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4048986541813596042616519 6073479812720394063924779)
            ·
              refine ⟨9110219719080591095887169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073479812720394063924779 9110219719080591095887169)
              ·
                refine ⟨6832664789310443321915377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9110219719080591095887169 6832664789310443321915377)
                ·
                  refine ⟨5124498591982832491436533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6832664789310443321915377 5124498591982832491436533)
                  ·
                    refine ⟨480421742998390546072175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5124498591982832491436533 480421742998390546072175)
                    ·
                      rfl

theorem cell22_1403427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_1403427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403427 prefixEnd_1403427 := by exact prefixLift 1403427
  have htrace : WordTrace (prefixWord ++ tailWord_1403427) baseStart_1403427 baseEnd_1403427 := by
    simpa [prefixWord, tailWord_1403427, baseEnd_1403427] using wordTrace_append hprefix tailTrace_1403427
  have hstable : (prefixWord ++ tailWord_1403427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403427).length < 2 ^ (prefixWord ++ tailWord_1403427).sum := by decide
  have hdescent : baseEnd_1403427 < baseStart_1403427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403442 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1403442 : Nat := 118140960795 + 1403442 * 2 ^ 59
def prefixEnd_1403442 : Nat := 4983230072969 + 3 ^ 40 * 1403442 * 2
def baseEnd_1403442 : Nat := 480426877804935506947129

theorem tailTrace_1403442 : CollatzResearch.WordTrace tailWord_1403442 prefixEnd_1403442 480426877804935506947129 := by
  unfold tailWord_1403442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12796933745394199414027145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34125156654384531770739053 12796933745394199414027145)
  ·
    refine ⟨9597700309045649560520359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12796933745394199414027145 9597700309045649560520359)
    ·
      refine ⟨14396550463568474340780539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9597700309045649560520359 14396550463568474340780539)
      ·
        refine ⟨21594825695352711511170809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14396550463568474340780539 21594825695352711511170809)
        ·
          refine ⟨16196119271514533633378107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21594825695352711511170809 16196119271514533633378107)
          ·
            refine ⟨24294178907271800450067161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16196119271514533633378107 24294178907271800450067161)
            ·
              refine ⟨18220634180453850337550371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24294178907271800450067161 18220634180453850337550371)
              ·
                refine ⟨27330951270680775506325557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18220634180453850337550371 27330951270680775506325557)
                ·
                  refine ⟨2562276681626322703718021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27330951270680775506325557 2562276681626322703718021)
                  ·
                    refine ⟨480426877804935506947129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562276681626322703718021 480426877804935506947129)
                    ·
                      rfl

theorem cell22_1403442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1403442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403442 prefixEnd_1403442 := by exact prefixLift 1403442
  have htrace : WordTrace (prefixWord ++ tailWord_1403442) baseStart_1403442 baseEnd_1403442 := by
    simpa [prefixWord, tailWord_1403442, baseEnd_1403442] using wordTrace_append hprefix tailTrace_1403442
  have hstable : (prefixWord ++ tailWord_1403442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403442).length < 2 ^ (prefixWord ++ tailWord_1403442).sum := by decide
  have hdescent : baseEnd_1403442 < baseStart_1403442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403489 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 4, 3]
def baseStart_1403489 : Nat := 118140960795 + 1403489 * 2 ^ 59
def prefixEnd_1403489 : Nat := 4983230072969 + 3 ^ 40 * 1403489 * 2
def baseEnd_1403489 : Nat := 480442966865443051021985

theorem tailTrace_1403489 : CollatzResearch.WordTrace tailWord_1403489 prefixEnd_1403489 480442966865443051021985 := by
  unfold tailWord_1403489
  simp only [CollatzResearch.WordTrace]
  refine ⟨51189449212406524683069521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34126299474937683122046347 51189449212406524683069521)
  ·
    refine ⟨38392086909304893512302141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51189449212406524683069521 38392086909304893512302141)
    ·
      refine ⟨14397032590989335067113303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38392086909304893512302141 14397032590989335067113303)
      ·
        refine ⟨21595548886484002600669955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14397032590989335067113303 21595548886484002600669955)
        ·
          refine ⟨32393323329726003901004933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21595548886484002600669955 32393323329726003901004933)
          ·
            refine ⟨6073748124323625731438425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32393323329726003901004933 6073748124323625731438425)
            ·
              refine ⟨4555311093242719298578819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6073748124323625731438425 4555311093242719298578819)
              ·
                refine ⟨6832966639864078947868229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555311093242719298578819 6832966639864078947868229)
                ·
                  refine ⟨1281181244974514802725293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6832966639864078947868229 1281181244974514802725293)
                  ·
                    refine ⟨480442966865443051021985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1281181244974514802725293 480442966865443051021985)
                    ·
                      rfl

theorem cell22_1403489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_1403489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403489 prefixEnd_1403489 := by exact prefixLift 1403489
  have htrace : WordTrace (prefixWord ++ tailWord_1403489) baseStart_1403489 baseEnd_1403489 := by
    simpa [prefixWord, tailWord_1403489, baseEnd_1403489] using wordTrace_append hprefix tailTrace_1403489
  have hstable : (prefixWord ++ tailWord_1403489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403489).length < 2 ^ (prefixWord ++ tailWord_1403489).sum := by decide
  have hdescent : baseEnd_1403489 < baseStart_1403489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403491 : List Nat := [1, 1, 1, 5, 1, 2, 5, 2, 4]
def baseStart_1403491 : Nat := 118140960795 + 1403491 * 2 ^ 59
def prefixEnd_1403491 : Nat := 4983230072969 + 3 ^ 40 * 1403491 * 2
def baseEnd_1403491 : Nat := 160147883835438570823993

theorem tailTrace_1403491 : CollatzResearch.WordTrace tailWord_1403491 prefixEnd_1403491 160147883835438570823993 := by
  unfold tailWord_1403491
  simp only [CollatzResearch.WordTrace]
  refine ⟨51189522158399279024642327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34126348105599519349761551 51189522158399279024642327)
  ·
    refine ⟨76784283237598918536963491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51189522158399279024642327 76784283237598918536963491)
    ·
      refine ⟨115176424856398377805445237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76784283237598918536963491 115176424856398377805445237)
      ·
        refine ⟨10797789830287347919260491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115176424856398377805445237 10797789830287347919260491)
        ·
          refine ⟨16196684745431021878890737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10797789830287347919260491 16196684745431021878890737)
          ·
            refine ⟨12147513559073266409168053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16196684745431021878890737 12147513559073266409168053)
            ·
              refine ⟨1138829396163118725859505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12147513559073266409168053 1138829396163118725859505)
              ·
                refine ⟨854122047122339044394629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138829396163118725859505 854122047122339044394629)
                ·
                  refine ⟨160147883835438570823993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854122047122339044394629 160147883835438570823993)
                  ·
                    rfl

theorem cell22_1403491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 4].length) (baseStart_1403491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403491 prefixEnd_1403491 := by exact prefixLift 1403491
  have htrace : WordTrace (prefixWord ++ tailWord_1403491) baseStart_1403491 baseEnd_1403491 := by
    simpa [prefixWord, tailWord_1403491, baseEnd_1403491] using wordTrace_append hprefix tailTrace_1403491
  have hstable : (prefixWord ++ tailWord_1403491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403491).length < 2 ^ (prefixWord ++ tailWord_1403491).sum := by decide
  have hdescent : baseEnd_1403491 < baseStart_1403491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403510 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_1403510 : Nat := 118140960795 + 1403510 * 2 ^ 59
def prefixEnd_1403510 : Nat := 4983230072969 + 3 ^ 40 * 1403510 * 2
def baseEnd_1403510 : Nat := 480450155594605996246921

theorem tailTrace_1403510 : CollatzResearch.WordTrace tailWord_1403510 prefixEnd_1403510 480450155594605996246921 := by
  unfold tailWord_1403510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3199388446583152829348999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34126810096886963513055989 3199388446583152829348999)
  ·
    refine ⟨4799082669874729244023499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3199388446583152829348999 4799082669874729244023499)
    ·
      refine ⟨7198624004812093866035249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4799082669874729244023499 7198624004812093866035249)
      ·
        refine ⟨5398968003609070399526437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7198624004812093866035249 5398968003609070399526437)
        ·
          refine ⟨1012306500676700699911207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5398968003609070399526437 1012306500676700699911207)
          ·
            refine ⟨1518459751015051049866811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012306500676700699911207 1518459751015051049866811)
            ·
              refine ⟨2277689626522576574800217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518459751015051049866811 2277689626522576574800217)
              ·
                refine ⟨1708267219891932431100163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277689626522576574800217 1708267219891932431100163)
                ·
                  refine ⟨2562400829837898646650245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708267219891932431100163 2562400829837898646650245)
                  ·
                    refine ⟨480450155594605996246921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562400829837898646650245 480450155594605996246921)
                    ·
                      rfl

theorem cell22_1403510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_1403510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403510 prefixEnd_1403510 := by exact prefixLift 1403510
  have htrace : WordTrace (prefixWord ++ tailWord_1403510) baseStart_1403510 baseEnd_1403510 := by
    simpa [prefixWord, tailWord_1403510, baseEnd_1403510] using wordTrace_append hprefix tailTrace_1403510
  have hstable : (prefixWord ++ tailWord_1403510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403510).length < 2 ^ (prefixWord ++ tailWord_1403510).sum := by decide
  have hdescent : baseEnd_1403510 < baseStart_1403510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403609 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 6]
def baseStart_1403609 : Nat := 118140960795 + 1403609 * 2 ^ 59
def prefixEnd_1403609 : Nat := 4983230072969 + 3 ^ 40 * 1403609 * 2
def baseEnd_1403609 : Nat := 160161348439267579340539

theorem tailTrace_1403609 : CollatzResearch.WordTrace tailWord_1403609 prefixEnd_1403609 160161348439267579340539 := by
  unfold tailWord_1403609
  simp only [CollatzResearch.WordTrace]
  refine ⟨51193825971971785177437881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34129217314647856784958587 51193825971971785177437881)
  ·
    refine ⟨38395369478978838883078411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51193825971971785177437881 38395369478978838883078411)
    ·
      refine ⟨57593054218468258324617617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38395369478978838883078411 57593054218468258324617617)
      ·
        refine ⟨43194790663851193743463213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57593054218468258324617617 43194790663851193743463213)
        ·
          refine ⟨16198046498944197653798705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43194790663851193743463213 16198046498944197653798705)
          ·
            refine ⟨12148534874208148240349029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16198046498944197653798705 12148534874208148240349029)
            ·
              refine ⟨2277850288914027795065443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12148534874208148240349029 2277850288914027795065443)
              ·
                refine ⟨3416775433371041692598165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277850288914027795065443 3416775433371041692598165)
                ·
                  refine ⟨160161348439267579340539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3416775433371041692598165 160161348439267579340539)
                  ·
                    rfl

theorem cell22_1403609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_1403609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403609 prefixEnd_1403609 := by exact prefixLift 1403609
  have htrace : WordTrace (prefixWord ++ tailWord_1403609) baseStart_1403609 baseEnd_1403609 := by
    simpa [prefixWord, tailWord_1403609, baseEnd_1403609] using wordTrace_append hprefix tailTrace_1403609
  have hstable : (prefixWord ++ tailWord_1403609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403609).length < 2 ^ (prefixWord ++ tailWord_1403609).sum := by decide
  have hdescent : baseEnd_1403609 < baseStart_1403609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403636 : List Nat := [2, 6, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1403636 : Nat := 118140960795 + 1403636 * 2 ^ 59
def prefixEnd_1403636 : Nat := 4983230072969 + 3 ^ 40 * 1403636 * 2
def baseEnd_1403636 : Nat := 480493287969583667596535

theorem tailTrace_1403636 : CollatzResearch.WordTrace tailWord_1403636 prefixEnd_1403636 480493287969583667596535 := by
  unfold tailWord_1403636
  simp only [CollatzResearch.WordTrace]
  refine ⟨25597405371436984394335381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34129873828582645859113841 25597405371436984394335381)
  ·
    refine ⟨1199878376786108643484471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25597405371436984394335381 1199878376786108643484471)
    ·
      refine ⟨1799817565179162965226707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1199878376786108643484471 1799817565179162965226707)
      ·
        refine ⟨2699726347768744447840061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799817565179162965226707 2699726347768744447840061)
        ·
          refine ⟨1012397380413279167940023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2699726347768744447840061 1012397380413279167940023)
          ·
            refine ⟨1518596070619918751910035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012397380413279167940023 1518596070619918751910035)
            ·
              refine ⟨2277894105929878127865053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518596070619918751910035 2277894105929878127865053)
              ·
                refine ⟨854210289723704297949395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2277894105929878127865053 854210289723704297949395)
                ·
                  refine ⟨1281315434585556446924093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854210289723704297949395 1281315434585556446924093)
                  ·
                    refine ⟨480493287969583667596535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1281315434585556446924093 480493287969583667596535)
                    ·
                      rfl

theorem cell22_1403636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1403636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403636 prefixEnd_1403636 := by exact prefixLift 1403636
  have htrace : WordTrace (prefixWord ++ tailWord_1403636) baseStart_1403636 baseEnd_1403636 := by
    simpa [prefixWord, tailWord_1403636, baseEnd_1403636] using wordTrace_append hprefix tailTrace_1403636
  have hstable : (prefixWord ++ tailWord_1403636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403636).length < 2 ^ (prefixWord ++ tailWord_1403636).sum := by decide
  have hdescent : baseEnd_1403636 < baseStart_1403636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403639 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 2, 4]
def baseStart_1403639 : Nat := 118140960795 + 1403639 * 2 ^ 59
def prefixEnd_1403639 : Nat := 4983230072969 + 3 ^ 40 * 1403639 * 2
def baseEnd_1403639 : Nat := 480494314930892659771525

theorem tailTrace_1403639 : CollatzResearch.WordTrace tailWord_1403639 prefixEnd_1403639 480494314930892659771525 := by
  unfold tailWord_1403639
  simp only [CollatzResearch.WordTrace]
  refine ⟨51194920161863100301029971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34129946774575400200686647 51194920161863100301029971)
  ·
    refine ⟨76792380242794650451544957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51194920161863100301029971 76792380242794650451544957)
    ·
      refine ⟨28797142591047993919329359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76792380242794650451544957 28797142591047993919329359)
      ·
        refine ⟨43195713886571990878994039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28797142591047993919329359 43195713886571990878994039)
        ·
          refine ⟨64793570829857986318491059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43195713886571990878994039 64793570829857986318491059)
          ·
            refine ⟨97190356244786979477736589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64793570829857986318491059 97190356244786979477736589)
            ·
              refine ⟨36446383591795117304151221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97190356244786979477736589 36446383591795117304151221)
              ·
                refine ⟨3416848461730792247264177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36446383591795117304151221 3416848461730792247264177)
                ·
                  refine ⟨2562636346298094185448133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3416848461730792247264177 2562636346298094185448133)
                  ·
                    refine ⟨480494314930892659771525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562636346298094185448133 480494314930892659771525)
                    ·
                      rfl

theorem cell22_1403639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_1403639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403639 prefixEnd_1403639 := by exact prefixLift 1403639
  have htrace : WordTrace (prefixWord ++ tailWord_1403639) baseStart_1403639 baseEnd_1403639 := by
    simpa [prefixWord, tailWord_1403639, baseEnd_1403639] using wordTrace_append hprefix tailTrace_1403639
  have hstable : (prefixWord ++ tailWord_1403639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403639).length < 2 ^ (prefixWord ++ tailWord_1403639).sum := by decide
  have hdescent : baseEnd_1403639 < baseStart_1403639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403656 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_1403656 : Nat := 118140960795 + 1403656 * 2 ^ 59
def prefixEnd_1403656 : Nat := 4983230072969 + 3 ^ 40 * 1403656 * 2
def baseEnd_1403656 : Nat := 480500134378310282096473

theorem tailTrace_1403656 : CollatzResearch.WordTrace tailWord_1403656 prefixEnd_1403656 480500134378310282096473 := by
  unfold tailWord_1403656
  simp only [CollatzResearch.WordTrace]
  refine ⟨25597770101400756102199411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34130360135201008136265881 25597770101400756102199411)
  ·
    refine ⟨38396655152101134153299117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25597770101400756102199411 38396655152101134153299117)
    ·
      refine ⟨14398745682037925307487169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38396655152101134153299117 14398745682037925307487169)
      ·
        refine ⟨10799059261528443980615377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14398745682037925307487169 10799059261528443980615377)
        ·
          refine ⟨8099294446146332985461533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10799059261528443980615377 8099294446146332985461533)
          ·
            refine ⟨3037235417304874869548075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8099294446146332985461533 3037235417304874869548075)
            ·
              refine ⟨4555853125957312304322113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037235417304874869548075 4555853125957312304322113)
              ·
                refine ⟨3416889844467984228241585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4555853125957312304322113 3416889844467984228241585)
                ·
                  refine ⟨2562667383350988171181189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3416889844467984228241585 2562667383350988171181189)
                  ·
                    refine ⟨480500134378310282096473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562667383350988171181189 480500134378310282096473)
                    ·
                      rfl

theorem cell22_1403656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_1403656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403656 prefixEnd_1403656 := by exact prefixLift 1403656
  have htrace : WordTrace (prefixWord ++ tailWord_1403656) baseStart_1403656 baseEnd_1403656 := by
    simpa [prefixWord, tailWord_1403656, baseEnd_1403656] using wordTrace_append hprefix tailTrace_1403656
  have hstable : (prefixWord ++ tailWord_1403656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403656).length < 2 ^ (prefixWord ++ tailWord_1403656).sum := by decide
  have hdescent : baseEnd_1403656 < baseStart_1403656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403671 : List Nat := [1, 1, 3, 4, 3, 1, 2, 7]
def baseStart_1403671 : Nat := 118140960795 + 1403671 * 2 ^ 59
def prefixEnd_1403671 : Nat := 4983230072969 + 3 ^ 40 * 1403671 * 2
def baseEnd_1403671 : Nat := 53389474353872804774603

theorem tailTrace_1403671 : CollatzResearch.WordTrace tailWord_1403671 prefixEnd_1403671 53389474353872804774603 := by
  unfold tailWord_1403671
  simp only [CollatzResearch.WordTrace]
  refine ⟨51196087297747169766194867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34130724865164779844129911 51196087297747169766194867)
  ·
    refine ⟨76794130946620754649292301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51196087297747169766194867 76794130946620754649292301)
    ·
      refine ⟨28797799104982782993484613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76794130946620754649292301 28797799104982782993484613)
      ·
        refine ⟨5399587332184271811278365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28797799104982782993484613 5399587332184271811278365)
        ·
          refine ⟨2024845249569101929229387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5399587332184271811278365 2024845249569101929229387)
          ·
            refine ⟨3037267874353652893844081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024845249569101929229387 3037267874353652893844081)
            ·
              refine ⟨2277950905765239670383061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037267874353652893844081 2277950905765239670383061)
              ·
                refine ⟨53389474353872804774603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2277950905765239670383061 53389474353872804774603)
                ·
                  rfl

theorem cell22_1403671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 7].length) (baseStart_1403671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403671 prefixEnd_1403671 := by exact prefixLift 1403671
  have htrace : WordTrace (prefixWord ++ tailWord_1403671) baseStart_1403671 baseEnd_1403671 := by
    simpa [prefixWord, tailWord_1403671, baseEnd_1403671] using wordTrace_append hprefix tailTrace_1403671
  have hstable : (prefixWord ++ tailWord_1403671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403671).length < 2 ^ (prefixWord ++ tailWord_1403671).sum := by decide
  have hdescent : baseEnd_1403671 < baseStart_1403671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403690 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1403690 : Nat := 118140960795 + 1403690 * 2 ^ 59
def prefixEnd_1403690 : Nat := 4983230072969 + 3 ^ 40 * 1403690 * 2
def baseEnd_1403690 : Nat := 480511773273145526746369

theorem tailTrace_1403690 : CollatzResearch.WordTrace tailWord_1403690 prefixEnd_1403690 480511773273145526746369 := by
  unfold tailWord_1403690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12799195071169584002784131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34131186856452224007424349 12799195071169584002784131)
  ·
    refine ⟨19198792606754376004176197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12799195071169584002784131 19198792606754376004176197)
    ·
      refine ⟨3599773613766445500783037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19198792606754376004176197 3599773613766445500783037)
      ·
        refine ⟨1349915105162417062793639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3599773613766445500783037 1349915105162417062793639)
        ·
          refine ⟨2024872657743625594190459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349915105162417062793639 2024872657743625594190459)
          ·
            refine ⟨3037308986615438391285689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024872657743625594190459 3037308986615438391285689)
            ·
              refine ⟨2277981739961578793464267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037308986615438391285689 2277981739961578793464267)
              ·
                refine ⟨3416972609942368190196401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277981739961578793464267 3416972609942368190196401)
                ·
                  refine ⟨2562729457456776142647301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3416972609942368190196401 2562729457456776142647301)
                  ·
                    refine ⟨480511773273145526746369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562729457456776142647301 480511773273145526746369)
                    ·
                      rfl

theorem cell22_1403690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1403690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403690 prefixEnd_1403690 := by exact prefixLift 1403690
  have htrace : WordTrace (prefixWord ++ tailWord_1403690) baseStart_1403690 baseEnd_1403690 := by
    simpa [prefixWord, tailWord_1403690, baseEnd_1403690] using wordTrace_append hprefix tailTrace_1403690
  have hstable : (prefixWord ++ tailWord_1403690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403690).length < 2 ^ (prefixWord ++ tailWord_1403690).sum := by decide
  have hdescent : baseEnd_1403690 < baseStart_1403690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403703 : List Nat := [1, 1, 3, 1, 2, 1, 4, 5, 1, 3]
def baseStart_1403703 : Nat := 118140960795 + 1403703 * 2 ^ 59
def prefixEnd_1403703 : Nat := 4983230072969 + 3 ^ 40 * 1403703 * 2
def baseEnd_1403703 : Nat := 480516223438817826171329

theorem tailTrace_1403703 : CollatzResearch.WordTrace tailWord_1403703 prefixEnd_1403703 480516223438817826171329 := by
  unfold tailWord_1403703
  simp only [CollatzResearch.WordTrace]
  refine ⟨51197254433631239231359763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34131502955754159487573175 51197254433631239231359763)
  ·
    refine ⟨76795881650446858847039645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51197254433631239231359763 76795881650446858847039645)
    ·
      refine ⟨28798455618917572067639867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76795881650446858847039645 28798455618917572067639867)
      ·
        refine ⟨43197683428376358101459801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28798455618917572067639867 43197683428376358101459801)
        ·
          refine ⟨32398262571282268576094851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43197683428376358101459801 32398262571282268576094851)
          ·
            refine ⟨48597393856923402864142277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32398262571282268576094851 48597393856923402864142277)
            ·
              refine ⟨9112011348173138037026677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48597393856923402864142277 9112011348173138037026677)
              ·
                refine ⟨854251063891231690971251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9112011348173138037026677 854251063891231690971251)
                ·
                  refine ⟨1281376595836847536456877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854251063891231690971251 1281376595836847536456877)
                  ·
                    refine ⟨480516223438817826171329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1281376595836847536456877 480516223438817826171329)
                    ·
                      rfl

theorem cell22_1403703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_1403703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403703 prefixEnd_1403703 := by exact prefixLift 1403703
  have htrace : WordTrace (prefixWord ++ tailWord_1403703) baseStart_1403703 baseEnd_1403703 := by
    simpa [prefixWord, tailWord_1403703, baseEnd_1403703] using wordTrace_append hprefix tailTrace_1403703
  have hstable : (prefixWord ++ tailWord_1403703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403703).length < 2 ^ (prefixWord ++ tailWord_1403703).sum := by decide
  have hdescent : baseEnd_1403703 < baseStart_1403703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403763 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 1, 4]
def baseStart_1403763 : Nat := 118140960795 + 1403763 * 2 ^ 59
def prefixEnd_1403763 : Nat := 4983230072969 + 3 ^ 40 * 1403763 * 2
def baseEnd_1403763 : Nat := 480536762664997669671145

theorem tailTrace_1403763 : CollatzResearch.WordTrace tailWord_1403763 prefixEnd_1403763 480536762664997669671145 := by
  unfold tailWord_1403763
  simp only [CollatzResearch.WordTrace]
  refine ⟨51199442813413869478543943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34132961875609246319029295 51199442813413869478543943)
  ·
    refine ⟨76799164220120804217815915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51199442813413869478543943 76799164220120804217815915)
    ·
      refine ⟨115198746330181206326723873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76799164220120804217815915 115198746330181206326723873)
      ·
        refine ⟨86399059747635904745042905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115198746330181206326723873 86399059747635904745042905)
        ·
          refine ⟨64799294810726928558782179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86399059747635904745042905 64799294810726928558782179)
          ·
            refine ⟨97198942216090392838173269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64799294810726928558782179 97198942216090392838173269)
            ·
              refine ⟨1139050104094809291072343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 97198942216090392838173269 1139050104094809291072343)
              ·
                refine ⟨1708575156142213936608515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139050104094809291072343 1708575156142213936608515)
                ·
                  refine ⟨2562862734213320904912773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708575156142213936608515 2562862734213320904912773)
                  ·
                    refine ⟨480536762664997669671145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562862734213320904912773 480536762664997669671145)
                    ·
                      rfl

theorem cell22_1403763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 4].length) (baseStart_1403763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403763 prefixEnd_1403763 := by exact prefixLift 1403763
  have htrace : WordTrace (prefixWord ++ tailWord_1403763) baseStart_1403763 baseEnd_1403763 := by
    simpa [prefixWord, tailWord_1403763, baseEnd_1403763] using wordTrace_append hprefix tailTrace_1403763
  have hstable : (prefixWord ++ tailWord_1403763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403763).length < 2 ^ (prefixWord ++ tailWord_1403763).sum := by decide
  have hdescent : baseEnd_1403763 < baseStart_1403763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403889 : List Nat := [1, 2, 2, 2, 4, 3, 2, 2, 1, 3]
def baseStart_1403889 : Nat := 118140960795 + 1403889 * 2 ^ 59
def prefixEnd_1403889 : Nat := 4983230072969 + 3 ^ 40 * 1403889 * 2
def baseEnd_1403889 : Nat := 480579895039975341020759

theorem tailTrace_1403889 : CollatzResearch.WordTrace tailWord_1403889 prefixEnd_1403889 480579895039975341020759 := by
  unfold tailWord_1403889
  simp only [CollatzResearch.WordTrace]
  refine ⟨51204038410957392997630721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34136025607304928665087147 51204038410957392997630721)
  ·
    refine ⟨38403028808218044748223041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51204038410957392997630721 38403028808218044748223041)
    ·
      refine ⟨28802271606163533561167281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38403028808218044748223041 28802271606163533561167281)
      ·
        refine ⟨21601703704622650170875461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28802271606163533561167281 21601703704622650170875461)
        ·
          refine ⟨4050319444616746907039149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21601703704622650170875461 4050319444616746907039149)
          ·
            refine ⟨1518869791731280090139681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4050319444616746907039149 1518869791731280090139681)
            ·
              refine ⟨1139152343798460067604761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518869791731280090139681 1139152343798460067604761)
              ·
                refine ⟨854364257848845050703571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139152343798460067604761 854364257848845050703571)
                ·
                  refine ⟨1281546386773267576055357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854364257848845050703571 1281546386773267576055357)
                  ·
                    refine ⟨480579895039975341020759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1281546386773267576055357 480579895039975341020759)
                    ·
                      rfl

theorem cell22_1403889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_1403889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403889 prefixEnd_1403889 := by exact prefixLift 1403889
  have htrace : WordTrace (prefixWord ++ tailWord_1403889) baseStart_1403889 baseEnd_1403889 := by
    simpa [prefixWord, tailWord_1403889, baseEnd_1403889] using wordTrace_append hprefix tailTrace_1403889
  have hstable : (prefixWord ++ tailWord_1403889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403889).length < 2 ^ (prefixWord ++ tailWord_1403889).sum := by decide
  have hdescent : baseEnd_1403889 < baseStart_1403889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403896 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 6]
def baseStart_1403896 : Nat := 118140960795 + 1403896 * 2 ^ 59
def prefixEnd_1403896 : Nat := 4983230072969 + 3 ^ 40 * 1403896 * 2
def baseEnd_1403896 : Nat := 160194097094343218698579

theorem tailTrace_1403896 : CollatzResearch.WordTrace tailWord_1403896 prefixEnd_1403896 160194097094343218698579 := by
  unfold tailWord_1403896
  simp only [CollatzResearch.WordTrace]
  refine ⟨25602146860966016596567771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34136195814621355462090361 25602146860966016596567771)
  ·
    refine ⟨38403220291449024894851657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25602146860966016596567771 38403220291449024894851657)
    ·
      refine ⟨28802415218586768671138743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38403220291449024894851657 28802415218586768671138743)
      ·
        refine ⟨43203622827880153006708115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28802415218586768671138743 43203622827880153006708115)
        ·
          refine ⟨64805434241820229510062173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43203622827880153006708115 64805434241820229510062173)
          ·
            refine ⟨24302037840682586066273315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64805434241820229510062173 24302037840682586066273315)
            ·
              refine ⟨36453056761023879099409973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24302037840682586066273315 36453056761023879099409973)
              ·
                refine ⟨3417474071345988665569685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36453056761023879099409973 3417474071345988665569685)
                ·
                  refine ⟨160194097094343218698579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3417474071345988665569685 160194097094343218698579)
                  ·
                    rfl

theorem cell22_1403896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_1403896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403896 prefixEnd_1403896 := by exact prefixLift 1403896
  have htrace : WordTrace (prefixWord ++ tailWord_1403896) baseStart_1403896 baseEnd_1403896 := by
    simpa [prefixWord, tailWord_1403896, baseEnd_1403896] using wordTrace_append hprefix tailTrace_1403896
  have hstable : (prefixWord ++ tailWord_1403896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403896).length < 2 ^ (prefixWord ++ tailWord_1403896).sum := by decide
  have hdescent : baseEnd_1403896 < baseStart_1403896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403928 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_1403928 : Nat := 118140960795 + 1403928 * 2 ^ 59
def prefixEnd_1403928 : Nat := 4983230072969 + 3 ^ 40 * 1403928 * 2
def baseEnd_1403928 : Nat := 480593245536992239295639

theorem tailTrace_1403928 : CollatzResearch.WordTrace tailWord_1403928 prefixEnd_1403928 480593245536992239295639 := by
  unfold tailWord_1403928
  simp only [CollatzResearch.WordTrace]
  refine ⟨25602730428908051329150219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34136973905210735105533625 25602730428908051329150219)
  ·
    refine ⟨38404095643362076993725329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25602730428908051329150219 38404095643362076993725329)
    ·
      refine ⟨28803071732521557745293997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38404095643362076993725329 28803071732521557745293997)
      ·
        refine ⟨10801151899695584154485249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28803071732521557745293997 10801151899695584154485249)
        ·
          refine ⟨8100863924771688115863937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10801151899695584154485249 8100863924771688115863937)
          ·
            refine ⟨6075647943578766086897953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8100863924771688115863937 6075647943578766086897953)
            ·
              refine ⟨4556735957684074565173465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6075647943578766086897953 4556735957684074565173465)
              ·
                refine ⟨3417551968263055923880099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4556735957684074565173465 3417551968263055923880099)
                ·
                  refine ⟨5126327952394583885820149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3417551968263055923880099 5126327952394583885820149)
                  ·
                    refine ⟨480593245536992239295639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5126327952394583885820149 480593245536992239295639)
                    ·
                      rfl

theorem cell22_1403928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_1403928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403928 prefixEnd_1403928 := by exact prefixLift 1403928
  have htrace : WordTrace (prefixWord ++ tailWord_1403928) baseStart_1403928 baseEnd_1403928 := by
    simpa [prefixWord, tailWord_1403928, baseEnd_1403928] using wordTrace_append hprefix tailTrace_1403928
  have hstable : (prefixWord ++ tailWord_1403928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403928).length < 2 ^ (prefixWord ++ tailWord_1403928).sum := by decide
  have hdescent : baseEnd_1403928 < baseStart_1403928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403930 : List Nat := [3, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_1403930 : Nat := 118140960795 + 1403930 * 2 ^ 59
def prefixEnd_1403930 : Nat := 4983230072969 + 3 ^ 40 * 1403930 * 2
def baseEnd_1403930 : Nat := 160197976725954966915211

theorem tailTrace_1403930 : CollatzResearch.WordTrace tailWord_1403930 prefixEnd_1403930 160197976725954966915211 := by
  unfold tailWord_1403930
  simp only [CollatzResearch.WordTrace]
  refine ⟨12801383450952214249968311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34137022535872571333248829 12801383450952214249968311)
  ·
    refine ⟨19202075176428321374952467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12801383450952214249968311 19202075176428321374952467)
    ·
      refine ⟨28803112764642482062428701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19202075176428321374952467 28803112764642482062428701)
      ·
        refine ⟨10801167286740930773410763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28803112764642482062428701 10801167286740930773410763)
        ·
          refine ⟨16201750930111396160116145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10801167286740930773410763 16201750930111396160116145)
          ·
            refine ⟨12151313197583547120087109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16201750930111396160116145 12151313197583547120087109)
            ·
              refine ⟨2278371224546915085016333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12151313197583547120087109 2278371224546915085016333)
              ·
                refine ⟨854389209205093156881125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2278371224546915085016333 854389209205093156881125)
                ·
                  refine ⟨160197976725954966915211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854389209205093156881125 160197976725954966915211)
                  ·
                    rfl

theorem cell22_1403930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_1403930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403930 prefixEnd_1403930 := by exact prefixLift 1403930
  have htrace : WordTrace (prefixWord ++ tailWord_1403930) baseStart_1403930 baseEnd_1403930 := by
    simpa [prefixWord, tailWord_1403930, baseEnd_1403930] using wordTrace_append hprefix tailTrace_1403930
  have hstable : (prefixWord ++ tailWord_1403930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403930).length < 2 ^ (prefixWord ++ tailWord_1403930).sum := by decide
  have hdescent : baseEnd_1403930 < baseStart_1403930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403941 : List Nat := [1, 3, 1, 2, 2, 2, 11]
def baseStart_1403941 : Nat := 118140960795 + 1403941 * 2 ^ 59
def prefixEnd_1403941 : Nat := 4983230072969 + 3 ^ 40 * 1403941 * 2
def baseEnd_1403941 : Nat := 17799914655654242174837

theorem tailTrace_1403941 : CollatzResearch.WordTrace tailWord_1403941 prefixEnd_1403941 17799914655654242174837 := by
  unfold tailWord_1403941
  simp only [CollatzResearch.WordTrace]
  refine ⟨51205935006769005878523677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34137290004512670585682451 51205935006769005878523677)
  ·
    refine ⟨19202225627538377204446379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51205935006769005878523677 19202225627538377204446379)
    ·
      refine ⟨28803338441307565806669569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19202225627538377204446379 28803338441307565806669569)
      ·
        refine ⟨21602503830980674355002177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28803338441307565806669569 21602503830980674355002177)
        ·
          refine ⟨16201877873235505766251633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21602503830980674355002177 16201877873235505766251633)
          ·
            refine ⟨12151408404926629324688725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16201877873235505766251633 12151408404926629324688725)
            ·
              refine ⟨17799914655654242174837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12151408404926629324688725 17799914655654242174837)
              ·
                rfl

theorem cell22_1403941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 11].length) (baseStart_1403941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403941 prefixEnd_1403941 := by exact prefixLift 1403941
  have htrace : WordTrace (prefixWord ++ tailWord_1403941) baseStart_1403941 baseEnd_1403941 := by
    simpa [prefixWord, tailWord_1403941, baseEnd_1403941] using wordTrace_append hprefix tailTrace_1403941
  have hstable : (prefixWord ++ tailWord_1403941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403941).length < 2 ^ (prefixWord ++ tailWord_1403941).sum := by decide
  have hdescent : baseEnd_1403941 < baseStart_1403941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403975 : List Nat := [1, 1, 4, 1, 3, 4, 2, 6]
def baseStart_1403975 : Nat := 118140960795 + 1403975 * 2 ^ 59
def prefixEnd_1403975 : Nat := 4983230072969 + 3 ^ 40 * 1403975 * 2
def baseEnd_1403975 : Nat := 53401037177499975930055

theorem tailTrace_1403975 : CollatzResearch.WordTrace tailWord_1403975 prefixEnd_1403975 53401037177499975930055 := by
  unfold tailWord_1403975
  simp only [CollatzResearch.WordTrace]
  refine ⟨51207175088645829685261379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34138116725763886456840919 51207175088645829685261379)
  ·
    refine ⟨76810762632968744527892069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51207175088645829685261379 76810762632968744527892069)
    ·
      refine ⟨14402017993681639598979763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76810762632968744527892069 14402017993681639598979763)
      ·
        refine ⟨21603026990522459398469645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14402017993681639598979763 21603026990522459398469645)
        ·
          refine ⟨8101135121445922274426117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21603026990522459398469645 8101135121445922274426117)
          ·
            refine ⟨1518962835271110426454897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8101135121445922274426117 1518962835271110426454897)
            ·
              refine ⟨1139222126453332819841173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518962835271110426454897 1139222126453332819841173)
              ·
                refine ⟨53401037177499975930055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1139222126453332819841173 53401037177499975930055)
                ·
                  rfl

theorem cell22_1403975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 6].length) (baseStart_1403975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1403975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1403975 prefixEnd_1403975 := by exact prefixLift 1403975
  have htrace : WordTrace (prefixWord ++ tailWord_1403975) baseStart_1403975 baseEnd_1403975 := by
    simpa [prefixWord, tailWord_1403975, baseEnd_1403975] using wordTrace_append hprefix tailTrace_1403975
  have hstable : (prefixWord ++ tailWord_1403975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403975).length < 2 ^ (prefixWord ++ tailWord_1403975).sum := by decide
  have hdescent : baseEnd_1403975 < baseStart_1403975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404003 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 5]
def baseStart_1404003 : Nat := 118140960795 + 1404003 * 2 ^ 59
def prefixEnd_1404003 : Nat := 4983230072969 + 3 ^ 40 * 1404003 * 2
def baseEnd_1404003 : Nat := 160206306523239014556803

theorem tailTrace_1404003 : CollatzResearch.WordTrace tailWord_1404003 prefixEnd_1404003 160206306523239014556803 := by
  unfold tailWord_1404003
  simp only [CollatzResearch.WordTrace]
  refine ⟨51208196332544390467280663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34138797555029593644853775 51208196332544390467280663)
  ·
    refine ⟨76812294498816585700920995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51208196332544390467280663 76812294498816585700920995)
    ·
      refine ⟨115218441748224878551381493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76812294498816585700920995 115218441748224878551381493)
      ·
        refine ⟨10801728913896082364192015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115218441748224878551381493 10801728913896082364192015)
        ·
          refine ⟨16202593370844123546288023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10801728913896082364192015 16202593370844123546288023)
          ·
            refine ⟨24303890056266185319432035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16202593370844123546288023 24303890056266185319432035)
            ·
              refine ⟨36455835084399277979148053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24303890056266185319432035 36455835084399277979148053)
              ·
                refine ⟨1708867269581216155272565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36455835084399277979148053 1708867269581216155272565)
                ·
                  refine ⟨160206306523239014556803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1708867269581216155272565 160206306523239014556803)
                  ·
                    rfl

theorem cell22_1404003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 5].length) (baseStart_1404003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404003 prefixEnd_1404003 := by exact prefixLift 1404003
  have htrace : WordTrace (prefixWord ++ tailWord_1404003) baseStart_1404003 baseEnd_1404003 := by
    simpa [prefixWord, tailWord_1404003, baseEnd_1404003] using wordTrace_append hprefix tailTrace_1404003
  have hstable : (prefixWord ++ tailWord_1404003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404003).length < 2 ^ (prefixWord ++ tailWord_1404003).sum := by decide
  have hdescent : baseEnd_1404003 < baseStart_1404003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404007 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1404007 : Nat := 118140960795 + 1404007 * 2 ^ 59
def prefixEnd_1404007 : Nat := 4983230072969 + 3 ^ 40 * 1404007 * 2
def baseEnd_1404007 : Nat := 480620288851462366570397

theorem tailTrace_1404007 : CollatzResearch.WordTrace tailWord_1404007 prefixEnd_1404007 480620288851462366570397 := by
  unfold tailWord_1404007
  simp only [CollatzResearch.WordTrace]
  refine ⟨51208342224529899150426275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34138894816353266100284183 51208342224529899150426275)
  ·
    refine ⟨76812513336794848725639413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51208342224529899150426275 76812513336794848725639413)
    ·
      refine ⟨7201173125324517068028695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76812513336794848725639413 7201173125324517068028695)
      ·
        refine ⟨10801759687986775602043043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7201173125324517068028695 10801759687986775602043043)
        ·
          refine ⟨16202639531980163403064565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10801759687986775602043043 16202639531980163403064565)
          ·
            refine ⟨1518997456123140319037303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16202639531980163403064565 1518997456123140319037303)
            ·
              refine ⟨2278496184184710478555955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518997456123140319037303 2278496184184710478555955)
              ·
                refine ⟨3417744276277065717833933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278496184184710478555955 3417744276277065717833933)
                ·
                  refine ⟨1281654103603899644187725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3417744276277065717833933 1281654103603899644187725)
                  ·
                    refine ⟨480620288851462366570397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1281654103603899644187725 480620288851462366570397)
                    ·
                      rfl

theorem cell22_1404007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1404007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404007 prefixEnd_1404007 := by exact prefixLift 1404007
  have htrace : WordTrace (prefixWord ++ tailWord_1404007) baseStart_1404007 baseEnd_1404007 := by
    simpa [prefixWord, tailWord_1404007, baseEnd_1404007] using wordTrace_append hprefix tailTrace_1404007
  have hstable : (prefixWord ++ tailWord_1404007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404007).length < 2 ^ (prefixWord ++ tailWord_1404007).sum := by decide
  have hdescent : baseEnd_1404007 < baseStart_1404007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404018 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1404018 : Nat := 118140960795 + 1404018 * 2 ^ 59
def prefixEnd_1404018 : Nat := 4983230072969 + 3 ^ 40 * 1404018 * 2
def baseEnd_1404018 : Nat := 480624054376262004545363

theorem tailTrace_1404018 : CollatzResearch.WordTrace tailWord_1404018 prefixEnd_1404018 480624054376262004545363 := by
  unfold tailWord_1404018
  simp only [CollatzResearch.WordTrace]
  refine ⟨12802185856872512007269177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34139162284993365352717805 12802185856872512007269177)
  ·
    refine ⟨9601639392654384005451883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12802185856872512007269177 9601639392654384005451883)
    ·
      refine ⟨14402459088981576008177825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9601639392654384005451883 14402459088981576008177825)
      ·
        refine ⟨10801844316736182006133369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14402459088981576008177825 10801844316736182006133369)
        ·
          refine ⟨8101383237552136504600027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10801844316736182006133369 8101383237552136504600027)
          ·
            refine ⟨12152074856328204756900041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8101383237552136504600027 12152074856328204756900041)
            ·
              refine ⟨9114056142246153567675031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12152074856328204756900041 9114056142246153567675031)
              ·
                refine ⟨13671084213369230351512547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9114056142246153567675031 13671084213369230351512547)
                ·
                  refine ⟨20506626320053845527268821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13671084213369230351512547 20506626320053845527268821)
                  ·
                    refine ⟨480624054376262004545363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20506626320053845527268821 480624054376262004545363)
                    ·
                      rfl

theorem cell22_1404018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1404018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404018 prefixEnd_1404018 := by exact prefixLift 1404018
  have htrace : WordTrace (prefixWord ++ tailWord_1404018) baseStart_1404018 baseEnd_1404018 := by
    simpa [prefixWord, tailWord_1404018, baseEnd_1404018] using wordTrace_append hprefix tailTrace_1404018
  have hstable : (prefixWord ++ tailWord_1404018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404018).length < 2 ^ (prefixWord ++ tailWord_1404018).sum := by decide
  have hdescent : baseEnd_1404018 < baseStart_1404018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404093 : List Nat := [1, 4, 1, 2, 1, 1, 2, 10]
def baseStart_1404093 : Nat := 118140960795 + 1404093 * 2 ^ 59
def prefixEnd_1404093 : Nat := 4983230072969 + 3 ^ 40 * 1404093 * 2
def baseEnd_1404093 : Nat := 53405525378776312102237

theorem tailTrace_1404093 : CollatzResearch.WordTrace tailWord_1404093 prefixEnd_1404093 53405525378776312102237 := by
  unfold tailWord_1404093
  simp only [CollatzResearch.WordTrace]
  refine ⟨51211478902218335838056933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34140985934812223892037955 51211478902218335838056933)
  ·
    refine ⟨9602152294165937969635675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51211478902218335838056933 9602152294165937969635675)
    ·
      refine ⟨14403228441248906954453513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9602152294165937969635675 14403228441248906954453513)
      ·
        refine ⟨10802421330936680215840135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14403228441248906954453513 10802421330936680215840135)
        ·
          refine ⟨16203631996405020323760203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10802421330936680215840135 16203631996405020323760203)
          ·
            refine ⟨24305447994607530485640305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16203631996405020323760203 24305447994607530485640305)
            ·
              refine ⟨18229085995955647864230229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24305447994607530485640305 18229085995955647864230229)
              ·
                refine ⟨53405525378776312102237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18229085995955647864230229 53405525378776312102237)
                ·
                  rfl

theorem cell22_1404093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 10].length) (baseStart_1404093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404093 prefixEnd_1404093 := by exact prefixLift 1404093
  have htrace : WordTrace (prefixWord ++ tailWord_1404093) baseStart_1404093 baseEnd_1404093 := by
    simpa [prefixWord, tailWord_1404093, baseEnd_1404093] using wordTrace_append hprefix tailTrace_1404093
  have hstable : (prefixWord ++ tailWord_1404093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404093).length < 2 ^ (prefixWord ++ tailWord_1404093).sum := by decide
  have hdescent : baseEnd_1404093 < baseStart_1404093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404095 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 2, 4]
def baseStart_1404095 : Nat := 118140960795 + 1404095 * 2 ^ 59
def prefixEnd_1404095 : Nat := 4983230072969 + 3 ^ 40 * 1404095 * 2
def baseEnd_1404095 : Nat := 480650413049859470370127

theorem tailTrace_1404095 : CollatzResearch.WordTrace tailWord_1404095 prefixEnd_1404095 480650413049859470370127 := by
  unfold tailWord_1404095
  simp only [CollatzResearch.WordTrace]
  refine ⟨51211551848211090179629739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34141034565474060119753159 51211551848211090179629739)
  ·
    refine ⟨76817327772316635269444609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51211551848211090179629739 76817327772316635269444609)
    ·
      refine ⟨57612995829237476452083457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76817327772316635269444609 57612995829237476452083457)
      ·
        refine ⟨43209746871928107339062593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57612995829237476452083457 43209746871928107339062593)
        ·
          refine ⟨32407310153946080504296945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43209746871928107339062593 32407310153946080504296945)
          ·
            refine ⟨24305482615459560378222709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32407310153946080504296945 24305482615459560378222709)
            ·
              refine ⟨2278638995199333785458379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24305482615459560378222709 2278638995199333785458379)
              ·
                refine ⟨3417958492799000678187569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278638995199333785458379 3417958492799000678187569)
                ·
                  refine ⟨2563468869599250508640677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3417958492799000678187569 2563468869599250508640677)
                  ·
                    refine ⟨480650413049859470370127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2563468869599250508640677 480650413049859470370127)
                    ·
                      rfl

theorem cell22_1404095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_1404095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404095 prefixEnd_1404095 := by exact prefixLift 1404095
  have htrace : WordTrace (prefixWord ++ tailWord_1404095) baseStart_1404095 baseEnd_1404095 := by
    simpa [prefixWord, tailWord_1404095, baseEnd_1404095] using wordTrace_append hprefix tailTrace_1404095
  have hstable : (prefixWord ++ tailWord_1404095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404095).length < 2 ^ (prefixWord ++ tailWord_1404095).sum := by decide
  have hdescent : baseEnd_1404095 < baseStart_1404095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404097 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1404097 : Nat := 118140960795 + 1404097 * 2 ^ 59
def prefixEnd_1404097 : Nat := 4983230072969 + 3 ^ 40 * 1404097 * 2
def baseEnd_1404097 : Nat := 480651097690732131820121

theorem tailTrace_1404097 : CollatzResearch.WordTrace tailWord_1404097 prefixEnd_1404097 480651097690732131820121 := by
  unfold tailWord_1404097
  simp only [CollatzResearch.WordTrace]
  refine ⟨51211624794203844521202545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34141083196135896347468363 51211624794203844521202545)
  ·
    refine ⟨38408718595652883390901909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51211624794203844521202545 38408718595652883390901909)
    ·
      refine ⟨1800408684171228908948527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38408718595652883390901909 1800408684171228908948527)
      ·
        refine ⟨2700613026256843363422791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800408684171228908948527 2700613026256843363422791)
        ·
          refine ⟨4050919539385265045134187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700613026256843363422791 4050919539385265045134187)
          ·
            refine ⟨6076379309077897567701281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4050919539385265045134187 6076379309077897567701281)
            ·
              refine ⟨4557284481808423175775961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6076379309077897567701281 4557284481808423175775961)
              ·
                refine ⟨3417963361356317381831971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4557284481808423175775961 3417963361356317381831971)
                ·
                  refine ⟨5126945042034476072747957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3417963361356317381831971 5126945042034476072747957)
                  ·
                    refine ⟨480651097690732131820121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5126945042034476072747957 480651097690732131820121)
                    ·
                      rfl

theorem cell22_1404097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1404097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404097 prefixEnd_1404097 := by exact prefixLift 1404097
  have htrace : WordTrace (prefixWord ++ tailWord_1404097) baseStart_1404097 baseEnd_1404097 := by
    simpa [prefixWord, tailWord_1404097, baseEnd_1404097] using wordTrace_append hprefix tailTrace_1404097
  have hstable : (prefixWord ++ tailWord_1404097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404097).length < 2 ^ (prefixWord ++ tailWord_1404097).sum := by decide
  have hdescent : baseEnd_1404097 < baseStart_1404097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404110 : List Nat := [4, 1, 1, 1, 5, 1, 9]
def baseStart_1404110 : Nat := 118140960795 + 1404110 * 2 ^ 59
def prefixEnd_1404110 : Nat := 4983230072969 + 3 ^ 40 * 1404110 * 2
def baseEnd_1404110 : Nat := 17802057328014978935003

theorem tailTrace_1404110 : CollatzResearch.WordTrace tailWord_1404110 prefixEnd_1404110 17802057328014978935003 := by
  unfold tailWord_1404110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401512367894593467678223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34141399295437831827617189 6401512367894593467678223)
  ·
    refine ⟨9602268551841890201517335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6401512367894593467678223 9602268551841890201517335)
    ·
      refine ⟨14403402827762835302276003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9602268551841890201517335 14403402827762835302276003)
      ·
        refine ⟨21605104241644252953414005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14403402827762835302276003 21605104241644252953414005)
        ·
          refine ⟨2025478522654148714382563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21605104241644252953414005 2025478522654148714382563)
          ·
            refine ⟨3038217783981223071573845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025478522654148714382563 3038217783981223071573845)
            ·
              refine ⟨17802057328014978935003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3038217783981223071573845 17802057328014978935003)
              ·
                rfl

theorem cell22_1404110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 9].length) (baseStart_1404110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404110 prefixEnd_1404110 := by exact prefixLift 1404110
  have htrace : WordTrace (prefixWord ++ tailWord_1404110) baseStart_1404110 baseEnd_1404110 := by
    simpa [prefixWord, tailWord_1404110, baseEnd_1404110] using wordTrace_append hprefix tailTrace_1404110
  have hstable : (prefixWord ++ tailWord_1404110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404110).length < 2 ^ (prefixWord ++ tailWord_1404110).sum := by decide
  have hdescent : baseEnd_1404110 < baseStart_1404110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404142 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1404142 : Nat := 118140960795 + 1404142 * 2 ^ 59
def prefixEnd_1404142 : Nat := 4983230072969 + 3 ^ 40 * 1404142 * 2
def baseEnd_1404142 : Nat := 480666502110367014444983

theorem tailTrace_1404142 : CollatzResearch.WordTrace tailWord_1404142 prefixEnd_1404142 480666502110367014444983 := by
  unfold tailWord_1404142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401658259880102150823835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34142177386027211471060453 6401658259880102150823835)
  ·
    refine ⟨9602487389820153226235753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6401658259880102150823835 9602487389820153226235753)
    ·
      refine ⟨7201865542365114919676815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9602487389820153226235753 7201865542365114919676815)
      ·
        refine ⟨10802798313547672379515223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7201865542365114919676815 10802798313547672379515223)
        ·
          refine ⟨16204197470321508569272835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10802798313547672379515223 16204197470321508569272835)
          ·
            refine ⟨24306296205482262853909253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16204197470321508569272835 24306296205482262853909253)
            ·
              refine ⟨4557430538527924285107985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24306296205482262853909253 4557430538527924285107985)
              ·
                refine ⟨3418072903895943213830989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4557430538527924285107985 3418072903895943213830989)
                ·
                  refine ⟨1281777338960978705186621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3418072903895943213830989 1281777338960978705186621)
                  ·
                    refine ⟨480666502110367014444983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1281777338960978705186621 480666502110367014444983)
                    ·
                      rfl

theorem cell22_1404142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1404142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404142 prefixEnd_1404142 := by exact prefixLift 1404142
  have htrace : WordTrace (prefixWord ++ tailWord_1404142) baseStart_1404142 baseEnd_1404142 := by
    simpa [prefixWord, tailWord_1404142, baseEnd_1404142] using wordTrace_append hprefix tailTrace_1404142
  have hstable : (prefixWord ++ tailWord_1404142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404142).length < 2 ^ (prefixWord ++ tailWord_1404142).sum := by decide
  have hdescent : baseEnd_1404142 < baseStart_1404142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404159 : List Nat := [1, 1, 2, 2, 1, 5, 3, 3, 1, 3]
def baseStart_1404159 : Nat := 118140960795 + 1404159 * 2 ^ 59
def prefixEnd_1404159 : Nat := 4983230072969 + 3 ^ 40 * 1404159 * 2
def baseEnd_1404159 : Nat := 480672321557784636769931

theorem tailTrace_1404159 : CollatzResearch.WordTrace tailWord_1404159 prefixEnd_1404159 480672321557784636769931 := by
  unfold tailWord_1404159
  simp only [CollatzResearch.WordTrace]
  refine ⟨51213886119979229109959531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34142590746652819406639687 51213886119979229109959531)
  ·
    refine ⟨76820829179968843664939297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51213886119979229109959531 76820829179968843664939297)
    ·
      refine ⟨57615621884976632748704473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76820829179968843664939297 57615621884976632748704473)
      ·
        refine ⟨43211716413732474561528355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57615621884976632748704473 43211716413732474561528355)
        ·
          refine ⟨64817574620598711842292533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43211716413732474561528355 64817574620598711842292533)
          ·
            refine ⟨6076647620681129235214925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64817574620598711842292533 6076647620681129235214925)
            ·
              refine ⟨2278742857755423463205597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6076647620681129235214925 2278742857755423463205597)
              ·
                refine ⟨854528571658283798702099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2278742857755423463205597 854528571658283798702099)
                ·
                  refine ⟨1281792857487425698053149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854528571658283798702099 1281792857487425698053149)
                  ·
                    refine ⟨480672321557784636769931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1281792857487425698053149 480672321557784636769931)
                    ·
                      rfl

theorem cell22_1404159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 3].length) (baseStart_1404159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404159 prefixEnd_1404159 := by exact prefixLift 1404159
  have htrace : WordTrace (prefixWord ++ tailWord_1404159) baseStart_1404159 baseEnd_1404159 := by
    simpa [prefixWord, tailWord_1404159, baseEnd_1404159] using wordTrace_append hprefix tailTrace_1404159
  have hstable : (prefixWord ++ tailWord_1404159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404159).length < 2 ^ (prefixWord ++ tailWord_1404159).sum := by decide
  have hdescent : baseEnd_1404159 < baseStart_1404159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404189 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 5]
def baseStart_1404189 : Nat := 118140960795 + 1404189 * 2 ^ 59
def prefixEnd_1404189 : Nat := 4983230072969 + 3 ^ 40 * 1404189 * 2
def baseEnd_1404189 : Nat := 160227530390291519506613

theorem tailTrace_1404189 : CollatzResearch.WordTrace tailWord_1404189 prefixEnd_1404189 160227530390291519506613 := by
  unfold tailWord_1404189
  simp only [CollatzResearch.WordTrace]
  refine ⟨51214980309870544233551621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34143320206580362822367747 51214980309870544233551621)
  ·
    refine ⟨9602808808100727043790929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51214980309870544233551621 9602808808100727043790929)
    ·
      refine ⟨7202106606075545282843197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9602808808100727043790929 7202106606075545282843197)
      ·
        refine ⟨2700789977278329481066199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7202106606075545282843197 2700789977278329481066199)
        ·
          refine ⟨4051184965917494221599299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700789977278329481066199 4051184965917494221599299)
          ·
            refine ⟨6076777448876241332398949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051184965917494221599299 6076777448876241332398949)
            ·
              refine ⟨1139395771664295249824803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6076777448876241332398949 1139395771664295249824803)
              ·
                refine ⟨1709093657496442874737205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139395771664295249824803 1709093657496442874737205)
                ·
                  refine ⟨160227530390291519506613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1709093657496442874737205 160227530390291519506613)
                  ·
                    rfl

theorem cell22_1404189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_1404189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404189 prefixEnd_1404189 := by exact prefixLift 1404189
  have htrace : WordTrace (prefixWord ++ tailWord_1404189) baseStart_1404189 baseEnd_1404189 := by
    simpa [prefixWord, tailWord_1404189, baseEnd_1404189] using wordTrace_append hprefix tailTrace_1404189
  have hstable : (prefixWord ++ tailWord_1404189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404189).length < 2 ^ (prefixWord ++ tailWord_1404189).sum := by decide
  have hdescent : baseEnd_1404189 < baseStart_1404189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404270 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_1404270 : Nat := 118140960795 + 1404270 * 2 ^ 59
def prefixEnd_1404270 : Nat := 4983230072969 + 3 ^ 40 * 1404270 * 2
def baseEnd_1404270 : Nat := 480710319126217347244591

theorem tailTrace_1404270 : CollatzResearch.WordTrace tailWord_1404270 prefixEnd_1404270 480710319126217347244591 := by
  unfold tailWord_1404270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402241827822136883406283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34145289748384730044833509 6402241827822136883406283)
  ·
    refine ⟨9603362741733205325109425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6402241827822136883406283 9603362741733205325109425)
    ·
      refine ⟨7202522056299903993832069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9603362741733205325109425 7202522056299903993832069)
      ·
        refine ⟨1350472885556231998843513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7202522056299903993832069 1350472885556231998843513)
        ·
          refine ⟨1012854664167173999132635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1350472885556231998843513 1012854664167173999132635)
          ·
            refine ⟨1519281996250760998698953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012854664167173999132635 1519281996250760998698953)
            ·
              refine ⟨1139461497188070749024215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1519281996250760998698953 1139461497188070749024215)
              ·
                refine ⟨1709192245782106123536323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139461497188070749024215 1709192245782106123536323)
                ·
                  refine ⟨2563788368673159185304485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709192245782106123536323 2563788368673159185304485)
                  ·
                    refine ⟨480710319126217347244591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2563788368673159185304485 480710319126217347244591)
                    ·
                      rfl

theorem cell22_1404270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_1404270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404270 prefixEnd_1404270 := by exact prefixLift 1404270
  have htrace : WordTrace (prefixWord ++ tailWord_1404270) baseStart_1404270 baseEnd_1404270 := by
    simpa [prefixWord, tailWord_1404270, baseEnd_1404270] using wordTrace_append hprefix tailTrace_1404270
  have hstable : (prefixWord ++ tailWord_1404270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404270).length < 2 ^ (prefixWord ++ tailWord_1404270).sum := by decide
  have hdescent : baseEnd_1404270 < baseStart_1404270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404335 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 8]
def baseStart_1404335 : Nat := 118140960795 + 1404335 * 2 ^ 59
def prefixEnd_1404335 : Nat := 4983230072969 + 3 ^ 40 * 1404335 * 2
def baseEnd_1404335 : Nat := 160244189984859614789797

theorem tailTrace_1404335 : CollatzResearch.WordTrace tailWord_1404335 prefixEnd_1404335 160244189984859614789797 := by
  unfold tailWord_1404335
  simp only [CollatzResearch.WordTrace]
  refine ⟨51220305367341611168366459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34146870244894407445577639 51220305367341611168366459)
  ·
    refine ⟨76830458051012416752549689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51220305367341611168366459 76830458051012416752549689)
    ·
      refine ⟨57622843538259312564412267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76830458051012416752549689 57622843538259312564412267)
      ·
        refine ⟨86434265307388968846618401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57622843538259312564412267 86434265307388968846618401)
        ·
          refine ⟨64825698980541726634963801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86434265307388968846618401 64825698980541726634963801)
          ·
            refine ⟨48619274235406294976222851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64825698980541726634963801 48619274235406294976222851)
            ·
              refine ⟨72928911353109442464334277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48619274235406294976222851 72928911353109442464334277)
              ·
                refine ⟨13674170878708020462062677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72928911353109442464334277 13674170878708020462062677)
                ·
                  refine ⟨160244189984859614789797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13674170878708020462062677 160244189984859614789797)
                  ·
                    rfl

theorem cell22_1404335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 8].length) (baseStart_1404335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404335 prefixEnd_1404335 := by exact prefixLift 1404335
  have htrace : WordTrace (prefixWord ++ tailWord_1404335) baseStart_1404335 baseEnd_1404335 := by
    simpa [prefixWord, tailWord_1404335, baseEnd_1404335] using wordTrace_append hprefix tailTrace_1404335
  have hstable : (prefixWord ++ tailWord_1404335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404335).length < 2 ^ (prefixWord ++ tailWord_1404335).sum := by decide
  have hdescent : baseEnd_1404335 < baseStart_1404335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404352 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 6]
def baseStart_1404352 : Nat := 118140960795 + 1404352 * 2 ^ 59
def prefixEnd_1404352 : Nat := 4983230072969 + 3 ^ 40 * 1404352 * 2
def baseEnd_1404352 : Nat := 160246129800665488898113

theorem tailTrace_1404352 : CollatzResearch.WordTrace tailWord_1404352 prefixEnd_1404352 160246129800665488898113 := by
  unfold tailWord_1404352
  simp only [CollatzResearch.WordTrace]
  refine ⟨25610462704140011535867655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34147283605520015381156873 25610462704140011535867655)
  ·
    refine ⟨38415694056210017303801483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25610462704140011535867655 38415694056210017303801483)
    ·
      refine ⟨57623541084315025955702225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38415694056210017303801483 57623541084315025955702225)
      ·
        refine ⟨43217655813236269466776669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57623541084315025955702225 43217655813236269466776669)
        ·
          refine ⟨16206620929963601050041251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43217655813236269466776669 16206620929963601050041251)
          ·
            refine ⟨24309931394945401575061877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16206620929963601050041251 24309931394945401575061877)
            ·
              refine ⟨2279056068276131397662051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24309931394945401575061877 2279056068276131397662051)
              ·
                refine ⟨3418584102414197096493077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279056068276131397662051 3418584102414197096493077)
                ·
                  refine ⟨160246129800665488898113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3418584102414197096493077 160246129800665488898113)
                  ·
                    rfl

theorem cell22_1404352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_1404352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404352 prefixEnd_1404352 := by exact prefixLift 1404352
  have htrace : WordTrace (prefixWord ++ tailWord_1404352) baseStart_1404352 baseEnd_1404352 := by
    simpa [prefixWord, tailWord_1404352, baseEnd_1404352] using wordTrace_append hprefix tailTrace_1404352
  have hstable : (prefixWord ++ tailWord_1404352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404352).length < 2 ^ (prefixWord ++ tailWord_1404352).sum := by decide
  have hdescent : baseEnd_1404352 < baseStart_1404352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404397 : List Nat := [1, 5, 1, 3, 12]
def baseStart_1404397 : Nat := 118140960795 + 1404397 * 2 ^ 59
def prefixEnd_1404397 : Nat := 4983230072969 + 3 ^ 40 * 1404397 * 2
def baseEnd_1404397 : Nat := 1978410674163091972507

theorem tailTrace_1404397 : CollatzResearch.WordTrace tailWord_1404397 prefixEnd_1404397 1978410674163091972507 := by
  unfold tailWord_1404397
  simp only [CollatzResearch.WordTrace]
  refine ⟨51222566693116995757123445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34148377795411330504748963 51222566693116995757123445)
  ·
    refine ⟨4802115627479718352230323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51222566693116995757123445 4802115627479718352230323)
    ·
      refine ⟨7203173441219577528345485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4802115627479718352230323 7203173441219577528345485)
      ·
        refine ⟨2701190040457341573129557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7203173441219577528345485 2701190040457341573129557)
        ·
          refine ⟨1978410674163091972507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2701190040457341573129557 1978410674163091972507)
          ·
            rfl

theorem cell22_1404397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 12].length) (baseStart_1404397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404397 prefixEnd_1404397 := by exact prefixLift 1404397
  have htrace : WordTrace (prefixWord ++ tailWord_1404397) baseStart_1404397 baseEnd_1404397 := by
    simpa [prefixWord, tailWord_1404397, baseEnd_1404397] using wordTrace_append hprefix tailTrace_1404397
  have hstable : (prefixWord ++ tailWord_1404397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404397).length < 2 ^ (prefixWord ++ tailWord_1404397).sum := by decide
  have hdescent : baseEnd_1404397 < baseStart_1404397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404401 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 2, 3]
def baseStart_1404401 : Nat := 118140960795 + 1404401 * 2 ^ 59
def prefixEnd_1404401 : Nat := 4983230072969 + 3 ^ 40 * 1404401 * 2
def baseEnd_1404401 : Nat := 480755163103376672219189

theorem tailTrace_1404401 : CollatzResearch.WordTrace tailWord_1404401 prefixEnd_1404401 480755163103376672219189 := by
  unfold tailWord_1404401
  simp only [CollatzResearch.WordTrace]
  refine ⟨51222712585102504440269057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34148475056735002960179371 51222712585102504440269057)
  ·
    refine ⟨38417034438826878330201793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51222712585102504440269057 38417034438826878330201793)
    ·
      refine ⟨28812775829120158747651345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38417034438826878330201793 28812775829120158747651345)
      ·
        refine ⟨21609581871840119060738509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28812775829120158747651345 21609581871840119060738509)
        ·
          refine ⟨8103593201940044647776941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21609581871840119060738509 8103593201940044647776941)
          ·
            refine ⟨3038847450727516742916353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8103593201940044647776941 3038847450727516742916353)
            ·
              refine ⟨2279135588045637557187265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038847450727516742916353 2279135588045637557187265)
              ·
                refine ⟨1709351691034228167890449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279135588045637557187265 1709351691034228167890449)
                ·
                  refine ⟨1282013768275671125917837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709351691034228167890449 1282013768275671125917837)
                  ·
                    refine ⟨480755163103376672219189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282013768275671125917837 480755163103376672219189)
                    ·
                      rfl

theorem cell22_1404401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_1404401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404401 prefixEnd_1404401 := by exact prefixLift 1404401
  have htrace : WordTrace (prefixWord ++ tailWord_1404401) baseStart_1404401 baseEnd_1404401 := by
    simpa [prefixWord, tailWord_1404401, baseEnd_1404401] using wordTrace_append hprefix tailTrace_1404401
  have hstable : (prefixWord ++ tailWord_1404401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404401).length < 2 ^ (prefixWord ++ tailWord_1404401).sum := by decide
  have hdescent : baseEnd_1404401 < baseStart_1404401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404418 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1404418 : Nat := 118140960795 + 1404418 * 2 ^ 59
def prefixEnd_1404418 : Nat := 4983230072969 + 3 ^ 40 * 1404418 * 2
def baseEnd_1404418 : Nat := 480760982550794294544137

theorem tailTrace_1404418 : CollatzResearch.WordTrace tailWord_1404418 prefixEnd_1404418 480760982550794294544137 := by
  unfold tailWord_1404418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12805833156510229085909477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34148888417360610895758605 12805833156510229085909477)
  ·
    refine ⟨2401093716845667953608027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12805833156510229085909477 2401093716845667953608027)
    ·
      refine ⟨3601640575268501930412041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2401093716845667953608027 3601640575268501930412041)
      ·
        refine ⟨2701230431451376447809031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3601640575268501930412041 2701230431451376447809031)
        ·
          refine ⟨4051845647177064671713547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701230431451376447809031 4051845647177064671713547)
          ·
            refine ⟨6077768470765597007570321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051845647177064671713547 6077768470765597007570321)
            ·
              refine ⟨4558326353074197755677741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6077768470765597007570321 4558326353074197755677741)
              ·
                refine ⟨1709372382402824158379153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4558326353074197755677741 1709372382402824158379153)
                ·
                  refine ⟨1282029286802118118784365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709372382402824158379153 1282029286802118118784365)
                  ·
                    refine ⟨480760982550794294544137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282029286802118118784365 480760982550794294544137)
                    ·
                      rfl

theorem cell22_1404418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1404418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404418 prefixEnd_1404418 := by exact prefixLift 1404418
  have htrace : WordTrace (prefixWord ++ tailWord_1404418) baseStart_1404418 baseEnd_1404418 := by
    simpa [prefixWord, tailWord_1404418, baseEnd_1404418] using wordTrace_append hprefix tailTrace_1404418
  have hstable : (prefixWord ++ tailWord_1404418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404418).length < 2 ^ (prefixWord ++ tailWord_1404418).sum := by decide
  have hdescent : baseEnd_1404418 < baseStart_1404418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404442 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_1404442 : Nat := 118140960795 + 1404442 * 2 ^ 59
def prefixEnd_1404442 : Nat := 4983230072969 + 3 ^ 40 * 1404442 * 2
def baseEnd_1404442 : Nat := 160256399413755410648021

theorem tailTrace_1404442 : CollatzResearch.WordTrace tailWord_1404442 prefixEnd_1404442 160256399413755410648021 := by
  unfold tailWord_1404442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12806051994488492110627895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34149471985302645628341053 12806051994488492110627895)
  ·
    refine ⟨19209077991732738165941843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12806051994488492110627895 19209077991732738165941843)
    ·
      refine ⟨28813616987599107248912765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19209077991732738165941843 28813616987599107248912765)
      ·
        refine ⟨10805106370349665218342287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28813616987599107248912765 10805106370349665218342287)
        ·
          refine ⟨16207659555524497827513431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10805106370349665218342287 16207659555524497827513431)
          ·
            refine ⟨24311489333286746741270147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16207659555524497827513431 24311489333286746741270147)
            ·
              refine ⟨36467233999930120111905221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24311489333286746741270147 36467233999930120111905221)
              ·
                refine ⟨6837606374986897520982229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36467233999930120111905221 6837606374986897520982229)
                ·
                  refine ⟨160256399413755410648021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6837606374986897520982229 160256399413755410648021)
                  ·
                    rfl

theorem cell22_1404442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_1404442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404442 prefixEnd_1404442 := by exact prefixLift 1404442
  have htrace : WordTrace (prefixWord ++ tailWord_1404442) baseStart_1404442 baseEnd_1404442 := by
    simpa [prefixWord, tailWord_1404442, baseEnd_1404442] using wordTrace_append hprefix tailTrace_1404442
  have hstable : (prefixWord ++ tailWord_1404442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404442).length < 2 ^ (prefixWord ++ tailWord_1404442).sum := by decide
  have hdescent : baseEnd_1404442 < baseStart_1404442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404551 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 2, 4]
def baseStart_1404551 : Nat := 118140960795 + 1404551 * 2 ^ 59
def prefixEnd_1404551 : Nat := 4983230072969 + 3 ^ 40 * 1404551 * 2
def baseEnd_1404551 : Nat := 480806511168826280968729

theorem tailTrace_1404551 : CollatzResearch.WordTrace tailWord_1404551 prefixEnd_1404551 480806511168826280968729 := by
  unfold tailWord_1404551
  simp only [CollatzResearch.WordTrace]
  refine ⟨51228183534559080058229507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34152122356372720038819671 51228183534559080058229507)
  ·
    refine ⟨76842275301838620087344261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51228183534559080058229507 76842275301838620087344261)
    ·
      refine ⟨14407926619094741266377049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76842275301838620087344261 14407926619094741266377049)
      ·
        refine ⟨10805944964321055949782787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14407926619094741266377049 10805944964321055949782787)
        ·
          refine ⟨16208917446481583924674181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10805944964321055949782787 16208917446481583924674181)
          ·
            refine ⟨3039172021215296985876409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16208917446481583924674181 3039172021215296985876409)
            ·
              refine ⟨2279379015911472739407307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039172021215296985876409 2279379015911472739407307)
              ·
                refine ⟨3419068523867209109110961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279379015911472739407307 3419068523867209109110961)
                ·
                  refine ⟨2564301392900406831833221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3419068523867209109110961 2564301392900406831833221)
                  ·
                    refine ⟨480806511168826280968729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2564301392900406831833221 480806511168826280968729)
                    ·
                      rfl

theorem cell22_1404551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_1404551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404551 prefixEnd_1404551 := by exact prefixLift 1404551
  have htrace : WordTrace (prefixWord ++ tailWord_1404551) baseStart_1404551 baseEnd_1404551 := by
    simpa [prefixWord, tailWord_1404551, baseEnd_1404551] using wordTrace_append hprefix tailTrace_1404551
  have hstable : (prefixWord ++ tailWord_1404551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404551).length < 2 ^ (prefixWord ++ tailWord_1404551).sum := by decide
  have hdescent : baseEnd_1404551 < baseStart_1404551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404572 : List Nat := [2, 2, 3, 2, 4, 1, 2, 2, 4]
def baseStart_1404572 : Nat := 118140960795 + 1404572 * 2 ^ 59
def prefixEnd_1404572 : Nat := 4983230072969 + 3 ^ 40 * 1404572 * 2
def baseEnd_1404572 : Nat := 160271233299329742064555

theorem tailTrace_1404572 : CollatzResearch.WordTrace tailWord_1404572 prefixEnd_1404572 160271233299329742064555 := by
  unfold tailWord_1404572
  simp only [CollatzResearch.WordTrace]
  refine ⟨25614474733741500322371985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34152632978322000429829313 25614474733741500322371985)
  ·
    refine ⟨19210856050306125241778989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25614474733741500322371985 19210856050306125241778989)
    ·
      refine ⟨7204071018864796965667121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19210856050306125241778989 7204071018864796965667121)
      ·
        refine ⟨5403053264148597724250341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7204071018864796965667121 5403053264148597724250341)
        ·
          refine ⟨1013072487027862073296939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5403053264148597724250341 1013072487027862073296939)
          ·
            refine ⟨1519608730541793109945409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013072487027862073296939 1519608730541793109945409)
            ·
              refine ⟨1139706547906344832459057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1519608730541793109945409 1139706547906344832459057)
              ·
                refine ⟨854779910929758624344293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139706547906344832459057 854779910929758624344293)
                ·
                  refine ⟨160271233299329742064555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854779910929758624344293 160271233299329742064555)
                  ·
                    rfl

theorem cell22_1404572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_1404572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404572 prefixEnd_1404572 := by exact prefixLift 1404572
  have htrace : WordTrace (prefixWord ++ tailWord_1404572) baseStart_1404572 baseEnd_1404572 := by
    simpa [prefixWord, tailWord_1404572, baseEnd_1404572] using wordTrace_append hprefix tailTrace_1404572
  have hstable : (prefixWord ++ tailWord_1404572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404572).length < 2 ^ (prefixWord ++ tailWord_1404572).sum := by decide
  have hdescent : baseEnd_1404572 < baseStart_1404572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404624 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_1404624 : Nat := 118140960795 + 1404624 * 2 ^ 59
def prefixEnd_1404624 : Nat := 4983230072969 + 3 ^ 40 * 1404624 * 2
def baseEnd_1404624 : Nat := 480831500560678423893505

theorem tailTrace_1404624 : CollatzResearch.WordTrace tailWord_1404624 prefixEnd_1404624 480831500560678423893505 := by
  unfold tailWord_1404624
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615423031647306762818463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34153897375529742350424617 25615423031647306762818463)
  ·
    refine ⟨38423134547470960144227695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25615423031647306762818463 38423134547470960144227695)
    ·
      refine ⟨57634701821206440216341543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38423134547470960144227695 57634701821206440216341543)
      ·
        refine ⟨86452052731809660324512315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57634701821206440216341543 86452052731809660324512315)
        ·
          refine ⟨129678079097714490486768473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86452052731809660324512315 129678079097714490486768473)
          ·
            refine ⟨97258559323285867865076355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129678079097714490486768473 97258559323285867865076355)
            ·
              refine ⟨145887838984928801797614533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97258559323285867865076355 145887838984928801797614533)
              ·
                refine ⟨27353969809674150337052725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145887838984928801797614533 27353969809674150337052725)
                ·
                  refine ⟨2564434669656951594098693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27353969809674150337052725 2564434669656951594098693)
                  ·
                    refine ⟨480831500560678423893505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2564434669656951594098693 480831500560678423893505)
                    ·
                      rfl

theorem cell22_1404624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_1404624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404624 prefixEnd_1404624 := by exact prefixLift 1404624
  have htrace : WordTrace (prefixWord ++ tailWord_1404624) baseStart_1404624 baseEnd_1404624 := by
    simpa [prefixWord, tailWord_1404624, baseEnd_1404624] using wordTrace_append hprefix tailTrace_1404624
  have hstable : (prefixWord ++ tailWord_1404624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404624).length < 2 ^ (prefixWord ++ tailWord_1404624).sum := by decide
  have hdescent : baseEnd_1404624 < baseStart_1404624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404626 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1404626 : Nat := 118140960795 + 1404626 * 2 ^ 59
def prefixEnd_1404626 : Nat := 4983230072969 + 3 ^ 40 * 1404626 * 2
def baseEnd_1404626 : Nat := 480832185201551085343499

theorem tailTrace_1404626 : CollatzResearch.WordTrace tailWord_1404626 prefixEnd_1404626 480832185201551085343499 := by
  unfold tailWord_1404626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12807729752321841966802433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34153946006191578578139821 12807729752321841966802433)
  ·
    refine ⟨9605797314241381475101825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12807729752321841966802433 9605797314241381475101825)
    ·
      refine ⟨7204347985681036106326369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9605797314241381475101825 7204347985681036106326369)
      ·
        refine ⟨5403260989260777079744777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7204347985681036106326369 5403260989260777079744777)
        ·
          refine ⟨4052445741945582809808583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5403260989260777079744777 4052445741945582809808583)
          ·
            refine ⟨6078668612918374214712875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4052445741945582809808583 6078668612918374214712875)
            ·
              refine ⟨9118002919377561322069313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6078668612918374214712875 9118002919377561322069313)
              ·
                refine ⟨6838502189533170991551985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9118002919377561322069313 6838502189533170991551985)
                ·
                  refine ⟨5128876642149878243663989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6838502189533170991551985 5128876642149878243663989)
                  ·
                    refine ⟨480832185201551085343499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5128876642149878243663989 480832185201551085343499)
                    ·
                      rfl

theorem cell22_1404626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1404626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404626 prefixEnd_1404626 := by exact prefixLift 1404626
  have htrace : WordTrace (prefixWord ++ tailWord_1404626) baseStart_1404626 baseEnd_1404626 := by
    simpa [prefixWord, tailWord_1404626, baseEnd_1404626] using wordTrace_append hprefix tailTrace_1404626
  have hstable : (prefixWord ++ tailWord_1404626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404626).length < 2 ^ (prefixWord ++ tailWord_1404626).sum := by decide
  have hdescent : baseEnd_1404626 < baseStart_1404626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404628 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1404628 : Nat := 118140960795 + 1404628 * 2 ^ 59
def prefixEnd_1404628 : Nat := 4983230072969 + 3 ^ 40 * 1404628 * 2
def baseEnd_1404628 : Nat := 160277623280807915597831

theorem tailTrace_1404628 : CollatzResearch.WordTrace tailWord_1404628 prefixEnd_1404628 160277623280807915597831 := by
  unfold tailWord_1404628
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615495977640061104391269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34153994636853414805855025 25615495977640061104391269)
  ·
    refine ⟨4802905495807511457073363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25615495977640061104391269 4802905495807511457073363)
    ·
      refine ⟨7204358243711267185610045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4802905495807511457073363 7204358243711267185610045)
      ·
        refine ⟨2701634341391725194603767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7204358243711267185610045 2701634341391725194603767)
        ·
          refine ⟨4052451512087587791905651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701634341391725194603767 4052451512087587791905651)
          ·
            refine ⟨6078677268131381687858477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4052451512087587791905651 6078677268131381687858477)
            ·
              refine ⟨2279503975549268132946929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6078677268131381687858477 2279503975549268132946929)
              ·
                refine ⟨1709627981661951099710197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279503975549268132946929 1709627981661951099710197)
                ·
                  refine ⟨160277623280807915597831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1709627981661951099710197 160277623280807915597831)
                  ·
                    rfl

theorem cell22_1404628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1404628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404628 prefixEnd_1404628 := by exact prefixLift 1404628
  have htrace : WordTrace (prefixWord ++ tailWord_1404628) baseStart_1404628 baseEnd_1404628 := by
    simpa [prefixWord, tailWord_1404628, baseEnd_1404628] using wordTrace_append hprefix tailTrace_1404628
  have hstable : (prefixWord ++ tailWord_1404628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404628).length < 2 ^ (prefixWord ++ tailWord_1404628).sum := by decide
  have hdescent : baseEnd_1404628 < baseStart_1404628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404658 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_1404658 : Nat := 118140960795 + 1404658 * 2 ^ 59
def prefixEnd_1404658 : Nat := 4983230072969 + 3 ^ 40 * 1404658 * 2
def baseEnd_1404658 : Nat := 480843139455513668543401

theorem tailTrace_1404658 : CollatzResearch.WordTrace tailWord_1404658 prefixEnd_1404658 480843139455513668543401 := by
  unfold tailWord_1404658
  simp only [CollatzResearch.WordTrace]
  refine ⟨12808021536292859333093657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34154724096780958221583085 12808021536292859333093657)
  ·
    refine ⟨9606016152219644499820243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12808021536292859333093657 9606016152219644499820243)
    ·
      refine ⟨14409024228329466749730365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9606016152219644499820243 14409024228329466749730365)
      ·
        refine ⟨5403384085623550031148887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14409024228329466749730365 5403384085623550031148887)
        ·
          refine ⟨8105076128435325046723331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403384085623550031148887 8105076128435325046723331)
          ·
            refine ⟨12157614192652987570084997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8105076128435325046723331 12157614192652987570084997)
            ·
              refine ⟨2279552661122435169390937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12157614192652987570084997 2279552661122435169390937)
              ·
                refine ⟨1709664495841826377043203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279552661122435169390937 1709664495841826377043203)
                ·
                  refine ⟨2564496743762739565564805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709664495841826377043203 2564496743762739565564805)
                  ·
                    refine ⟨480843139455513668543401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2564496743762739565564805 480843139455513668543401)
                    ·
                      rfl

theorem cell22_1404658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_1404658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404658 prefixEnd_1404658 := by exact prefixLift 1404658
  have htrace : WordTrace (prefixWord ++ tailWord_1404658) baseStart_1404658 baseEnd_1404658 := by
    simpa [prefixWord, tailWord_1404658, baseEnd_1404658] using wordTrace_append hprefix tailTrace_1404658
  have hstable : (prefixWord ++ tailWord_1404658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404658).length < 2 ^ (prefixWord ++ tailWord_1404658).sum := by decide
  have hdescent : baseEnd_1404658 < baseStart_1404658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404671 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 4, 3]
def baseStart_1404671 : Nat := 118140960795 + 1404671 * 2 ^ 59
def prefixEnd_1404671 : Nat := 4983230072969 + 3 ^ 40 * 1404671 * 2
def baseEnd_1404671 : Nat := 480847589621185967968361

theorem tailTrace_1404671 : CollatzResearch.WordTrace tailWord_1404671 prefixEnd_1404671 480847589621185967968361 := by
  unfold tailWord_1404671
  simp only [CollatzResearch.WordTrace]
  refine ⟨51232560294124340552597867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34155040196082893701731911 51232560294124340552597867)
  ·
    refine ⟨76848840441186510828896801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51232560294124340552597867 76848840441186510828896801)
    ·
      refine ⟨57636630330889883121672601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76848840441186510828896801 57636630330889883121672601)
      ·
        refine ⟨43227472748167412341254451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57636630330889883121672601 43227472748167412341254451)
        ·
          refine ⟨64841209122251118511881677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43227472748167412341254451 64841209122251118511881677)
          ·
            refine ⟨24315453420844169441955629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64841209122251118511881677 24315453420844169441955629)
            ·
              refine ⟨9118295032816563540733361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24315453420844169441955629 9118295032816563540733361)
              ·
                refine ⟨6838721274612422655550021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9118295032816563540733361 6838721274612422655550021)
                ·
                  refine ⟨1282260238989829247915629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6838721274612422655550021 1282260238989829247915629)
                  ·
                    refine ⟨480847589621185967968361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282260238989829247915629 480847589621185967968361)
                    ·
                      rfl

theorem cell22_1404671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_1404671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404671 prefixEnd_1404671 := by exact prefixLift 1404671
  have htrace : WordTrace (prefixWord ++ tailWord_1404671) baseStart_1404671 baseEnd_1404671 := by
    simpa [prefixWord, tailWord_1404671, baseEnd_1404671] using wordTrace_append hprefix tailTrace_1404671
  have hstable : (prefixWord ++ tailWord_1404671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404671).length < 2 ^ (prefixWord ++ tailWord_1404671).sum := by decide
  have hdescent : baseEnd_1404671 < baseStart_1404671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404673 : List Nat := [1, 2, 4, 1, 1, 1, 5, 3, 4]
def baseStart_1404673 : Nat := 118140960795 + 1404673 * 2 ^ 59
def prefixEnd_1404673 : Nat := 4983230072969 + 3 ^ 40 * 1404673 * 2
def baseEnd_1404673 : Nat := 160282758087352876472785

theorem tailTrace_1404673 : CollatzResearch.WordTrace tailWord_1404673 prefixEnd_1404673 160282758087352876472785 := by
  unfold tailWord_1404673
  simp only [CollatzResearch.WordTrace]
  refine ⟨51232633240117094894170673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34155088826744729929447115 51232633240117094894170673)
  ·
    refine ⟨38424474930087821170628005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51232633240117094894170673 38424474930087821170628005)
    ·
      refine ⟨7204589049391466469492751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38424474930087821170628005 7204589049391466469492751)
      ·
        refine ⟨10806883574087199704239127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204589049391466469492751 10806883574087199704239127)
        ·
          refine ⟨16210325361130799556358691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10806883574087199704239127 16210325361130799556358691)
          ·
            refine ⟨24315488041696199334538037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16210325361130799556358691 24315488041696199334538037)
            ·
              refine ⟨2279577003909018687612941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24315488041696199334538037 2279577003909018687612941)
              ·
                refine ⟨854841376465882007854853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2279577003909018687612941 854841376465882007854853)
                ·
                  refine ⟨160282758087352876472785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854841376465882007854853 160282758087352876472785)
                  ·
                    rfl

theorem cell22_1404673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 4].length) (baseStart_1404673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404673 prefixEnd_1404673 := by exact prefixLift 1404673
  have htrace : WordTrace (prefixWord ++ tailWord_1404673) baseStart_1404673 baseEnd_1404673 := by
    simpa [prefixWord, tailWord_1404673, baseEnd_1404673] using wordTrace_append hprefix tailTrace_1404673
  have hstable : (prefixWord ++ tailWord_1404673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404673).length < 2 ^ (prefixWord ++ tailWord_1404673).sum := by decide
  have hdescent : baseEnd_1404673 < baseStart_1404673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404684 : List Nat := [2, 2, 1, 2, 2, 1, 12]
def baseStart_1404684 : Nat := 118140960795 + 1404684 * 2 ^ 59
def prefixEnd_1404684 : Nat := 4983230072969 + 3 ^ 40 * 1404684 * 2
def baseEnd_1404684 : Nat := 17809334806920676570123

theorem tailTrace_1404684 : CollatzResearch.WordTrace tailWord_1404684 prefixEnd_1404684 17809334806920676570123 := by
  unfold tailWord_1404684
  simp only [CollatzResearch.WordTrace]
  refine ⟨25616517221538621886410553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34155356295384829181880737 25616517221538621886410553)
  ·
    refine ⟨19212387916153966414807915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25616517221538621886410553 19212387916153966414807915)
    ·
      refine ⟨28818581874230949622211873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19212387916153966414807915 28818581874230949622211873)
      ·
        refine ⟨21613936405673212216658905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28818581874230949622211873 21613936405673212216658905)
        ·
          refine ⟨16210452304254909162494179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21613936405673212216658905 16210452304254909162494179)
          ·
            refine ⟨24315678456382363743741269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16210452304254909162494179 24315678456382363743741269)
            ·
              refine ⟨17809334806920676570123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 24315678456382363743741269 17809334806920676570123)
              ·
                rfl

theorem cell22_1404684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 12].length) (baseStart_1404684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404684 prefixEnd_1404684 := by exact prefixLift 1404684
  have htrace : WordTrace (prefixWord ++ tailWord_1404684) baseStart_1404684 baseEnd_1404684 := by
    simpa [prefixWord, tailWord_1404684, baseEnd_1404684] using wordTrace_append hprefix tailTrace_1404684
  have hstable : (prefixWord ++ tailWord_1404684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404684).length < 2 ^ (prefixWord ++ tailWord_1404684).sum := by decide
  have hdescent : baseEnd_1404684 < baseStart_1404684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404686 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1404686 : Nat := 118140960795 + 1404686 * 2 ^ 59
def prefixEnd_1404686 : Nat := 4983230072969 + 3 ^ 40 * 1404686 * 2
def baseEnd_1404686 : Nat := 480852724427730928843315

theorem tailTrace_1404686 : CollatzResearch.WordTrace tailWord_1404686 prefixEnd_1404686 480852724427730928843315 := by
  unfold tailWord_1404686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6404138423633749764299239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34155404926046665409595941 6404138423633749764299239)
  ·
    refine ⟨9606207635450624646448859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6404138423633749764299239 9606207635450624646448859)
    ·
      refine ⟨14409311453175936969673289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9606207635450624646448859 14409311453175936969673289)
      ·
        refine ⟨10806983589881952727254967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14409311453175936969673289 10806983589881952727254967)
        ·
          refine ⟨16210475384822929090882451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10806983589881952727254967 16210475384822929090882451)
          ·
            refine ⟨24315713077234393636323677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16210475384822929090882451 24315713077234393636323677)
            ·
              refine ⟨9118392403962897613621379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24315713077234393636323677 9118392403962897613621379)
              ·
                refine ⟨13677588605944346420432069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9118392403962897613621379 13677588605944346420432069)
                ·
                  refine ⟨2564547863614564953831013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13677588605944346420432069 2564547863614564953831013)
                  ·
                    refine ⟨480852724427730928843315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2564547863614564953831013 480852724427730928843315)
                    ·
                      rfl

theorem cell22_1404686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1404686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404686 prefixEnd_1404686 := by exact prefixLift 1404686
  have htrace : WordTrace (prefixWord ++ tailWord_1404686) baseStart_1404686 baseEnd_1404686 := by
    simpa [prefixWord, tailWord_1404686, baseEnd_1404686] using wordTrace_append hprefix tailTrace_1404686
  have hstable : (prefixWord ++ tailWord_1404686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404686).length < 2 ^ (prefixWord ++ tailWord_1404686).sum := by decide
  have hdescent : baseEnd_1404686 < baseStart_1404686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404690 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_1404690 : Nat := 118140960795 + 1404690 * 2 ^ 59
def prefixEnd_1404690 : Nat := 4983230072969 + 3 ^ 40 * 1404690 * 2
def baseEnd_1404690 : Nat := 160284697903158750581101

theorem tailTrace_1404690 : CollatzResearch.WordTrace tailWord_1404690 prefixEnd_1404690 160284697903158750581101 := by
  unfold tailWord_1404690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12808313320263876699384881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34155502187370337865026349 12808313320263876699384881)
  ·
    refine ⟨9606234990197907524538661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12808313320263876699384881 9606234990197907524538661)
    ·
      refine ⟨1801169060662107660850999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9606234990197907524538661 1801169060662107660850999)
      ·
        refine ⟨2701753590993161491276499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801169060662107660850999 2701753590993161491276499)
        ·
          refine ⟨4052630386489742236914749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701753590993161491276499 4052630386489742236914749)
          ·
            refine ⟨1519736394933653338843031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4052630386489742236914749 1519736394933653338843031)
            ·
              refine ⟨2279604592400480008264547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519736394933653338843031 2279604592400480008264547)
              ·
                refine ⟨3419406888600720012396821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279604592400480008264547 3419406888600720012396821)
                ·
                  refine ⟨160284697903158750581101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3419406888600720012396821 160284697903158750581101)
                  ·
                    rfl

theorem cell22_1404690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_1404690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404690 prefixEnd_1404690 := by exact prefixLift 1404690
  have htrace : WordTrace (prefixWord ++ tailWord_1404690) baseStart_1404690 baseEnd_1404690 := by
    simpa [prefixWord, tailWord_1404690, baseEnd_1404690] using wordTrace_append hprefix tailTrace_1404690
  have hstable : (prefixWord ++ tailWord_1404690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404690).length < 2 ^ (prefixWord ++ tailWord_1404690).sum := by decide
  have hdescent : baseEnd_1404690 < baseStart_1404690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404705 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 2, 3]
def baseStart_1404705 : Nat := 118140960795 + 1404705 * 2 ^ 59
def prefixEnd_1404705 : Nat := 4983230072969 + 3 ^ 40 * 1404705 * 2
def baseEnd_1404705 : Nat := 480859228516021212618257

theorem tailTrace_1404705 : CollatzResearch.WordTrace tailWord_1404705 prefixEnd_1404705 480859228516021212618257 := by
  unfold tailWord_1404705
  simp only [CollatzResearch.WordTrace]
  refine ⟨51233800376001164359335569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34155866917334109572890379 51233800376001164359335569)
  ·
    refine ⟨38425350282000873269501677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51233800376001164359335569 38425350282000873269501677)
    ·
      refine ⟨14409506355750327476063129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38425350282000873269501677 14409506355750327476063129)
      ·
        refine ⟨10807129766812745607047347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14409506355750327476063129 10807129766812745607047347)
        ·
          refine ⟨16210694650219118410571021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10807129766812745607047347 16210694650219118410571021)
          ·
            refine ⟨6079010493832169403964133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16210694650219118410571021 6079010493832169403964133)
            ·
              refine ⟨1139814467593531763243275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6079010493832169403964133 1139814467593531763243275)
              ·
                refine ⟨1709721701390297644864913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139814467593531763243275 1709721701390297644864913)
                ·
                  refine ⟨1282291276042723233648685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709721701390297644864913 1282291276042723233648685)
                  ·
                    refine ⟨480859228516021212618257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282291276042723233648685 480859228516021212618257)
                    ·
                      rfl

theorem cell22_1404705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_1404705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404705 prefixEnd_1404705 := by exact prefixLift 1404705
  have htrace : WordTrace (prefixWord ++ tailWord_1404705) baseStart_1404705 baseEnd_1404705 := by
    simpa [prefixWord, tailWord_1404705, baseEnd_1404705] using wordTrace_append hprefix tailTrace_1404705
  have hstable : (prefixWord ++ tailWord_1404705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404705).length < 2 ^ (prefixWord ++ tailWord_1404705).sum := by decide
  have hdescent : baseEnd_1404705 < baseStart_1404705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404761 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_1404761 : Nat := 118140960795 + 1404761 * 2 ^ 59
def prefixEnd_1404761 : Nat := 4983230072969 + 3 ^ 40 * 1404761 * 2
def baseEnd_1404761 : Nat := 480878398460455733218085

theorem tailTrace_1404761 : CollatzResearch.WordTrace tailWord_1404761 prefixEnd_1404761 480878398460455733218085 := by
  unfold tailWord_1404761
  simp only [CollatzResearch.WordTrace]
  refine ⟨51235842863798285923374137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34157228575865523948916091 51235842863798285923374137)
  ·
    refine ⟨38426882147848714442530603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51235842863798285923374137 38426882147848714442530603)
    ·
      refine ⟨57640323221773071663795905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38426882147848714442530603 57640323221773071663795905)
      ·
        refine ⟨43230242416329803747846929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57640323221773071663795905 43230242416329803747846929)
        ·
          refine ⟨32422681812247352810885197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43230242416329803747846929 32422681812247352810885197)
          ·
            refine ⟨12158505679592757304081949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32422681812247352810885197 12158505679592757304081949)
            ·
              refine ⟨4559439629847283989030731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12158505679592757304081949 4559439629847283989030731)
              ·
                refine ⟨6839159444770925983546097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559439629847283989030731 6839159444770925983546097)
                ·
                  refine ⟨5129369583578194487659573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6839159444770925983546097 5129369583578194487659573)
                  ·
                    refine ⟨480878398460455733218085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5129369583578194487659573 480878398460455733218085)
                    ·
                      rfl

theorem cell22_1404761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_1404761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404761 prefixEnd_1404761 := by exact prefixLift 1404761
  have htrace : WordTrace (prefixWord ++ tailWord_1404761) baseStart_1404761 baseEnd_1404761 := by
    simpa [prefixWord, tailWord_1404761, baseEnd_1404761] using wordTrace_append hprefix tailTrace_1404761
  have hstable : (prefixWord ++ tailWord_1404761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404761).length < 2 ^ (prefixWord ++ tailWord_1404761).sum := by decide
  have hdescent : baseEnd_1404761 < baseStart_1404761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404793 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_1404793 : Nat := 118140960795 + 1404793 * 2 ^ 59
def prefixEnd_1404793 : Nat := 4983230072969 + 3 ^ 40 * 1404793 * 2
def baseEnd_1404793 : Nat := 480889352714418316417987

theorem tailTrace_1404793 : CollatzResearch.WordTrace tailWord_1404793 prefixEnd_1404793 480889352714418316417987 := by
  unfold tailWord_1404793
  simp only [CollatzResearch.WordTrace]
  refine ⟨51237009999682355388539033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34158006666454903592359355 51237009999682355388539033)
  ·
    refine ⟨38427757499761766541404275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51237009999682355388539033 38427757499761766541404275)
    ·
      refine ⟨57641636249642649812106413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38427757499761766541404275 57641636249642649812106413)
      ·
        refine ⟨21615613593615993679539905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57641636249642649812106413 21615613593615993679539905)
        ·
          refine ⟨16211710195211995259654929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21615613593615993679539905 16211710195211995259654929)
          ·
            refine ⟨12158782646408996444741197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16211710195211995259654929 12158782646408996444741197)
            ·
              refine ⟨4559543492403373666777949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12158782646408996444741197 4559543492403373666777949)
              ·
                refine ⟨1709828809651265125041731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4559543492403373666777949 1709828809651265125041731)
                ·
                  refine ⟨2564743214476897687562597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709828809651265125041731 2564743214476897687562597)
                  ·
                    refine ⟨480889352714418316417987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2564743214476897687562597 480889352714418316417987)
                    ·
                      rfl

theorem cell22_1404793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_1404793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404793 prefixEnd_1404793 := by exact prefixLift 1404793
  have htrace : WordTrace (prefixWord ++ tailWord_1404793) baseStart_1404793 baseEnd_1404793 := by
    simpa [prefixWord, tailWord_1404793, baseEnd_1404793] using wordTrace_append hprefix tailTrace_1404793
  have hstable : (prefixWord ++ tailWord_1404793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404793).length < 2 ^ (prefixWord ++ tailWord_1404793).sum := by decide
  have hdescent : baseEnd_1404793 < baseStart_1404793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404821 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1404821 : Nat := 118140960795 + 1404821 * 2 ^ 59
def prefixEnd_1404821 : Nat := 4983230072969 + 3 ^ 40 * 1404821 * 2
def baseEnd_1404821 : Nat := 480898937686635576717901

theorem tailTrace_1404821 : CollatzResearch.WordTrace tailWord_1404821 prefixEnd_1404821 480898937686635576717901 := by
  unfold tailWord_1404821
  simp only [CollatzResearch.WordTrace]
  refine ⟨51238031243580916170558317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34158687495720610780372211 51238031243580916170558317)
  ·
    refine ⟨19214261716342843563959369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51238031243580916170558317 19214261716342843563959369)
    ·
      refine ⟨14410696287257132672969527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19214261716342843563959369 14410696287257132672969527)
      ·
        refine ⟨21616044430885699009454291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14410696287257132672969527 21616044430885699009454291)
        ·
          refine ⟨32424066646328548514181437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21616044430885699009454291 32424066646328548514181437)
          ·
            refine ⟨12159024992373205692818039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32424066646328548514181437 12159024992373205692818039)
            ·
              refine ⟨18238537488559808539227059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12159024992373205692818039 18238537488559808539227059)
              ·
                refine ⟨27357806232839712808840589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18238537488559808539227059 27357806232839712808840589)
                ·
                  refine ⟨10259177337314892303315221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27357806232839712808840589 10259177337314892303315221)
                  ·
                    refine ⟨480898937686635576717901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10259177337314892303315221 480898937686635576717901)
                    ·
                      rfl

theorem cell22_1404821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1404821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404821 prefixEnd_1404821 := by exact prefixLift 1404821
  have htrace : WordTrace (prefixWord ++ tailWord_1404821) baseStart_1404821 baseEnd_1404821 := by
    simpa [prefixWord, tailWord_1404821, baseEnd_1404821] using wordTrace_append hprefix tailTrace_1404821
  have hstable : (prefixWord ++ tailWord_1404821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404821).length < 2 ^ (prefixWord ++ tailWord_1404821).sum := by decide
  have hdescent : baseEnd_1404821 < baseStart_1404821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404823 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 1, 5]
def baseStart_1404823 : Nat := 118140960795 + 1404823 * 2 ^ 59
def prefixEnd_1404823 : Nat := 4983230072969 + 3 ^ 40 * 1404823 * 2
def baseEnd_1404823 : Nat := 480899622327508238167895

theorem tailTrace_1404823 : CollatzResearch.WordTrace tailWord_1404823 prefixEnd_1404823 480899622327508238167895 := by
  unfold tailWord_1404823
  simp only [CollatzResearch.WordTrace]
  refine ⟨51238104189573670512131123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34158736126382447008087415 51238104189573670512131123)
  ·
    refine ⟨76857156284360505768196685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51238104189573670512131123 76857156284360505768196685)
    ·
      refine ⟨28821433606635189663073757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76857156284360505768196685 28821433606635189663073757)
      ·
        refine ⟨10808037602488196123652659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28821433606635189663073757 10808037602488196123652659)
        ·
          refine ⟨16212056403732294185478989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10808037602488196123652659 16212056403732294185478989)
          ·
            refine ⟨6079521151399610319554621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16212056403732294185478989 6079521151399610319554621)
            ·
              refine ⟨2279820431774853869832983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6079521151399610319554621 2279820431774853869832983)
              ·
                refine ⟨3419730647662280804749475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279820431774853869832983 3419730647662280804749475)
                ·
                  refine ⟨5129595971493421207124213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419730647662280804749475 5129595971493421207124213)
                  ·
                    refine ⟨480899622327508238167895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5129595971493421207124213 480899622327508238167895)
                    ·
                      rfl

theorem cell22_1404823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_1404823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404823 prefixEnd_1404823 := by exact prefixLift 1404823
  have htrace : WordTrace (prefixWord ++ tailWord_1404823) baseStart_1404823 baseEnd_1404823 := by
    simpa [prefixWord, tailWord_1404823, baseEnd_1404823] using wordTrace_append hprefix tailTrace_1404823
  have hstable : (prefixWord ++ tailWord_1404823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404823).length < 2 ^ (prefixWord ++ tailWord_1404823).sum := by decide
  have hdescent : baseEnd_1404823 < baseStart_1404823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404853 : List Nat := [1, 3, 3, 2, 1, 4, 8]
def baseStart_1404853 : Nat := 118140960795 + 1404853 * 2 ^ 59
def prefixEnd_1404853 : Nat := 4983230072969 + 3 ^ 40 * 1404853 * 2
def baseEnd_1404853 : Nat := 17811477479281413330289

theorem tailTrace_1404853 : CollatzResearch.WordTrace tailWord_1404853 prefixEnd_1404853 17811477479281413330289 := by
  unfold tailWord_1404853
  simp only [CollatzResearch.WordTrace]
  refine ⟨51239198379464985635723213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34159465586309990423815475 51239198379464985635723213)
  ·
    refine ⟨19214699392299369613396205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51239198379464985635723213 19214699392299369613396205)
    ·
      refine ⟨7205512272112263605023577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19214699392299369613396205 7205512272112263605023577)
      ·
        refine ⟨5404134204084197703767683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7205512272112263605023577 5404134204084197703767683)
        ·
          refine ⟨8106201306126296555651525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404134204084197703767683 8106201306126296555651525)
          ·
            refine ⟨1519912744898680604184661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8106201306126296555651525 1519912744898680604184661)
            ·
              refine ⟨17811477479281413330289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1519912744898680604184661 17811477479281413330289)
              ·
                rfl

theorem cell22_1404853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 8].length) (baseStart_1404853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404853 prefixEnd_1404853 := by exact prefixLift 1404853
  have htrace : WordTrace (prefixWord ++ tailWord_1404853) baseStart_1404853 baseEnd_1404853 := by
    simpa [prefixWord, tailWord_1404853, baseEnd_1404853] using wordTrace_append hprefix tailTrace_1404853
  have hstable : (prefixWord ++ tailWord_1404853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404853).length < 2 ^ (prefixWord ++ tailWord_1404853).sum := by decide
  have hdescent : baseEnd_1404853 < baseStart_1404853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404881 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 9]
def baseStart_1404881 : Nat := 118140960795 + 1404881 * 2 ^ 59
def prefixEnd_1404881 : Nat := 4983230072969 + 3 ^ 40 * 1404881 * 2
def baseEnd_1404881 : Nat := 160306492304271806739239

theorem tailTrace_1404881 : CollatzResearch.WordTrace tailWord_1404881 prefixEnd_1404881 160306492304271806739239 := by
  unfold tailWord_1404881
  simp only [CollatzResearch.WordTrace]
  refine ⟨51240219623363546417742497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34160146415575697611828331 51240219623363546417742497)
  ·
    refine ⟨38430164717522659813306873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51240219623363546417742497 38430164717522659813306873)
    ·
      refine ⟨28822623538141994859980155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38430164717522659813306873 28822623538141994859980155)
      ·
        refine ⟨43233935307212992289970233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28822623538141994859980155 43233935307212992289970233)
        ·
          refine ⟨32425451480409744217477675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43233935307212992289970233 32425451480409744217477675)
          ·
            refine ⟨48638177220614616326216513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32425451480409744217477675 48638177220614616326216513)
            ·
              refine ⟨36478632915460962244662385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48638177220614616326216513 36478632915460962244662385)
              ·
                refine ⟨27358974686595721683496789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36478632915460962244662385 27358974686595721683496789)
                ·
                  refine ⟨160306492304271806739239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27358974686595721683496789 160306492304271806739239)
                  ·
                    rfl

theorem cell22_1404881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_1404881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404881 prefixEnd_1404881 := by exact prefixLift 1404881
  have htrace : WordTrace (prefixWord ++ tailWord_1404881) baseStart_1404881 baseEnd_1404881 := by
    simpa [prefixWord, tailWord_1404881, baseEnd_1404881] using wordTrace_append hprefix tailTrace_1404881
  have hstable : (prefixWord ++ tailWord_1404881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404881).length < 2 ^ (prefixWord ++ tailWord_1404881).sum := by decide
  have hdescent : baseEnd_1404881 < baseStart_1404881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404975 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 2, 3]
def baseStart_1404975 : Nat := 118140960795 + 1404975 * 2 ^ 59
def prefixEnd_1404975 : Nat := 4983230072969 + 3 ^ 40 * 1404975 * 2
def baseEnd_1404975 : Nat := 480951655033830508367429

theorem tailTrace_1404975 : CollatzResearch.WordTrace tailWord_1404975 prefixEnd_1404975 480951655033830508367429 := by
  unfold tailWord_1404975
  simp only [CollatzResearch.WordTrace]
  refine ⟨51243648085023000471664379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34162432056682000314442919 51243648085023000471664379)
  ·
    refine ⟨76865472127534500707496569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51243648085023000471664379 76865472127534500707496569)
    ·
      refine ⟨57649104095650875530622427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76865472127534500707496569 57649104095650875530622427)
      ·
        refine ⟨86473656143476313295933641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57649104095650875530622427 86473656143476313295933641)
        ·
          refine ⟨64855242107607234971950231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86473656143476313295933641 64855242107607234971950231)
          ·
            refine ⟨97282863161410852457925347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64855242107607234971950231 97282863161410852457925347)
            ·
              refine ⟨145924294742116278686888021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97282863161410852457925347 145924294742116278686888021)
              ·
                refine ⟨1710050329009175140861969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 145924294742116278686888021 1710050329009175140861969)
                ·
                  refine ⟨1282537746756881355646477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710050329009175140861969 1282537746756881355646477)
                  ·
                    refine ⟨480951655033830508367429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282537746756881355646477 480951655033830508367429)
                    ·
                      rfl

theorem cell22_1404975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_1404975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404975 prefixEnd_1404975 := by exact prefixLift 1404975
  have htrace : WordTrace (prefixWord ++ tailWord_1404975) baseStart_1404975 baseEnd_1404975 := by
    simpa [prefixWord, tailWord_1404975, baseEnd_1404975] using wordTrace_append hprefix tailTrace_1404975
  have hstable : (prefixWord ++ tailWord_1404975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404975).length < 2 ^ (prefixWord ++ tailWord_1404975).sum := by decide
  have hdescent : baseEnd_1404975 < baseStart_1404975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404988 : List Nat := [2, 2, 2, 2, 2, 1, 2, 9]
def baseStart_1404988 : Nat := 118140960795 + 1404988 * 2 ^ 59
def prefixEnd_1404988 : Nat := 4983230072969 + 3 ^ 40 * 1404988 * 2
def baseEnd_1404988 : Nat := 53439567244389200865821

theorem tailTrace_1404988 : CollatzResearch.WordTrace tailWord_1404988 prefixEnd_1404988 53439567244389200865821 := by
  unfold tailWord_1404988
  simp only [CollatzResearch.WordTrace]
  refine ⟨25622061116987951845943809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34162748155983935794591745 25622061116987951845943809)
  ·
    refine ⟨19216545837740963884457857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25622061116987951845943809 19216545837740963884457857)
    ·
      refine ⟨14412409378305722913343393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19216545837740963884457857 14412409378305722913343393)
      ·
        refine ⟨10809307033729292185007545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14412409378305722913343393 10809307033729292185007545)
        ·
          refine ⟨8106980275296969138755659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10809307033729292185007545 8106980275296969138755659)
          ·
            refine ⟨12160470412945453708133489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8106980275296969138755659 12160470412945453708133489)
            ·
              refine ⟨9120352809709090281100117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12160470412945453708133489 9120352809709090281100117)
              ·
                refine ⟨53439567244389200865821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9120352809709090281100117 53439567244389200865821)
                ·
                  rfl

theorem cell22_1404988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 9].length) (baseStart_1404988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1404988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1404988 prefixEnd_1404988 := by exact prefixLift 1404988
  have htrace : WordTrace (prefixWord ++ tailWord_1404988) baseStart_1404988 baseEnd_1404988 := by
    simpa [prefixWord, tailWord_1404988, baseEnd_1404988] using wordTrace_append hprefix tailTrace_1404988
  have hstable : (prefixWord ++ tailWord_1404988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404988).length < 2 ^ (prefixWord ++ tailWord_1404988).sum := by decide
  have hdescent : baseEnd_1404988 < baseStart_1404988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405005 : List Nat := [1, 6, 1, 1, 1, 1, 3, 8]
def baseStart_1405005 : Nat := 118140960795 + 1405005 * 2 ^ 59
def prefixEnd_1405005 : Nat := 4983230072969 + 3 ^ 40 * 1405005 * 2
def baseEnd_1405005 : Nat := 53440213849657825568593

theorem tailTrace_1405005 : CollatzResearch.WordTrace tailWord_1405005 prefixEnd_1405005 53440213849657825568593 := by
  unfold tailWord_1405005
  simp only [CollatzResearch.WordTrace]
  refine ⟨51244742274914315595256469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34163161516609543730170979 51244742274914315595256469)
  ·
    refine ⟨2402097294136608543527647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51244742274914315595256469 2402097294136608543527647)
    ·
      refine ⟨3603145941204912815291471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402097294136608543527647 3603145941204912815291471)
      ·
        refine ⟨5404718911807369222937207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603145941204912815291471 5404718911807369222937207)
        ·
          refine ⟨8107078367711053834405811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404718911807369222937207 8107078367711053834405811)
          ·
            refine ⟨12160617551566580751608717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107078367711053834405811 12160617551566580751608717)
            ·
              refine ⟨4560231581837467781853269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12160617551566580751608717 4560231581837467781853269)
              ·
                refine ⟨53440213849657825568593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4560231581837467781853269 53440213849657825568593)
                ·
                  rfl

theorem cell22_1405005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 8].length) (baseStart_1405005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405005 prefixEnd_1405005 := by exact prefixLift 1405005
  have htrace : WordTrace (prefixWord ++ tailWord_1405005) baseStart_1405005 baseEnd_1405005 := by
    simpa [prefixWord, tailWord_1405005, baseEnd_1405005] using wordTrace_append hprefix tailTrace_1405005
  have hstable : (prefixWord ++ tailWord_1405005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405005).length < 2 ^ (prefixWord ++ tailWord_1405005).sum := by decide
  have hdescent : baseEnd_1405005 < baseStart_1405005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405033 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 7]
def baseStart_1405033 : Nat := 118140960795 + 1405033 * 2 ^ 59
def prefixEnd_1405033 : Nat := 4983230072969 + 3 ^ 40 * 1405033 * 2
def baseEnd_1405033 : Nat := 160323836539712563472417

theorem tailTrace_1405033 : CollatzResearch.WordTrace tailWord_1405033 prefixEnd_1405033 160323836539712563472417 := by
  unfold tailWord_1405033
  simp only [CollatzResearch.WordTrace]
  refine ⟨51245763518812876377275753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34163842345875250918183835 51245763518812876377275753)
  ·
    refine ⟨38434322639109657282956815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51245763518812876377275753 38434322639109657282956815)
    ·
      refine ⟨57651483958664485924435223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38434322639109657282956815 57651483958664485924435223)
      ·
        refine ⟨86477225937996728886652835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57651483958664485924435223 86477225937996728886652835)
        ·
          refine ⟨129715838906995093329979253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86477225937996728886652835 129715838906995093329979253)
          ·
            refine ⟨12160859897530789999685555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129715838906995093329979253 12160859897530789999685555)
            ·
              refine ⟨18241289846296184999528333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12160859897530789999685555 18241289846296184999528333)
              ·
                refine ⟨6840483692361069374823125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18241289846296184999528333 6840483692361069374823125)
                ·
                  refine ⟨160323836539712563472417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6840483692361069374823125 160323836539712563472417)
                  ·
                    rfl

theorem cell22_1405033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_1405033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405033 prefixEnd_1405033 := by exact prefixLift 1405033
  have htrace : WordTrace (prefixWord ++ tailWord_1405033) baseStart_1405033 baseEnd_1405033 := by
    simpa [prefixWord, tailWord_1405033, baseEnd_1405033] using wordTrace_append hprefix tailTrace_1405033
  have hstable : (prefixWord ++ tailWord_1405033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405033).length < 2 ^ (prefixWord ++ tailWord_1405033).sum := by decide
  have hdescent : baseEnd_1405033 < baseStart_1405033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405048 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_1405048 : Nat := 118140960795 + 1405048 * 2 ^ 59
def prefixEnd_1405048 : Nat := 4983230072969 + 3 ^ 40 * 1405048 * 2
def baseEnd_1405048 : Nat := 480976644425682651292205

theorem tailTrace_1405048 : CollatzResearch.WordTrace tailWord_1405048 prefixEnd_1405048 480976644425682651292205 := by
  unfold tailWord_1405048
  simp only [CollatzResearch.WordTrace]
  refine ⟨25623155306879266969535899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34164207075839022626047865 25623155306879266969535899)
  ·
    refine ⟨38434732960318900454303849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25623155306879266969535899 38434732960318900454303849)
    ·
      refine ⟨28826049720239175340727887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38434732960318900454303849 28826049720239175340727887)
      ·
        refine ⟨43239074580358763011091831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28826049720239175340727887 43239074580358763011091831)
        ·
          refine ⟨64858611870538144516637747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43239074580358763011091831 64858611870538144516637747)
          ·
            refine ⟨97287917805807216774956621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64858611870538144516637747 97287917805807216774956621)
            ·
              refine ⟨36482969177177706290608733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97287917805807216774956621 36482969177177706290608733)
              ·
                refine ⟨13681113441441639858978275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36482969177177706290608733 13681113441441639858978275)
                ·
                  refine ⟨20521670162162459788467413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13681113441441639858978275 20521670162162459788467413)
                  ·
                    refine ⟨480976644425682651292205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20521670162162459788467413 480976644425682651292205)
                    ·
                      rfl

theorem cell22_1405048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_1405048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405048 prefixEnd_1405048 := by exact prefixLift 1405048
  have htrace : WordTrace (prefixWord ++ tailWord_1405048) baseStart_1405048 baseEnd_1405048 := by
    simpa [prefixWord, tailWord_1405048, baseEnd_1405048] using wordTrace_append hprefix tailTrace_1405048
  have hstable : (prefixWord ++ tailWord_1405048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405048).length < 2 ^ (prefixWord ++ tailWord_1405048).sum := by decide
  have hdescent : baseEnd_1405048 < baseStart_1405048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405144 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 2, 3]
def baseStart_1405144 : Nat := 118140960795 + 1405144 * 2 ^ 59
def prefixEnd_1405144 : Nat := 4983230072969 + 3 ^ 40 * 1405144 * 2
def baseEnd_1405144 : Nat := 481009507187570400891911

theorem tailTrace_1405144 : CollatzResearch.WordTrace tailWord_1405144 prefixEnd_1405144 481009507187570400891911 := by
  unfold tailWord_1405144
  simp only [CollatzResearch.WordTrace]
  refine ⟨25624906010705371167283243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34166541347607161556377657 25624906010705371167283243)
  ·
    refine ⟨38437359016058056750924865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25624906010705371167283243 38437359016058056750924865)
    ·
      refine ⟨28828019262043542563193649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38437359016058056750924865 28828019262043542563193649)
      ·
        refine ⟨21621014446532656922395237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28828019262043542563193649 21621014446532656922395237)
        ·
          refine ⟨4053940208724873172949107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21621014446532656922395237 4053940208724873172949107)
          ·
            refine ⟨6080910313087309759423661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053940208724873172949107 6080910313087309759423661)
            ·
              refine ⟨2280341367407741159783873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6080910313087309759423661 2280341367407741159783873)
              ·
                refine ⟨1710256025555805869837905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280341367407741159783873 1710256025555805869837905)
                ·
                  refine ⟨1282692019166854402378429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710256025555805869837905 1282692019166854402378429)
                  ·
                    refine ⟨481009507187570400891911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282692019166854402378429 481009507187570400891911)
                    ·
                      rfl

theorem cell22_1405144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_1405144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405144 prefixEnd_1405144 := by exact prefixLift 1405144
  have htrace : WordTrace (prefixWord ++ tailWord_1405144) baseStart_1405144 baseEnd_1405144 := by
    simpa [prefixWord, tailWord_1405144, baseEnd_1405144] using wordTrace_append hprefix tailTrace_1405144
  have hstable : (prefixWord ++ tailWord_1405144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405144).length < 2 ^ (prefixWord ++ tailWord_1405144).sum := by decide
  have hdescent : baseEnd_1405144 < baseStart_1405144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405185 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 9]
def baseStart_1405185 : Nat := 118140960795 + 1405185 * 2 ^ 59
def prefixEnd_1405185 : Nat := 4983230072969 + 3 ^ 40 * 1405185 * 2
def baseEnd_1405185 : Nat := 160341180775153320205595

theorem tailTrace_1405185 : CollatzResearch.WordTrace tailWord_1405185 prefixEnd_1405185 160341180775153320205595 := by
  unfold tailWord_1405185
  simp only [CollatzResearch.WordTrace]
  refine ⟨51251307414262206336809009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34167538276174804224539339 51251307414262206336809009)
  ·
    refine ⟨38438480560696654752606757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51251307414262206336809009 38438480560696654752606757)
    ·
      refine ⟨7207215105130622766113767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38438480560696654752606757 7207215105130622766113767)
      ·
        refine ⟨10810822657695934149170651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7207215105130622766113767 10810822657695934149170651)
        ·
          refine ⟨16216233986543901223755977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10810822657695934149170651 16216233986543901223755977)
          ·
            refine ⟨12162175489907925917816983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16216233986543901223755977 12162175489907925917816983)
            ·
              refine ⟨18243263234861888876725475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12162175489907925917816983 18243263234861888876725475)
              ·
                refine ⟨27364894852292833315088213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18243263234861888876725475 27364894852292833315088213)
                ·
                  refine ⟨160341180775153320205595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27364894852292833315088213 160341180775153320205595)
                  ·
                    rfl

theorem cell22_1405185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_1405185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405185 prefixEnd_1405185 := by exact prefixLift 1405185
  have htrace : WordTrace (prefixWord ++ tailWord_1405185) baseStart_1405185 baseEnd_1405185 := by
    simpa [prefixWord, tailWord_1405185, baseEnd_1405185] using wordTrace_append hprefix tailTrace_1405185
  have hstable : (prefixWord ++ tailWord_1405185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405185).length < 2 ^ (prefixWord ++ tailWord_1405185).sum := by decide
  have hdescent : baseEnd_1405185 < baseStart_1405185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405189 : List Nat := [1, 3, 1, 1, 2, 1, 2, 7, 1, 3]
def baseStart_1405189 : Nat := 118140960795 + 1405189 * 2 ^ 59
def prefixEnd_1405189 : Nat := 4983230072969 + 3 ^ 40 * 1405189 * 2
def baseEnd_1405189 : Nat := 481024911607205283516773

theorem tailTrace_1405189 : CollatzResearch.WordTrace tailWord_1405189 prefixEnd_1405189 481024911607205283516773 := by
  unfold tailWord_1405189
  simp only [CollatzResearch.WordTrace]
  refine ⟨51251453306247715019954621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34167635537498476679969747 51251453306247715019954621)
  ·
    refine ⟨19219294989842893132482983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51251453306247715019954621 19219294989842893132482983)
    ·
      refine ⟨28828942484764339698724475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19219294989842893132482983 28828942484764339698724475)
      ·
        refine ⟨43243413727146509548086713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28828942484764339698724475 43243413727146509548086713)
        ·
          refine ⟨32432560295359882161065035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43243413727146509548086713 32432560295359882161065035)
          ·
            refine ⟨48648840443039823241597553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32432560295359882161065035 48648840443039823241597553)
            ·
              refine ⟨36486630332279867431198165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48648840443039823241597553 36486630332279867431198165)
              ·
                refine ⟨855155398412809392918707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36486630332279867431198165 855155398412809392918707)
                ·
                  refine ⟨1282733097619214089378061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855155398412809392918707 1282733097619214089378061)
                  ·
                    refine ⟨481024911607205283516773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282733097619214089378061 481024911607205283516773)
                    ·
                      rfl

theorem cell22_1405189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_1405189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405189 prefixEnd_1405189 := by exact prefixLift 1405189
  have htrace : WordTrace (prefixWord ++ tailWord_1405189) baseStart_1405189 baseEnd_1405189 := by
    simpa [prefixWord, tailWord_1405189, baseEnd_1405189] using wordTrace_append hprefix tailTrace_1405189
  have hstable : (prefixWord ++ tailWord_1405189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405189).length < 2 ^ (prefixWord ++ tailWord_1405189).sum := by decide
  have hdescent : baseEnd_1405189 < baseStart_1405189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405232 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_1405232 : Nat := 118140960795 + 1405232 * 2 ^ 59
def prefixEnd_1405232 : Nat := 4983230072969 + 3 ^ 40 * 1405232 * 2
def baseEnd_1405232 : Nat := 481039631385967504691641

theorem tailTrace_1405232 : CollatzResearch.WordTrace tailWord_1405232 prefixEnd_1405232 481039631385967504691641 := by
  unfold tailWord_1405232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626510822545966681884975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34168681096727955575846633 25626510822545966681884975)
  ·
    refine ⟨38439766233818950022827463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25626510822545966681884975 38439766233818950022827463)
    ·
      refine ⟨57659649350728425034241195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38439766233818950022827463 57659649350728425034241195)
      ·
        refine ⟨86489474026092637551361793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57659649350728425034241195 86489474026092637551361793)
        ·
          refine ⟨64867105519569478163521345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86489474026092637551361793 64867105519569478163521345)
          ·
            refine ⟨48650329139677108622641009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64867105519569478163521345 48650329139677108622641009)
            ·
              refine ⟨36487746854757831466980757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48650329139677108622641009 36487746854757831466980757)
              ·
                refine ⟨1710363133816773350014723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36487746854757831466980757 1710363133816773350014723)
                ·
                  refine ⟨2565544700725160025022085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710363133816773350014723 2565544700725160025022085)
                  ·
                    refine ⟨481039631385967504691641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2565544700725160025022085 481039631385967504691641)
                    ·
                      rfl

theorem cell22_1405232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_1405232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405232 prefixEnd_1405232 := by exact prefixLift 1405232
  have htrace : WordTrace (prefixWord ++ tailWord_1405232) baseStart_1405232 baseEnd_1405232 := by
    simpa [prefixWord, tailWord_1405232, baseEnd_1405232] using wordTrace_append hprefix tailTrace_1405232
  have hstable : (prefixWord ++ tailWord_1405232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405232).length < 2 ^ (prefixWord ++ tailWord_1405232).sum := by decide
  have hdescent : baseEnd_1405232 < baseStart_1405232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405264 : List Nat := [2, 1, 1, 1, 1, 7, 1, 4, 4]
def baseStart_1405264 : Nat := 118140960795 + 1405264 * 2 ^ 59
def prefixEnd_1405264 : Nat := 4983230072969 + 3 ^ 40 * 1405264 * 2
def baseEnd_1405264 : Nat := 160350195213310029297181

theorem tailTrace_1405264 : CollatzResearch.WordTrace tailWord_1405264 prefixEnd_1405264 160350195213310029297181 := by
  unfold tailWord_1405264
  simp only [CollatzResearch.WordTrace]
  refine ⟨25627094390488001414467423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34169459187317335219289897 25627094390488001414467423)
  ·
    refine ⟨38440641585732002121701135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25627094390488001414467423 38440641585732002121701135)
    ·
      refine ⟨57660962378598003182551703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38440641585732002121701135 57660962378598003182551703)
      ·
        refine ⟨86491443567897004773827555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57660962378598003182551703 86491443567897004773827555)
        ·
          refine ⟨129737165351845507160741333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86491443567897004773827555 129737165351845507160741333)
          ·
            refine ⟨3040714812933879074079875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 129737165351845507160741333 3040714812933879074079875)
            ·
              refine ⟨4561072219400818611119813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040714812933879074079875 4561072219400818611119813)
              ·
                refine ⟨855201041137653489584965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4561072219400818611119813 855201041137653489584965)
                ·
                  refine ⟨160350195213310029297181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 855201041137653489584965 160350195213310029297181)
                  ·
                    rfl

theorem cell22_1405264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 4].length) (baseStart_1405264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405264 prefixEnd_1405264 := by exact prefixLift 1405264
  have htrace : WordTrace (prefixWord ++ tailWord_1405264) baseStart_1405264 baseEnd_1405264 := by
    simpa [prefixWord, tailWord_1405264, baseEnd_1405264] using wordTrace_append hprefix tailTrace_1405264
  have hstable : (prefixWord ++ tailWord_1405264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405264).length < 2 ^ (prefixWord ++ tailWord_1405264).sum := by decide
  have hdescent : baseEnd_1405264 < baseStart_1405264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405279 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 2, 3]
def baseStart_1405279 : Nat := 118140960795 + 1405279 * 2 ^ 59
def prefixEnd_1405279 : Nat := 4983230072969 + 3 ^ 40 * 1405279 * 2
def baseEnd_1405279 : Nat := 481055720446475048766497

theorem tailTrace_1405279 : CollatzResearch.WordTrace tailWord_1405279 prefixEnd_1405279 481055720446475048766497 := by
  unfold tailWord_1405279
  simp only [CollatzResearch.WordTrace]
  refine ⟨51254735875921660390730891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34169823917281106927153927 51254735875921660390730891)
  ·
    refine ⟨76882103813882490586096337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51254735875921660390730891 76882103813882490586096337)
    ·
      refine ⟨57661577860411867939572253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76882103813882490586096337 57661577860411867939572253)
      ·
        refine ⟨21623091697654450477339595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57661577860411867939572253 21623091697654450477339595)
        ·
          refine ⟨32434637546481675716009393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21623091697654450477339595 32434637546481675716009393)
          ·
            refine ⟨24325978159861256787007045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32434637546481675716009393 24325978159861256787007045)
            ·
              refine ⟨4561120904973985647563821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24325978159861256787007045 4561120904973985647563821)
              ·
                refine ⟨1710420339365244617836433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4561120904973985647563821 1710420339365244617836433)
                ·
                  refine ⟨1282815254523933463377325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710420339365244617836433 1282815254523933463377325)
                  ·
                    refine ⟨481055720446475048766497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282815254523933463377325 481055720446475048766497)
                    ·
                      rfl

theorem cell22_1405279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_1405279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405279 prefixEnd_1405279 := by exact prefixLift 1405279
  have htrace : WordTrace (prefixWord ++ tailWord_1405279) baseStart_1405279 baseEnd_1405279 := by
    simpa [prefixWord, tailWord_1405279, baseEnd_1405279] using wordTrace_append hprefix tailTrace_1405279
  have hstable : (prefixWord ++ tailWord_1405279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405279).length < 2 ^ (prefixWord ++ tailWord_1405279).sum := by decide
  have hdescent : baseEnd_1405279 < baseStart_1405279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405313 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 2, 3]
def baseStart_1405313 : Nat := 118140960795 + 1405313 * 2 ^ 59
def prefixEnd_1405313 : Nat := 4983230072969 + 3 ^ 40 * 1405313 * 2
def baseEnd_1405313 : Nat := 481067359341310293416393

theorem tailTrace_1405313 : CollatzResearch.WordTrace tailWord_1405313 prefixEnd_1405313 481067359341310293416393 := by
  unfold tailWord_1405313
  simp only [CollatzResearch.WordTrace]
  refine ⟨51255975957798484197468593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34170650638532322798312395 51255975957798484197468593)
  ·
    refine ⟨38441981968348863148101445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51255975957798484197468593 38441981968348863148101445)
    ·
      refine ⟨7207871619065411840269021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38441981968348863148101445 7207871619065411840269021)
      ·
        refine ⟨2702951857149529440100883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7207871619065411840269021 2702951857149529440100883)
        ·
          refine ⟨4054427785724294160151325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702951857149529440100883 4054427785724294160151325)
          ·
            refine ⟨1520410419646610310056747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4054427785724294160151325 1520410419646610310056747)
            ·
              refine ⟨2280615629469915465085121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520410419646610310056747 2280615629469915465085121)
              ·
                refine ⟨1710461722102436598813841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280615629469915465085121 1710461722102436598813841)
                ·
                  refine ⟨1282846291576827449110381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710461722102436598813841 1282846291576827449110381)
                  ·
                    refine ⟨481067359341310293416393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282846291576827449110381 481067359341310293416393)
                    ·
                      rfl

theorem cell22_1405313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_1405313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405313 prefixEnd_1405313 := by exact prefixLift 1405313
  have htrace : WordTrace (prefixWord ++ tailWord_1405313) baseStart_1405313 baseEnd_1405313 := by
    simpa [prefixWord, tailWord_1405313, baseEnd_1405313] using wordTrace_append hprefix tailTrace_1405313
  have hstable : (prefixWord ++ tailWord_1405313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405313).length < 2 ^ (prefixWord ++ tailWord_1405313).sum := by decide
  have hdescent : baseEnd_1405313 < baseStart_1405313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405324 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_1405324 : Nat := 118140960795 + 1405324 * 2 ^ 59
def prefixEnd_1405324 : Nat := 4983230072969 + 3 ^ 40 * 1405324 * 2
def baseEnd_1405324 : Nat := 481071124866109931391359

theorem tailTrace_1405324 : CollatzResearch.WordTrace tailWord_1405324 prefixEnd_1405324 481071124866109931391359 := by
  unfold tailWord_1405324
  simp only [CollatzResearch.WordTrace]
  refine ⟨25628188580379316538059513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34170918107172422050746017 25628188580379316538059513)
  ·
    refine ⟨19221141435284487403544635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25628188580379316538059513 19221141435284487403544635)
    ·
      refine ⟨28831712152926731105316953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19221141435284487403544635 28831712152926731105316953)
      ·
        refine ⟨21623784114695048328987715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28831712152926731105316953 21623784114695048328987715)
        ·
          refine ⟨32435676172042572493481573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21623784114695048328987715 32435676172042572493481573)
          ·
            refine ⟨6081689282257982342527795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32435676172042572493481573 6081689282257982342527795)
            ·
              refine ⟨9122533923386973513791693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6081689282257982342527795 9122533923386973513791693)
              ·
                refine ⟨3420950221270115067671885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9122533923386973513791693 3420950221270115067671885)
                ·
                  refine ⟨1282856332976293150376957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3420950221270115067671885 1282856332976293150376957)
                  ·
                    refine ⟨481071124866109931391359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282856332976293150376957 481071124866109931391359)
                    ·
                      rfl

theorem cell22_1405324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_1405324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405324 prefixEnd_1405324 := by exact prefixLift 1405324
  have htrace : WordTrace (prefixWord ++ tailWord_1405324) baseStart_1405324 baseEnd_1405324 := by
    simpa [prefixWord, tailWord_1405324, baseEnd_1405324] using wordTrace_append hprefix tailTrace_1405324
  have hstable : (prefixWord ++ tailWord_1405324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405324).length < 2 ^ (prefixWord ++ tailWord_1405324).sum := by decide
  have hdescent : baseEnd_1405324 < baseStart_1405324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405388 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 5]
def baseStart_1405388 : Nat := 118140960795 + 1405388 * 2 ^ 59
def prefixEnd_1405388 : Nat := 4983230072969 + 3 ^ 40 * 1405388 * 2
def baseEnd_1405388 : Nat := 160364344458011699263721

theorem tailTrace_1405388 : CollatzResearch.WordTrace tailWord_1405388 prefixEnd_1405388 160364344458011699263721 := by
  unfold tailWord_1405388
  simp only [CollatzResearch.WordTrace]
  refine ⟨25629355716263386003224409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34172474288351181337632545 25629355716263386003224409)
  ·
    refine ⟨19222016787197539502418307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25629355716263386003224409 19222016787197539502418307)
    ·
      refine ⟨28833025180796309253627461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19222016787197539502418307 28833025180796309253627461)
      ·
        refine ⟨5406192221399307985055149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28833025180796309253627461 5406192221399307985055149)
        ·
          refine ⟨2027322083024740494395681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5406192221399307985055149 2027322083024740494395681)
          ·
            refine ⟨1520491562268555370796761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2027322083024740494395681 1520491562268555370796761)
            ·
              refine ⟨1140368671701416528097571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520491562268555370796761 1140368671701416528097571)
              ·
                refine ⟨1710553007552124792146357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140368671701416528097571 1710553007552124792146357)
                ·
                  refine ⟨160364344458011699263721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1710553007552124792146357 160364344458011699263721)
                  ·
                    rfl

theorem cell22_1405388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_1405388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405388 prefixEnd_1405388 := by exact prefixLift 1405388
  have htrace : WordTrace (prefixWord ++ tailWord_1405388) baseStart_1405388 baseEnd_1405388 := by
    simpa [prefixWord, tailWord_1405388, baseEnd_1405388] using wordTrace_append hprefix tailTrace_1405388
  have hstable : (prefixWord ++ tailWord_1405388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405388).length < 2 ^ (prefixWord ++ tailWord_1405388).sum := by decide
  have hdescent : baseEnd_1405388 < baseStart_1405388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405418 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 1, 4]
def baseStart_1405418 : Nat := 118140960795 + 1405418 * 2 ^ 59
def prefixEnd_1405418 : Nat := 4983230072969 + 3 ^ 40 * 1405418 * 2
def baseEnd_1405418 : Nat := 481103302987125019541071

theorem tailTrace_1405418 : CollatzResearch.WordTrace tailWord_1405418 prefixEnd_1405418 481103302987125019541071 := by
  unfold tailWord_1405418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12814951405604521782510227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34173203748278724753360605 12814951405604521782510227)
  ·
    refine ⟨19222427108406782673765341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12814951405604521782510227 19222427108406782673765341)
    ·
      refine ⟨7208410165652543502662003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19222427108406782673765341 7208410165652543502662003)
      ·
        refine ⟨10812615248478815253993005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7208410165652543502662003 10812615248478815253993005)
        ·
          refine ⟨4054730718179555720247377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10812615248478815253993005 4054730718179555720247377)
          ·
            refine ⟨3041048038634666790185533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4054730718179555720247377 3041048038634666790185533)
            ·
              refine ⟨1140393014488000046319575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3041048038634666790185533 1140393014488000046319575)
              ·
                refine ⟨1710589521732000069479363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140393014488000046319575 1710589521732000069479363)
                ·
                  refine ⟨2565884282598000104219045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710589521732000069479363 2565884282598000104219045)
                  ·
                    refine ⟨481103302987125019541071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2565884282598000104219045 481103302987125019541071)
                    ·
                      rfl

theorem cell22_1405418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_1405418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405418 prefixEnd_1405418 := by exact prefixLift 1405418
  have htrace : WordTrace (prefixWord ++ tailWord_1405418) baseStart_1405418 baseEnd_1405418 := by
    simpa [prefixWord, tailWord_1405418, baseEnd_1405418] using wordTrace_append hprefix tailTrace_1405418
  have hstable : (prefixWord ++ tailWord_1405418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405418).length < 2 ^ (prefixWord ++ tailWord_1405418).sum := by decide
  have hdescent : baseEnd_1405418 < baseStart_1405418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405493 : List Nat := [1, 3, 3, 1, 1, 2, 1, 6, 1, 3]
def baseStart_1405493 : Nat := 118140960795 + 1405493 * 2 ^ 59
def prefixEnd_1405493 : Nat := 4983230072969 + 3 ^ 40 * 1405493 * 2
def baseEnd_1405493 : Nat := 481128977019849823915841

theorem tailTrace_1405493 : CollatzResearch.WordTrace tailWord_1405493 prefixEnd_1405493 481128977019849823915841 := by
  unfold tailWord_1405493
  simp only [CollatzResearch.WordTrace]
  refine ⟨51262541097146374939021133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34175027398097583292680755 51262541097146374939021133)
  ·
    refine ⟨19223452911429890602132925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51262541097146374939021133 19223452911429890602132925)
    ·
      refine ⟨7208794841786208975799847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19223452911429890602132925 7208794841786208975799847)
      ·
        refine ⟨10813192262679313463699771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7208794841786208975799847 10813192262679313463699771)
        ·
          refine ⟨16219788394018970195549657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10813192262679313463699771 16219788394018970195549657)
          ·
            refine ⟨12164841295514227646662243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16219788394018970195549657 12164841295514227646662243)
            ·
              refine ⟨18247261943271341469993365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12164841295514227646662243 18247261943271341469993365)
              ·
                refine ⟨855340403590844131405939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18247261943271341469993365 855340403590844131405939)
                ·
                  refine ⟨1283010605386266197108909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855340403590844131405939 1283010605386266197108909)
                  ·
                    refine ⟨481128977019849823915841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283010605386266197108909 481128977019849823915841)
                    ·
                      rfl

theorem cell22_1405493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_1405493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405493 prefixEnd_1405493 := by exact prefixLift 1405493
  have htrace : WordTrace (prefixWord ++ tailWord_1405493) baseStart_1405493 baseEnd_1405493 := by
    simpa [prefixWord, tailWord_1405493, baseEnd_1405493] using wordTrace_append hprefix tailTrace_1405493
  have hstable : (prefixWord ++ tailWord_1405493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405493).length < 2 ^ (prefixWord ++ tailWord_1405493).sum := by decide
  have hdescent : baseEnd_1405493 < baseStart_1405493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405504 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_1405504 : Nat := 118140960795 + 1405504 * 2 ^ 59
def prefixEnd_1405504 : Nat := 4983230072969 + 3 ^ 40 * 1405504 * 2
def baseEnd_1405504 : Nat := 481132742544649461890807

theorem tailTrace_1405504 : CollatzResearch.WordTrace tailWord_1405504 prefixEnd_1405504 481132742544649461890807 := by
  unfold tailWord_1405504
  simp only [CollatzResearch.WordTrace]
  refine ⟨25631471150053261908835783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34175294866737682545114377 25631471150053261908835783)
  ·
    refine ⟨38447206725079892863253675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25631471150053261908835783 38447206725079892863253675)
    ·
      refine ⟨57670810087619839294880513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38447206725079892863253675 57670810087619839294880513)
      ·
        refine ⟨43253107565714879471160385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57670810087619839294880513 43253107565714879471160385)
        ·
          refine ⟨32439830674286159603370289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43253107565714879471160385 32439830674286159603370289)
          ·
            refine ⟨24329873005714619702527717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32439830674286159603370289 24329873005714619702527717)
            ·
              refine ⟨4561851188571491194223947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24329873005714619702527717 4561851188571491194223947)
              ·
                refine ⟨6842776782857236791335921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561851188571491194223947 6842776782857236791335921)
                ·
                  refine ⟨5132082587142927593501941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6842776782857236791335921 5132082587142927593501941)
                  ·
                    refine ⟨481132742544649461890807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5132082587142927593501941 481132742544649461890807)
                    ·
                      rfl

theorem cell22_1405504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_1405504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405504 prefixEnd_1405504 := by exact prefixLift 1405504
  have htrace : WordTrace (prefixWord ++ tailWord_1405504) baseStart_1405504 baseEnd_1405504 := by
    simpa [prefixWord, tailWord_1405504, baseEnd_1405504] using wordTrace_append hprefix tailTrace_1405504
  have hstable : (prefixWord ++ tailWord_1405504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405504).length < 2 ^ (prefixWord ++ tailWord_1405504).sum := by decide
  have hdescent : baseEnd_1405504 < baseStart_1405504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405510 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1405510 : Nat := 118140960795 + 1405510 * 2 ^ 59
def prefixEnd_1405510 : Nat := 4983230072969 + 3 ^ 40 * 1405510 * 2
def baseEnd_1405510 : Nat := 481134796467267446240789

theorem tailTrace_1405510 : CollatzResearch.WordTrace tailWord_1405510 prefixEnd_1405510 481134796467267446240789 := by
  unfold tailWord_1405510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601973785565149588824687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34175440758723191228259989 1601973785565149588824687)
  ·
    refine ⟨2402960678347724383237031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1601973785565149588824687 2402960678347724383237031)
    ·
      refine ⟨3604441017521586574855547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402960678347724383237031 3604441017521586574855547)
      ·
        refine ⟨5406661526282379862283321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604441017521586574855547 5406661526282379862283321)
        ·
          refine ⟨4054996144711784896712491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5406661526282379862283321 4054996144711784896712491)
          ·
            refine ⟨6082494217067677345068737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054996144711784896712491 6082494217067677345068737)
            ·
              refine ⟨4561870662800758008801553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6082494217067677345068737 4561870662800758008801553)
              ·
                refine ⟨3421402997100568506601165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4561870662800758008801553 3421402997100568506601165)
                ·
                  refine ⟨1283026123912713189975437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3421402997100568506601165 1283026123912713189975437)
                  ·
                    refine ⟨481134796467267446240789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283026123912713189975437 481134796467267446240789)
                    ·
                      rfl

theorem cell22_1405510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1405510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405510 prefixEnd_1405510 := by exact prefixLift 1405510
  have htrace : WordTrace (prefixWord ++ tailWord_1405510) baseStart_1405510 baseEnd_1405510 := by
    simpa [prefixWord, tailWord_1405510, baseEnd_1405510] using wordTrace_append hprefix tailTrace_1405510
  have hstable : (prefixWord ++ tailWord_1405510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405510).length < 2 ^ (prefixWord ++ tailWord_1405510).sum := by decide
  have hdescent : baseEnd_1405510 < baseStart_1405510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405519 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 3, 4]
def baseStart_1405519 : Nat := 118140960795 + 1405519 * 2 ^ 59
def prefixEnd_1405519 : Nat := 4983230072969 + 3 ^ 40 * 1405519 * 2
def baseEnd_1405519 : Nat := 481137877351194422765761

theorem tailTrace_1405519 : CollatzResearch.WordTrace tailWord_1405519 prefixEnd_1405519 481137877351194422765761 := by
  unfold tailWord_1405519
  simp only [CollatzResearch.WordTrace]
  refine ⟨51263489395052181379467611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34175659596701454252978407 51263489395052181379467611)
  ·
    refine ⟨76895234092578272069201417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51263489395052181379467611 76895234092578272069201417)
    ·
      refine ⟨57671425569433704051901063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76895234092578272069201417 57671425569433704051901063)
      ·
        refine ⟨86507138354150556077851595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57671425569433704051901063 86507138354150556077851595)
        ·
          refine ⟨129760707531225834116777393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86507138354150556077851595 129760707531225834116777393)
          ·
            refine ⟨97320530648419375587583045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129760707531225834116777393 97320530648419375587583045)
            ·
              refine ⟨18247599496578632922671821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97320530648419375587583045 18247599496578632922671821)
              ·
                refine ⟨6842849811216987346001933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18247599496578632922671821 6842849811216987346001933)
                ·
                  refine ⟨2566068679206370254750725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6842849811216987346001933 2566068679206370254750725)
                  ·
                    refine ⟨481137877351194422765761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2566068679206370254750725 481137877351194422765761)
                    ·
                      rfl

theorem cell22_1405519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_1405519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405519 prefixEnd_1405519 := by exact prefixLift 1405519
  have htrace : WordTrace (prefixWord ++ tailWord_1405519) baseStart_1405519 baseEnd_1405519 := by
    simpa [prefixWord, tailWord_1405519, baseEnd_1405519] using wordTrace_append hprefix tailTrace_1405519
  have hstable : (prefixWord ++ tailWord_1405519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405519).length < 2 ^ (prefixWord ++ tailWord_1405519).sum := by decide
  have hdescent : baseEnd_1405519 < baseStart_1405519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405536 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_1405536 : Nat := 118140960795 + 1405536 * 2 ^ 59
def prefixEnd_1405536 : Nat := 4983230072969 + 3 ^ 40 * 1405536 * 2
def baseEnd_1405536 : Nat := 481143696798612045090709

theorem tailTrace_1405536 : CollatzResearch.WordTrace tailWord_1405536 prefixEnd_1405536 481143696798612045090709 := by
  unfold tailWord_1405536
  simp only [CollatzResearch.WordTrace]
  refine ⟨25632054717995296641418231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34176072957327062188557641 25632054717995296641418231)
  ·
    refine ⟨38448082076992944962127347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25632054717995296641418231 38448082076992944962127347)
    ·
      refine ⟨57672123115489417443191021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38448082076992944962127347 57672123115489417443191021)
      ·
        refine ⟨21627046168308531541196633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57672123115489417443191021 21627046168308531541196633)
        ·
          refine ⟨16220284626231398655897475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21627046168308531541196633 16220284626231398655897475)
          ·
            refine ⟨24330426939347097983846213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16220284626231398655897475 24330426939347097983846213)
            ·
              refine ⟨4561955051127580871971165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24330426939347097983846213 4561955051127580871971165)
              ·
                refine ⟨1710733144172842826989187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4561955051127580871971165 1710733144172842826989187)
                ·
                  refine ⟨2566099716259264240483781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710733144172842826989187 2566099716259264240483781)
                  ·
                    refine ⟨481143696798612045090709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2566099716259264240483781 481143696798612045090709)
                    ·
                      rfl

theorem cell22_1405536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_1405536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405536 prefixEnd_1405536 := by exact prefixLift 1405536
  have htrace : WordTrace (prefixWord ++ tailWord_1405536) baseStart_1405536 baseEnd_1405536 := by
    simpa [prefixWord, tailWord_1405536, baseEnd_1405536] using wordTrace_append hprefix tailTrace_1405536
  have hstable : (prefixWord ++ tailWord_1405536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405536).length < 2 ^ (prefixWord ++ tailWord_1405536).sum := by decide
  have hdescent : baseEnd_1405536 < baseStart_1405536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405551 : List Nat := [1, 1, 2, 1, 3, 2, 2, 6, 4]
def baseStart_1405551 : Nat := 118140960795 + 1405551 * 2 ^ 59
def prefixEnd_1405551 : Nat := 4983230072969 + 3 ^ 40 * 1405551 * 2
def baseEnd_1405551 : Nat := 160382943868385668655221

theorem tailTrace_1405551 : CollatzResearch.WordTrace tailWord_1405551 prefixEnd_1405551 160382943868385668655221 := by
  unfold tailWord_1405551
  simp only [CollatzResearch.WordTrace]
  refine ⟨51264656530936250844632507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34176437687290833896421671 51264656530936250844632507)
  ·
    refine ⟨76896984796404376266948761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51264656530936250844632507 76896984796404376266948761)
    ·
      refine ⟨57672738597303282200211571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76896984796404376266948761 57672738597303282200211571)
      ·
        refine ⟨86509107895954923300317357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57672738597303282200211571 86509107895954923300317357)
        ·
          refine ⟨32440915460983096237619009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86509107895954923300317357 32440915460983096237619009)
          ·
            refine ⟨24330686595737322178214257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32440915460983096237619009 24330686595737322178214257)
            ·
              refine ⟨18248014946802991633660693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24330686595737322178214257 18248014946802991633660693)
              ·
                refine ⟨855375700631390232827845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18248014946802991633660693 855375700631390232827845)
                ·
                  refine ⟨160382943868385668655221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 855375700631390232827845 160382943868385668655221)
                  ·
                    rfl

theorem cell22_1405551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 4].length) (baseStart_1405551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405551 prefixEnd_1405551 := by exact prefixLift 1405551
  have htrace : WordTrace (prefixWord ++ tailWord_1405551) baseStart_1405551 baseEnd_1405551 := by
    simpa [prefixWord, tailWord_1405551, baseEnd_1405551] using wordTrace_append hprefix tailTrace_1405551
  have hstable : (prefixWord ++ tailWord_1405551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405551).length < 2 ^ (prefixWord ++ tailWord_1405551).sum := by decide
  have hdescent : baseEnd_1405551 < baseStart_1405551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405557 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 5]
def baseStart_1405557 : Nat := 118140960795 + 1405557 * 2 ^ 59
def prefixEnd_1405557 : Nat := 4983230072969 + 3 ^ 40 * 1405557 * 2
def baseEnd_1405557 : Nat := 160383628509258330105215

theorem tailTrace_1405557 : CollatzResearch.WordTrace tailWord_1405557 prefixEnd_1405557 160383628509258330105215 := by
  unfold tailWord_1405557
  simp only [CollatzResearch.WordTrace]
  refine ⟨51264875368914513869350925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34176583579276342579567283 51264875368914513869350925)
  ·
    refine ⟨19224328263342942701006597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51264875368914513869350925 19224328263342942701006597)
    ·
      refine ⟨3604561549376801756438737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19224328263342942701006597 3604561549376801756438737)
      ·
        refine ⟨2703421162032601317329053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3604561549376801756438737 2703421162032601317329053)
        ·
          refine ⟨1013782935762225493998395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2703421162032601317329053 1013782935762225493998395)
          ·
            refine ⟨1520674403643338240997593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013782935762225493998395 1520674403643338240997593)
            ·
              refine ⟨1140505802732503680748195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520674403643338240997593 1140505802732503680748195)
              ·
                refine ⟨1710758704098755521122293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140505802732503680748195 1710758704098755521122293)
                ·
                  refine ⟨160383628509258330105215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1710758704098755521122293 160383628509258330105215)
                  ·
                    rfl

theorem cell22_1405557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_1405557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405557 prefixEnd_1405557 := by exact prefixLift 1405557
  have htrace : WordTrace (prefixWord ++ tailWord_1405557) baseStart_1405557 baseEnd_1405557 := by
    simpa [prefixWord, tailWord_1405557, baseEnd_1405557] using wordTrace_append hprefix tailTrace_1405557
  have hstable : (prefixWord ++ tailWord_1405557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405557).length < 2 ^ (prefixWord ++ tailWord_1405557).sum := by decide
  have hdescent : baseEnd_1405557 < baseStart_1405557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405564 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1405564 : Nat := 118140960795 + 1405564 * 2 ^ 59
def prefixEnd_1405564 : Nat := 4983230072969 + 3 ^ 40 * 1405564 * 2
def baseEnd_1405564 : Nat := 481153281770829305390623

theorem tailTrace_1405564 : CollatzResearch.WordTrace tailWord_1405564 prefixEnd_1405564 481153281770829305390623 := by
  unfold tailWord_1405564
  simp only [CollatzResearch.WordTrace]
  refine ⟨25632565339944577032427873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34176753786592769376570497 25632565339944577032427873)
  ·
    refine ⟨19224424004958432774320905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25632565339944577032427873 19224424004958432774320905)
    ·
      refine ⟨14418318003718824580740679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19224424004958432774320905 14418318003718824580740679)
      ·
        refine ⟨21627477005578236871111019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14418318003718824580740679 21627477005578236871111019)
        ·
          refine ⟨32441215508367355306666529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21627477005578236871111019 32441215508367355306666529)
          ·
            refine ⟨24330911631275516479999897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32441215508367355306666529 24330911631275516479999897)
            ·
              refine ⟨18248183723456637359999923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24330911631275516479999897 18248183723456637359999923)
              ·
                refine ⟨27372275585184956039999885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18248183723456637359999923 27372275585184956039999885)
                ·
                  refine ⟨10264603344444358514999957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27372275585184956039999885 10264603344444358514999957)
                  ·
                    refine ⟨481153281770829305390623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10264603344444358514999957 481153281770829305390623)
                    ·
                      rfl

theorem cell22_1405564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1405564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405564 prefixEnd_1405564 := by exact prefixLift 1405564
  have htrace : WordTrace (prefixWord ++ tailWord_1405564) baseStart_1405564 baseEnd_1405564 := by
    simpa [prefixWord, tailWord_1405564, baseEnd_1405564] using wordTrace_append hprefix tailTrace_1405564
  have hstable : (prefixWord ++ tailWord_1405564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405564).length < 2 ^ (prefixWord ++ tailWord_1405564).sum := by decide
  have hdescent : baseEnd_1405564 < baseStart_1405564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405598 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1405598 : Nat := 118140960795 + 1405598 * 2 ^ 59
def prefixEnd_1405598 : Nat := 4983230072969 + 3 ^ 40 * 1405598 * 2
def baseEnd_1405598 : Nat := 481164920665664550040519

theorem tailTrace_1405598 : CollatzResearch.WordTrace tailWord_1405598 prefixEnd_1405598 481164920665664550040519 := by
  unfold tailWord_1405598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6408296345220747233949181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34177580507843985247728965 6408296345220747233949181)
  ·
    refine ⟨2403111129457780212730943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6408296345220747233949181 2403111129457780212730943)
    ·
      refine ⟨3604666694186670319096415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2403111129457780212730943 3604666694186670319096415)
      ·
        refine ⟨5407000041280005478644623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604666694186670319096415 5407000041280005478644623)
        ·
          refine ⟨8110500061920008217966935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407000041280005478644623 8110500061920008217966935)
          ·
            refine ⟨12165750092880012326950403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8110500061920008217966935 12165750092880012326950403)
            ·
              refine ⟨18248625139320018490425605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12165750092880012326950403 18248625139320018490425605)
              ·
                refine ⟨3421617213622503466954801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18248625139320018490425605 3421617213622503466954801)
                ·
                  refine ⟨2566212910216877600216101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3421617213622503466954801 2566212910216877600216101)
                  ·
                    refine ⟨481164920665664550040519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2566212910216877600216101 481164920665664550040519)
                    ·
                      rfl

theorem cell22_1405598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1405598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405598 prefixEnd_1405598 := by exact prefixLift 1405598
  have htrace : WordTrace (prefixWord ++ tailWord_1405598) baseStart_1405598 baseEnd_1405598 := by
    simpa [prefixWord, tailWord_1405598, baseEnd_1405598] using wordTrace_append hprefix tailTrace_1405598
  have hstable : (prefixWord ++ tailWord_1405598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405598).length < 2 ^ (prefixWord ++ tailWord_1405598).sum := by decide
  have hdescent : baseEnd_1405598 < baseStart_1405598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405600 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 2, 3]
def baseStart_1405600 : Nat := 118140960795 + 1405600 * 2 ^ 59
def prefixEnd_1405600 : Nat := 4983230072969 + 3 ^ 40 * 1405600 * 2
def baseEnd_1405600 : Nat := 481165605306537211490513

theorem tailTrace_1405600 : CollatzResearch.WordTrace tailWord_1405600 prefixEnd_1405600 481165605306537211490513 := by
  unfold tailWord_1405600
  simp only [CollatzResearch.WordTrace]
  refine ⟨25633221853879366106583127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34177629138505821475444169 25633221853879366106583127)
  ·
    refine ⟨38449832780819049159874691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25633221853879366106583127 38449832780819049159874691)
    ·
      refine ⟨57674749171228573739812037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38449832780819049159874691 57674749171228573739812037)
      ·
        refine ⟨10814015469605357576214757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57674749171228573739812037 10814015469605357576214757)
        ·
          refine ⟨2027627900551004545540267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10814015469605357576214757 2027627900551004545540267)
          ·
            refine ⟨3041441850826506818310401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027627900551004545540267 3041441850826506818310401)
            ·
              refine ⟨2281081388119880113732801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3041441850826506818310401 2281081388119880113732801)
              ·
                refine ⟨1710811041089910085299601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281081388119880113732801 1710811041089910085299601)
                ·
                  refine ⟨1283108280817432563974701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710811041089910085299601 1283108280817432563974701)
                  ·
                    refine ⟨481165605306537211490513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283108280817432563974701 481165605306537211490513)
                    ·
                      rfl

theorem cell22_1405600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_1405600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405600 prefixEnd_1405600 := by exact prefixLift 1405600
  have htrace : WordTrace (prefixWord ++ tailWord_1405600) baseStart_1405600 baseEnd_1405600 := by
    simpa [prefixWord, tailWord_1405600, baseEnd_1405600] using wordTrace_append hprefix tailTrace_1405600
  have hstable : (prefixWord ++ tailWord_1405600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405600).length < 2 ^ (prefixWord ++ tailWord_1405600).sum := by decide
  have hdescent : baseEnd_1405600 < baseStart_1405600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405609 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_1405609 : Nat := 118140960795 + 1405609 * 2 ^ 59
def prefixEnd_1405609 : Nat := 4983230072969 + 3 ^ 40 * 1405609 * 2
def baseEnd_1405609 : Nat := 481168686190464188015485

theorem tailTrace_1405609 : CollatzResearch.WordTrace tailWord_1405609 prefixEnd_1405609 481168686190464188015485 := by
  unfold tailWord_1405609
  simp only [CollatzResearch.WordTrace]
  refine ⟨51266771964726126750243881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34177847976484084500162587 51266771964726126750243881)
  ·
    refine ⟨38450078973544595062682911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51266771964726126750243881 38450078973544595062682911)
    ·
      refine ⟨57675118460316892594024367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38450078973544595062682911 57675118460316892594024367)
      ·
        refine ⟨86512677690475338891036551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57675118460316892594024367 86512677690475338891036551)
        ·
          refine ⟨129769016535713008336554827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86512677690475338891036551 129769016535713008336554827)
          ·
            refine ⟨194653524803569512504832241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129769016535713008336554827 194653524803569512504832241)
            ·
              refine ⟨145990143602677134378624181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194653524803569512504832241 145990143602677134378624181)
              ·
                refine ⟨13686575962750981347996017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145990143602677134378624181 13686575962750981347996017)
                ·
                  refine ⟨10264931972063236010997013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13686575962750981347996017 10264931972063236010997013)
                  ·
                    refine ⟨481168686190464188015485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10264931972063236010997013 481168686190464188015485)
                    ·
                      rfl

theorem cell22_1405609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_1405609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405609 prefixEnd_1405609 := by exact prefixLift 1405609
  have htrace : WordTrace (prefixWord ++ tailWord_1405609) baseStart_1405609 baseEnd_1405609 := by
    simpa [prefixWord, tailWord_1405609, baseEnd_1405609] using wordTrace_append hprefix tailTrace_1405609
  have hstable : (prefixWord ++ tailWord_1405609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405609).length < 2 ^ (prefixWord ++ tailWord_1405609).sum := by decide
  have hdescent : baseEnd_1405609 < baseStart_1405609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405613 : List Nat := [1, 5, 2, 1, 1, 4, 1, 7]
def baseStart_1405613 : Nat := 118140960795 + 1405613 * 2 ^ 59
def prefixEnd_1405613 : Nat := 4983230072969 + 3 ^ 40 * 1405613 * 2
def baseEnd_1405613 : Nat := 53463339496912167879497

theorem tailTrace_1405613 : CollatzResearch.WordTrace tailWord_1405613 prefixEnd_1405613 53463339496912167879497 := by
  unfold tailWord_1405613
  simp only [CollatzResearch.WordTrace]
  refine ⟨51266917856711635433389493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34177945237807756955592995 51266917856711635433389493)
  ·
    refine ⟨4806273549066715821880265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51266917856711635433389493 4806273549066715821880265)
    ·
      refine ⟨3604705161800036866410199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4806273549066715821880265 3604705161800036866410199)
      ·
        refine ⟨5407057742700055299615299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604705161800036866410199 5407057742700055299615299)
        ·
          refine ⟨8110586614050082949422949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407057742700055299615299 8110586614050082949422949)
          ·
            refine ⟨1520734990134390553016803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8110586614050082949422949 1520734990134390553016803)
            ·
              refine ⟨2281102485201585829525205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520734990134390553016803 2281102485201585829525205)
              ·
                refine ⟨53463339496912167879497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2281102485201585829525205 53463339496912167879497)
                ·
                  rfl

theorem cell22_1405613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 7].length) (baseStart_1405613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405613 prefixEnd_1405613 := by exact prefixLift 1405613
  have htrace : WordTrace (prefixWord ++ tailWord_1405613) baseStart_1405613 baseEnd_1405613 := by
    simpa [prefixWord, tailWord_1405613, baseEnd_1405613] using wordTrace_append hprefix tailTrace_1405613
  have hstable : (prefixWord ++ tailWord_1405613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405613).length < 2 ^ (prefixWord ++ tailWord_1405613).sum := by decide
  have hdescent : baseEnd_1405613 < baseStart_1405613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405624 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 11]
def baseStart_1405624 : Nat := 118140960795 + 1405624 * 2 ^ 59
def prefixEnd_1405624 : Nat := 4983230072969 + 3 ^ 40 * 1405624 * 2
def baseEnd_1405624 : Nat := 160391273665669716296813

theorem tailTrace_1405624 : CollatzResearch.WordTrace tailWord_1405624 prefixEnd_1405624 160391273665669716296813 := by
  unfold tailWord_1405624
  simp only [CollatzResearch.WordTrace]
  refine ⟨25633659529835892156019963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34178212706447856208026617 25633659529835892156019963)
  ·
    refine ⟨38450489294753838234029945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25633659529835892156019963 38450489294753838234029945)
    ·
      refine ⟨28837866971065378675522459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38450489294753838234029945 28837866971065378675522459)
      ·
        refine ⟨43256800456598068013283689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28837866971065378675522459 43256800456598068013283689)
        ·
          refine ⟨32442600342448551009962767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43256800456598068013283689 32442600342448551009962767)
          ·
            refine ⟨48663900513672826514944151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32442600342448551009962767 48663900513672826514944151)
            ·
              refine ⟨72995850770509239772416227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48663900513672826514944151 72995850770509239772416227)
              ·
                refine ⟨109493776155763859658624341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72995850770509239772416227 109493776155763859658624341)
                ·
                  refine ⟨160391273665669716296813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 109493776155763859658624341 160391273665669716296813)
                  ·
                    rfl

theorem cell22_1405624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_1405624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405624 prefixEnd_1405624 := by exact prefixLift 1405624
  have htrace : WordTrace (prefixWord ++ tailWord_1405624) baseStart_1405624 baseEnd_1405624 := by
    simpa [prefixWord, tailWord_1405624, baseEnd_1405624] using wordTrace_append hprefix tailTrace_1405624
  have hstable : (prefixWord ++ tailWord_1405624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405624).length < 2 ^ (prefixWord ++ tailWord_1405624).sum := by decide
  have hdescent : baseEnd_1405624 < baseStart_1405624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405628 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_1405628 : Nat := 118140960795 + 1405628 * 2 ^ 59
def prefixEnd_1405628 : Nat := 4983230072969 + 3 ^ 40 * 1405628 * 2
def baseEnd_1405628 : Nat := 481175190278754471790427

theorem tailTrace_1405628 : CollatzResearch.WordTrace tailWord_1405628 prefixEnd_1405628 481175190278754471790427 := by
  unfold tailWord_1405628
  simp only [CollatzResearch.WordTrace]
  refine ⟨25633732475828646497592769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34178309967771528663457025 25633732475828646497592769)
  ·
    refine ⟨19225299356871484873194577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25633732475828646497592769 19225299356871484873194577)
    ·
      refine ⟨14418974517653613654895933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19225299356871484873194577 14418974517653613654895933)
      ·
        refine ⟨5407115444120105120585975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14418974517653613654895933 5407115444120105120585975)
        ·
          refine ⟨8110673166180157680878963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407115444120105120585975 8110673166180157680878963)
          ·
            refine ⟨12166009749270236521318445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8110673166180157680878963 12166009749270236521318445)
            ·
              refine ⟨4562253655976338695494417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12166009749270236521318445 4562253655976338695494417)
              ·
                refine ⟨3421690241982254021620813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4562253655976338695494417 3421690241982254021620813)
                ·
                  refine ⟨1283133840743345258107805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3421690241982254021620813 1283133840743345258107805)
                  ·
                    refine ⟨481175190278754471790427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283133840743345258107805 481175190278754471790427)
                    ·
                      rfl

theorem cell22_1405628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_1405628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405628 prefixEnd_1405628 := by exact prefixLift 1405628
  have htrace : WordTrace (prefixWord ++ tailWord_1405628) baseStart_1405628 baseEnd_1405628 := by
    simpa [prefixWord, tailWord_1405628, baseEnd_1405628] using wordTrace_append hprefix tailTrace_1405628
  have hstable : (prefixWord ++ tailWord_1405628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405628).length < 2 ^ (prefixWord ++ tailWord_1405628).sum := by decide
  have hdescent : baseEnd_1405628 < baseStart_1405628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405656 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_1405656 : Nat := 118140960795 + 1405656 * 2 ^ 59
def prefixEnd_1405656 : Nat := 4983230072969 + 3 ^ 40 * 1405656 * 2
def baseEnd_1405656 : Nat := 481184775250971732090341

theorem tailTrace_1405656 : CollatzResearch.WordTrace tailWord_1405656 prefixEnd_1405656 481184775250971732090341 := by
  unfold tailWord_1405656
  simp only [CollatzResearch.WordTrace]
  refine ⟨25634243097777926888602411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34178990797037235851469881 25634243097777926888602411)
  ·
    refine ⟨38451364646666890332903617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25634243097777926888602411 38451364646666890332903617)
    ·
      refine ⟨28838523485000167749677713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38451364646666890332903617 28838523485000167749677713)
      ·
        refine ⟨21628892613750125812258285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28838523485000167749677713 21628892613750125812258285)
        ·
          refine ⟨8110834730156297179596857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21628892613750125812258285 8110834730156297179596857)
          ·
            refine ⟨6083126047617222884697643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8110834730156297179596857 6083126047617222884697643)
            ·
              refine ⟨9124689071425834327046465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083126047617222884697643 9124689071425834327046465)
              ·
                refine ⟨6843516803569375745284849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9124689071425834327046465 6843516803569375745284849)
                ·
                  refine ⟨5132637602677031808963637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6843516803569375745284849 5132637602677031808963637)
                  ·
                    refine ⟨481184775250971732090341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5132637602677031808963637 481184775250971732090341)
                    ·
                      rfl

theorem cell22_1405656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_1405656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405656 prefixEnd_1405656 := by exact prefixLift 1405656
  have htrace : WordTrace (prefixWord ++ tailWord_1405656) baseStart_1405656 baseEnd_1405656 := by
    simpa [prefixWord, tailWord_1405656, baseEnd_1405656] using wordTrace_append hprefix tailTrace_1405656
  have hstable : (prefixWord ++ tailWord_1405656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405656).length < 2 ^ (prefixWord ++ tailWord_1405656).sum := by decide
  have hdescent : baseEnd_1405656 < baseStart_1405656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405688 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_1405688 : Nat := 118140960795 + 1405688 * 2 ^ 59
def prefixEnd_1405688 : Nat := 4983230072969 + 3 ^ 40 * 1405688 * 2
def baseEnd_1405688 : Nat := 481195729504934315290243

theorem tailTrace_1405688 : CollatzResearch.WordTrace tailWord_1405688 prefixEnd_1405688 481195729504934315290243 := by
  unfold tailWord_1405688
  simp only [CollatzResearch.WordTrace]
  refine ⟨25634826665719961621184859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34179768887626615494913145 25634826665719961621184859)
  ·
    refine ⟨38452239998579942431777289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25634826665719961621184859 38452239998579942431777289)
    ·
      refine ⟨28839179998934956823832967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38452239998579942431777289 28839179998934956823832967)
      ·
        refine ⟨43258769998402435235749451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28839179998934956823832967 43258769998402435235749451)
        ·
          refine ⟨64888154997603652853624177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43258769998402435235749451 64888154997603652853624177)
          ·
            refine ⟨48666116248202739640218133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64888154997603652853624177 48666116248202739640218133)
            ·
              refine ⟨2281224199134503420635225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48666116248202739640218133 2281224199134503420635225)
              ·
                refine ⟨1710918149350877565476419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281224199134503420635225 1710918149350877565476419)
                ·
                  refine ⟨2566377224026316348214629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710918149350877565476419 2566377224026316348214629)
                  ·
                    refine ⟨481195729504934315290243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2566377224026316348214629 481195729504934315290243)
                    ·
                      rfl

theorem cell22_1405688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_1405688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405688 prefixEnd_1405688 := by exact prefixLift 1405688
  have htrace : WordTrace (prefixWord ++ tailWord_1405688) baseStart_1405688 baseEnd_1405688 := by
    simpa [prefixWord, tailWord_1405688, baseEnd_1405688] using wordTrace_append hprefix tailTrace_1405688
  have hstable : (prefixWord ++ tailWord_1405688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405688).length < 2 ^ (prefixWord ++ tailWord_1405688).sum := by decide
  have hdescent : baseEnd_1405688 < baseStart_1405688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405701 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_1405701 : Nat := 118140960795 + 1405701 * 2 ^ 59
def prefixEnd_1405701 : Nat := 4983230072969 + 3 ^ 40 * 1405701 * 2
def baseEnd_1405701 : Nat := 481200179670606614715203

theorem tailTrace_1405701 : CollatzResearch.WordTrace tailWord_1405701 prefixEnd_1405701 481200179670606614715203 := by
  unfold tailWord_1405701
  simp only [CollatzResearch.WordTrace]
  refine ⟨51270127480392826462592957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34180084986928550975061971 51270127480392826462592957)
  ·
    refine ⟨19226297805147309923472359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51270127480392826462592957 19226297805147309923472359)
    ·
      refine ⟨28839446707720964885208539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19226297805147309923472359 28839446707720964885208539)
      ·
        refine ⟨43259170061581447327812809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28839446707720964885208539 43259170061581447327812809)
        ·
          refine ⟨32444377546186085495859607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43259170061581447327812809 32444377546186085495859607)
          ·
            refine ⟨48666566319279128243789411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32444377546186085495859607 48666566319279128243789411)
            ·
              refine ⟨72999849478918692365684117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48666566319279128243789411 72999849478918692365684117)
              ·
                refine ⟨3421867944324313704641443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72999849478918692365684117 3421867944324313704641443)
                ·
                  refine ⟨5132801916486470556962165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421867944324313704641443 5132801916486470556962165)
                  ·
                    refine ⟨481200179670606614715203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5132801916486470556962165 481200179670606614715203)
                    ·
                      rfl

theorem cell22_1405701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_1405701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405701 prefixEnd_1405701 := by exact prefixLift 1405701
  have htrace : WordTrace (prefixWord ++ tailWord_1405701) baseStart_1405701 baseEnd_1405701 := by
    simpa [prefixWord, tailWord_1405701, baseEnd_1405701] using wordTrace_append hprefix tailTrace_1405701
  have hstable : (prefixWord ++ tailWord_1405701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405701).length < 2 ^ (prefixWord ++ tailWord_1405701).sum := by decide
  have hdescent : baseEnd_1405701 < baseStart_1405701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405776 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 7]
def baseStart_1405776 : Nat := 118140960795 + 1405776 * 2 ^ 59
def prefixEnd_1405776 : Nat := 4983230072969 + 3 ^ 40 * 1405776 * 2
def baseEnd_1405776 : Nat := 160408617901110473029991

theorem tailTrace_1405776 : CollatzResearch.WordTrace tailWord_1405776 prefixEnd_1405776 160408617901110473029991 := by
  unfold tailWord_1405776
  simp only [CollatzResearch.WordTrace]
  refine ⟨25636431477560557135786591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34181908636747409514382121 25636431477560557135786591)
  ·
    refine ⟨38454647216340835703679887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25636431477560557135786591 38454647216340835703679887)
    ·
      refine ⟨57681970824511253555519831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38454647216340835703679887 57681970824511253555519831)
      ·
        refine ⟨86522956236766880333279747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57681970824511253555519831 86522956236766880333279747)
        ·
          refine ⟨129784434355150320499919621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86522956236766880333279747 129784434355150320499919621)
          ·
            refine ⟨24334581441590685093734929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129784434355150320499919621 24334581441590685093734929)
            ·
              refine ⟨18250936081193013820301197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24334581441590685093734929 18250936081193013820301197)
              ·
                refine ⟨6844101030447380182612949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18250936081193013820301197 6844101030447380182612949)
                ·
                  refine ⟨160408617901110473029991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6844101030447380182612949 160408617901110473029991)
                  ·
                    rfl

theorem cell22_1405776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_1405776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405776 prefixEnd_1405776 := by exact prefixLift 1405776
  have htrace : WordTrace (prefixWord ++ tailWord_1405776) baseStart_1405776 baseEnd_1405776 := by
    simpa [prefixWord, tailWord_1405776, baseEnd_1405776] using wordTrace_append hprefix tailTrace_1405776
  have hstable : (prefixWord ++ tailWord_1405776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405776).length < 2 ^ (prefixWord ++ tailWord_1405776).sum := by decide
  have hdescent : baseEnd_1405776 < baseStart_1405776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405814 : List Nat := [5, 1, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_1405814 : Nat := 118140960795 + 1405814 * 2 ^ 59
def prefixEnd_1405814 : Nat := 4983230072969 + 3 ^ 40 * 1405814 * 2
def baseEnd_1405814 : Nat := 481238861879911986639857

theorem tailTrace_1405814 : CollatzResearch.WordTrace tailWord_1405814 prefixEnd_1405814 481238861879911986639857 := by
  unfold tailWord_1405814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204640558061465422591031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34182832619322297840970997 3204640558061465422591031)
  ·
    refine ⟨4806960837092198133886547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3204640558061465422591031 4806960837092198133886547)
    ·
      refine ⟨7210441255638297200829821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4806960837092198133886547 7210441255638297200829821)
      ·
        refine ⟨2703915470864361450311183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7210441255638297200829821 2703915470864361450311183)
        ·
          refine ⟨4055873206296542175466775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703915470864361450311183 4055873206296542175466775)
          ·
            refine ⟨6083809809444813263200163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055873206296542175466775 6083809809444813263200163)
            ·
              refine ⟨9125714714167219894800245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083809809444813263200163 9125714714167219894800245)
              ·
                refine ⟨855535754453176865137523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9125714714167219894800245 855535754453176865137523)
                ·
                  refine ⟨1283303631679765297706285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855535754453176865137523 1283303631679765297706285)
                  ·
                    refine ⟨481238861879911986639857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283303631679765297706285 481238861879911986639857)
                    ·
                      rfl

theorem cell22_1405814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_1405814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405814 prefixEnd_1405814 := by exact prefixLift 1405814
  have htrace : WordTrace (prefixWord ++ tailWord_1405814) baseStart_1405814 baseEnd_1405814 := by
    simpa [prefixWord, tailWord_1405814, baseEnd_1405814] using wordTrace_append hprefix tailTrace_1405814
  have hstable : (prefixWord ++ tailWord_1405814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405814).length < 2 ^ (prefixWord ++ tailWord_1405814).sum := by decide
  have hdescent : baseEnd_1405814 < baseStart_1405814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405857 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1405857 : Nat := 118140960795 + 1405857 * 2 ^ 59
def prefixEnd_1405857 : Nat := 4983230072969 + 3 ^ 40 * 1405857 * 2
def baseEnd_1405857 : Nat := 481253581658674207814725

theorem tailTrace_1405857 : CollatzResearch.WordTrace tailWord_1405857 prefixEnd_1405857 481253581658674207814725 := by
  unfold tailWord_1405857
  simp only [CollatzResearch.WordTrace]
  refine ⟨51275817267827665105271825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34183878178551776736847883 51275817267827665105271825)
  ·
    refine ⟨38456862950870748828953869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51275817267827665105271825 38456862950870748828953869)
    ·
      refine ⟨14421323606576530810857701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38456862950870748828953869 14421323606576530810857701)
      ·
        refine ⟨2703998176233099527035819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14421323606576530810857701 2703998176233099527035819)
        ·
          refine ⟨4055997264349649290553729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703998176233099527035819 4055997264349649290553729)
          ·
            refine ⟨3041997948262236967915297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4055997264349649290553729 3041997948262236967915297)
            ·
              refine ⟨2281498461196677725936473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3041997948262236967915297 2281498461196677725936473)
              ·
                refine ⟨1711123845897508294452355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281498461196677725936473 1711123845897508294452355)
                ·
                  refine ⟨2566685768846262441678533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711123845897508294452355 2566685768846262441678533)
                  ·
                    refine ⟨481253581658674207814725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2566685768846262441678533 481253581658674207814725)
                    ·
                      rfl

theorem cell22_1405857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1405857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405857 prefixEnd_1405857 := by exact prefixLift 1405857
  have htrace : WordTrace (prefixWord ++ tailWord_1405857) baseStart_1405857 baseEnd_1405857 := by
    simpa [prefixWord, tailWord_1405857, baseEnd_1405857] using wordTrace_append hprefix tailTrace_1405857
  have hstable : (prefixWord ++ tailWord_1405857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405857).length < 2 ^ (prefixWord ++ tailWord_1405857).sum := by decide
  have hdescent : baseEnd_1405857 < baseStart_1405857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405928 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 9]
def baseStart_1405928 : Nat := 118140960795 + 1405928 * 2 ^ 59
def prefixEnd_1405928 : Nat := 4983230072969 + 3 ^ 40 * 1405928 * 2
def baseEnd_1405928 : Nat := 160425962136551229763169

theorem tailTrace_1405928 : CollatzResearch.WordTrace tailWord_1405928 prefixEnd_1405928 160425962136551229763169 := by
  unfold tailWord_1405928
  simp only [CollatzResearch.WordTrace]
  refine ⟨25639203425285222115553219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34185604567046962820737625 25639203425285222115553219)
  ·
    refine ⟨38458805137927833173329829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25639203425285222115553219 38458805137927833173329829)
    ·
      refine ⟨7211025963361468719999343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38458805137927833173329829 7211025963361468719999343)
      ·
        refine ⟨10816538945042203079999015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7211025963361468719999343 10816538945042203079999015)
        ·
          refine ⟨16224808417563304619998523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10816538945042203079999015 16224808417563304619998523)
          ·
            refine ⟨24337212626344956929997785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16224808417563304619998523 24337212626344956929997785)
            ·
              refine ⟨18252909469758717697498339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24337212626344956929997785 18252909469758717697498339)
              ·
                refine ⟨27379364204638076546247509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18252909469758717697498339 27379364204638076546247509)
                ·
                  refine ⟨160425962136551229763169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27379364204638076546247509 160425962136551229763169)
                  ·
                    rfl

theorem cell22_1405928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_1405928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405928 prefixEnd_1405928 := by exact prefixLift 1405928
  have htrace : WordTrace (prefixWord ++ tailWord_1405928) baseStart_1405928 baseEnd_1405928 := by
    simpa [prefixWord, tailWord_1405928, baseEnd_1405928] using wordTrace_append hprefix tailTrace_1405928
  have hstable : (prefixWord ++ tailWord_1405928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405928).length < 2 ^ (prefixWord ++ tailWord_1405928).sum := by decide
  have hdescent : baseEnd_1405928 < baseStart_1405928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405945 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 5]
def baseStart_1405945 : Nat := 118140960795 + 1405945 * 2 ^ 59
def prefixEnd_1405945 : Nat := 4983230072969 + 3 ^ 40 * 1405945 * 2
def baseEnd_1405945 : Nat := 160427901952357103871485

theorem tailTrace_1405945 : CollatzResearch.WordTrace tailWord_1405945 prefixEnd_1405945 160427901952357103871485 := by
  unfold tailWord_1405945
  simp only [CollatzResearch.WordTrace]
  refine ⟨51279026891508856134475289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34186017927672570756316859 51279026891508856134475289)
  ·
    refine ⟨38459270168631642100856467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51279026891508856134475289 38459270168631642100856467)
    ·
      refine ⟨57688905252947463151284701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38459270168631642100856467 57688905252947463151284701)
      ·
        refine ⟨21633339469855298681731763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57688905252947463151284701 21633339469855298681731763)
        ·
          refine ⟨32450009204782948022597645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21633339469855298681731763 32450009204782948022597645)
          ·
            refine ⟨12168753451793605508474117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32450009204782948022597645 12168753451793605508474117)
            ·
              refine ⟨2281641272211301032838897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12168753451793605508474117 2281641272211301032838897)
              ·
                refine ⟨1711230954158475774629173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281641272211301032838897 1711230954158475774629173)
                ·
                  refine ⟨160427901952357103871485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1711230954158475774629173 160427901952357103871485)
                  ·
                    rfl

theorem cell22_1405945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_1405945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405945 prefixEnd_1405945 := by exact prefixLift 1405945
  have htrace : WordTrace (prefixWord ++ tailWord_1405945) baseStart_1405945 baseEnd_1405945 := by
    simpa [prefixWord, tailWord_1405945, baseEnd_1405945] using wordTrace_append hprefix tailTrace_1405945
  have hstable : (prefixWord ++ tailWord_1405945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405945).length < 2 ^ (prefixWord ++ tailWord_1405945).sum := by decide
  have hdescent : baseEnd_1405945 < baseStart_1405945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405960 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_1405960 : Nat := 118140960795 + 1405960 * 2 ^ 59
def prefixEnd_1405960 : Nat := 4983230072969 + 3 ^ 40 * 1405960 * 2
def baseEnd_1405960 : Nat := 481288840663616272489409

theorem tailTrace_1405960 : CollatzResearch.WordTrace tailWord_1405960 prefixEnd_1405960 481288840663616272489409 := by
  unfold tailWord_1405960
  simp only [CollatzResearch.WordTrace]
  refine ⟨25639786993227256848135667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34186382657636342464180889 25639786993227256848135667)
  ·
    refine ⟨38459680489840885272203501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25639786993227256848135667 38459680489840885272203501)
    ·
      refine ⟨14422380183690331977076313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38459680489840885272203501 14422380183690331977076313)
      ·
        refine ⟨10816785137767748982807235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14422380183690331977076313 10816785137767748982807235)
        ·
          refine ⟨16225177706651623474210853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10816785137767748982807235 16225177706651623474210853)
          ·
            refine ⟨3042220819997179401414535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16225177706651623474210853 3042220819997179401414535)
            ·
              refine ⟨4563331229995769102121803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042220819997179401414535 4563331229995769102121803)
              ·
                refine ⟨6844996844993653653182705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4563331229995769102121803 6844996844993653653182705)
                ·
                  refine ⟨5133747633745240239887029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6844996844993653653182705 5133747633745240239887029)
                  ·
                    refine ⟨481288840663616272489409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5133747633745240239887029 481288840663616272489409)
                    ·
                      rfl

theorem cell22_1405960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_1405960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1405960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1405960 prefixEnd_1405960 := by exact prefixLift 1405960
  have htrace : WordTrace (prefixWord ++ tailWord_1405960) baseStart_1405960 baseEnd_1405960 := by
    simpa [prefixWord, tailWord_1405960, baseEnd_1405960] using wordTrace_append hprefix tailTrace_1405960
  have hstable : (prefixWord ++ tailWord_1405960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405960).length < 2 ^ (prefixWord ++ tailWord_1405960).sum := by decide
  have hdescent : baseEnd_1405960 < baseStart_1405960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406069 : List Nat := [1, 3, 4, 3, 1, 1, 2, 7]
def baseStart_1406069 : Nat := 118140960795 + 1406069 * 2 ^ 59
def prefixEnd_1406069 : Nat := 4983230072969 + 3 ^ 40 * 1406069 * 2
def baseEnd_1406069 : Nat := 53480683732352924612675

theorem tailTrace_1406069 : CollatzResearch.WordTrace tailWord_1406069 prefixEnd_1406069 53480683732352924612675 := by
  unfold tailWord_1406069
  simp only [CollatzResearch.WordTrace]
  refine ⟨51283549543059625311989261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34189033028706416874659507 51283549543059625311989261)
  ·
    refine ⟨19231331078647359491995973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51283549543059625311989261 19231331078647359491995973)
    ·
      refine ⟨3605874577246379904749245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19231331078647359491995973 3605874577246379904749245)
      ·
        refine ⟨1352202966467392464280967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3605874577246379904749245 1352202966467392464280967)
        ·
          refine ⟨2028304449701088696421451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352202966467392464280967 2028304449701088696421451)
          ·
            refine ⟨3042456674551633044632177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028304449701088696421451 3042456674551633044632177)
            ·
              refine ⟨2281842505913724783474133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042456674551633044632177 2281842505913724783474133)
              ·
                refine ⟨53480683732352924612675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2281842505913724783474133 53480683732352924612675)
                ·
                  rfl

theorem cell22_1406069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 7].length) (baseStart_1406069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406069 prefixEnd_1406069 := by exact prefixLift 1406069
  have htrace : WordTrace (prefixWord ++ tailWord_1406069) baseStart_1406069 baseEnd_1406069 := by
    simpa [prefixWord, tailWord_1406069, baseEnd_1406069] using wordTrace_append hprefix tailTrace_1406069
  have hstable : (prefixWord ++ tailWord_1406069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406069).length < 2 ^ (prefixWord ++ tailWord_1406069).sum := by decide
  have hdescent : baseEnd_1406069 < baseStart_1406069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406073 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 2, 3]
def baseStart_1406073 : Nat := 118140960795 + 1406073 * 2 ^ 59
def prefixEnd_1406073 : Nat := 4983230072969 + 3 ^ 40 * 1406073 * 2
def baseEnd_1406073 : Nat := 481327522872921644414063

theorem tailTrace_1406073 : CollatzResearch.WordTrace tailWord_1406073 prefixEnd_1406073 481327522872921644414063 := by
  unfold tailWord_1406073
  simp only [CollatzResearch.WordTrace]
  refine ⟨51283695435045133995134873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34189130290030089330089915 51283695435045133995134873)
  ·
    refine ⟨38462771576283850496351155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51283695435045133995134873 38462771576283850496351155)
    ·
      refine ⟨57694157364425775744526733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38462771576283850496351155 57694157364425775744526733)
      ·
        refine ⟨21635309011659665904197525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57694157364425775744526733 21635309011659665904197525)
        ·
          refine ⟨1014155109921546839259259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21635309011659665904197525 1014155109921546839259259)
          ·
            refine ⟨1521232664882320258888889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014155109921546839259259 1521232664882320258888889)
            ·
              refine ⟨1140924498661740194166667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521232664882320258888889 1140924498661740194166667)
              ·
                refine ⟨1711386747992610291250001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140924498661740194166667 1711386747992610291250001)
                ·
                  refine ⟨1283540060994457718437501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711386747992610291250001 1283540060994457718437501)
                  ·
                    refine ⟨481327522872921644414063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283540060994457718437501 481327522872921644414063)
                    ·
                      rfl

theorem cell22_1406073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 3].length) (baseStart_1406073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406073 prefixEnd_1406073 := by exact prefixLift 1406073
  have htrace : WordTrace (prefixWord ++ tailWord_1406073) baseStart_1406073 baseEnd_1406073 := by
    simpa [prefixWord, tailWord_1406073, baseEnd_1406073] using wordTrace_append hprefix tailTrace_1406073
  have hstable : (prefixWord ++ tailWord_1406073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406073).length < 2 ^ (prefixWord ++ tailWord_1406073).sum := by decide
  have hdescent : baseEnd_1406073 < baseStart_1406073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406142 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_1406142 : Nat := 118140960795 + 1406142 * 2 ^ 59
def prefixEnd_1406142 : Nat := 4983230072969 + 3 ^ 40 * 1406142 * 2
def baseEnd_1406142 : Nat := 160450380994342821479617

theorem tailTrace_1406142 : CollatzResearch.WordTrace tailWord_1406142 prefixEnd_1406142 160450380994342821479617 := by
  unfold tailWord_1406142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6410776508974394847424585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34190808047863439186264453 6410776508974394847424585)
  ·
    refine ⟨4808082381730796135568439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6410776508974394847424585 4808082381730796135568439)
    ·
      refine ⟨7212123572596194203352659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4808082381730796135568439 7212123572596194203352659)
      ·
        refine ⟨10818185358894291305028989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7212123572596194203352659 10818185358894291305028989)
        ·
          refine ⟨4056819509585359239385871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10818185358894291305028989 4056819509585359239385871)
          ·
            refine ⟨6085229264378038859078807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4056819509585359239385871 6085229264378038859078807)
            ·
              refine ⟨9127843896567058288618211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6085229264378038859078807 9127843896567058288618211)
              ·
                refine ⟨13691765844850587432927317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9127843896567058288618211 13691765844850587432927317)
                ·
                  refine ⟨160450380994342821479617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13691765844850587432927317 160450380994342821479617)
                  ·
                    rfl

theorem cell22_1406142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_1406142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406142 prefixEnd_1406142 := by exact prefixLift 1406142
  have htrace : WordTrace (prefixWord ++ tailWord_1406142) baseStart_1406142 baseEnd_1406142 := by
    simpa [prefixWord, tailWord_1406142, baseEnd_1406142] using wordTrace_append hprefix tailTrace_1406142
  have hstable : (prefixWord ++ tailWord_1406142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406142).length < 2 ^ (prefixWord ++ tailWord_1406142).sum := by decide
  have hdescent : baseEnd_1406142 < baseStart_1406142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406185 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_1406185 : Nat := 118140960795 + 1406185 * 2 ^ 59
def prefixEnd_1406185 : Nat := 4983230072969 + 3 ^ 40 * 1406185 * 2
def baseEnd_1406185 : Nat := 481365862761790685613719

theorem tailTrace_1406185 : CollatzResearch.WordTrace tailWord_1406185 prefixEnd_1406185 481365862761790685613719 := by
  unfold tailWord_1406185
  simp only [CollatzResearch.WordTrace]
  refine ⟨51287780410639377123212009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34191853607092918082141339 51287780410639377123212009)
  ·
    refine ⟨38465835307979532842409007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51287780410639377123212009 38465835307979532842409007)
    ·
      refine ⟨57698752961969299263613511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38465835307979532842409007 57698752961969299263613511)
      ·
        refine ⟨86548129442953948895420267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57698752961969299263613511 86548129442953948895420267)
        ·
          refine ⟨129822194164430923343130401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86548129442953948895420267 129822194164430923343130401)
          ·
            refine ⟨97366645623323192507347801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129822194164430923343130401 97366645623323192507347801)
            ·
              refine ⟨73024984217492394380510851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97366645623323192507347801 73024984217492394380510851)
              ·
                refine ⟨109537476326238591570766277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73024984217492394380510851 109537476326238591570766277)
                ·
                  refine ⟨20538276811169735919518677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109537476326238591570766277 20538276811169735919518677)
                  ·
                    refine ⟨481365862761790685613719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20538276811169735919518677 481365862761790685613719)
                    ·
                      rfl

theorem cell22_1406185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_1406185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406185 prefixEnd_1406185 := by exact prefixLift 1406185
  have htrace : WordTrace (prefixWord ++ tailWord_1406185) baseStart_1406185 baseEnd_1406185 := by
    simpa [prefixWord, tailWord_1406185, baseEnd_1406185] using wordTrace_append hprefix tailTrace_1406185
  have hstable : (prefixWord ++ tailWord_1406185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406185).length < 2 ^ (prefixWord ++ tailWord_1406185).sum := by decide
  have hdescent : baseEnd_1406185 < baseStart_1406185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406191 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 1, 5]
def baseStart_1406191 : Nat := 118140960795 + 1406191 * 2 ^ 59
def prefixEnd_1406191 : Nat := 4983230072969 + 3 ^ 40 * 1406191 * 2
def baseEnd_1406191 : Nat := 481367916684408669963701

theorem tailTrace_1406191 : CollatzResearch.WordTrace tailWord_1406191 prefixEnd_1406191 481367916684408669963701 := by
  unfold tailWord_1406191
  simp only [CollatzResearch.WordTrace]
  refine ⟨51287999248617640147930427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34191999499078426765286951 51287999248617640147930427)
  ·
    refine ⟨76931998872926460221895641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51287999248617640147930427 76931998872926460221895641)
    ·
      refine ⟨57698999154694845166421731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76931998872926460221895641 57698999154694845166421731)
      ·
        refine ⟨86548498732042267749632597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57698999154694845166421731 86548498732042267749632597)
        ·
          refine ⟨1014240219516120325191007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 86548498732042267749632597 1014240219516120325191007)
          ·
            refine ⟨1521360329274180487786511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014240219516120325191007 1521360329274180487786511)
            ·
              refine ⟨2282040493911270731679767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521360329274180487786511 2282040493911270731679767)
              ·
                refine ⟨3423060740866906097519651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282040493911270731679767 3423060740866906097519651)
                ·
                  refine ⟨5134591111300359146279477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423060740866906097519651 5134591111300359146279477)
                  ·
                    refine ⟨481367916684408669963701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5134591111300359146279477 481367916684408669963701)
                    ·
                      rfl

theorem cell22_1406191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 5].length) (baseStart_1406191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406191 prefixEnd_1406191 := by exact prefixLift 1406191
  have htrace : WordTrace (prefixWord ++ tailWord_1406191) baseStart_1406191 baseEnd_1406191 := by
    simpa [prefixWord, tailWord_1406191, baseEnd_1406191] using wordTrace_append hprefix tailTrace_1406191
  have hstable : (prefixWord ++ tailWord_1406191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406191).length < 2 ^ (prefixWord ++ tailWord_1406191).sum := by decide
  have hdescent : baseEnd_1406191 < baseStart_1406191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406210 : List Nat := [3, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1406210 : Nat := 118140960795 + 1406210 * 2 ^ 59
def prefixEnd_1406210 : Nat := 4983230072969 + 3 ^ 40 * 1406210 * 2
def baseEnd_1406210 : Nat := 160458140257566317912881

theorem tailTrace_1406210 : CollatzResearch.WordTrace tailWord_1406210 prefixEnd_1406210 160458140257566317912881 := by
  unfold tailWord_1406210
  simp only [CollatzResearch.WordTrace]
  refine ⟨12822173058887201598218021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34192461490365870928581389 12822173058887201598218021)
  ·
    refine ⟨2404157448541350299665879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12822173058887201598218021 2404157448541350299665879)
    ·
      refine ⟨3606236172812025449498819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2404157448541350299665879 3606236172812025449498819)
      ·
        refine ⟨5409354259218038174248229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3606236172812025449498819 5409354259218038174248229)
        ·
          refine ⟨1014253923603382157671543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5409354259218038174248229 1014253923603382157671543)
          ·
            refine ⟨1521380885405073236507315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014253923603382157671543 1521380885405073236507315)
            ·
              refine ⟨2282071328107609854760973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521380885405073236507315 2282071328107609854760973)
              ·
                refine ⟨855776748040353695535365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2282071328107609854760973 855776748040353695535365)
                ·
                  refine ⟨160458140257566317912881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 855776748040353695535365 160458140257566317912881)
                  ·
                    rfl

theorem cell22_1406210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1406210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406210 prefixEnd_1406210 := by exact prefixLift 1406210
  have htrace : WordTrace (prefixWord ++ tailWord_1406210) baseStart_1406210 baseEnd_1406210 := by
    simpa [prefixWord, tailWord_1406210, baseEnd_1406210] using wordTrace_append hprefix tailTrace_1406210
  have hstable : (prefixWord ++ tailWord_1406210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406210).length < 2 ^ (prefixWord ++ tailWord_1406210).sum := by decide
  have hdescent : baseEnd_1406210 < baseStart_1406210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406232 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 7]
def baseStart_1406232 : Nat := 118140960795 + 1406232 * 2 ^ 59
def prefixEnd_1406232 : Nat := 4983230072969 + 3 ^ 40 * 1406232 * 2
def baseEnd_1406232 : Nat := 160460650607432743229525

theorem tailTrace_1406232 : CollatzResearch.WordTrace tailWord_1406232 prefixEnd_1406232 160460650607432743229525 := by
  unfold tailWord_1406232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25644747320734552075086475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34192996427646069433448633 25644747320734552075086475)
  ·
    refine ⟨38467120981101828112629713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25644747320734552075086475 38467120981101828112629713)
    ·
      refine ⟨28850340735826371084472285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38467120981101828112629713 28850340735826371084472285)
      ·
        refine ⟨10818877775934889156677107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28850340735826371084472285 10818877775934889156677107)
        ·
          refine ⟨16228316663902333735015661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10818877775934889156677107 16228316663902333735015661)
          ·
            refine ⟨6085618748963375150630873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16228316663902333735015661 6085618748963375150630873)
            ·
              refine ⟨4564214061722531362973155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6085618748963375150630873 4564214061722531362973155)
              ·
                refine ⟨6846321092583797044459733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4564214061722531362973155 6846321092583797044459733)
                ·
                  refine ⟨160460650607432743229525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6846321092583797044459733 160460650607432743229525)
                  ·
                    rfl

theorem cell22_1406232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_1406232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406232 prefixEnd_1406232 := by exact prefixLift 1406232
  have htrace : WordTrace (prefixWord ++ tailWord_1406232) baseStart_1406232 baseEnd_1406232 := by
    simpa [prefixWord, tailWord_1406232, baseEnd_1406232] using wordTrace_append hprefix tailTrace_1406232
  have hstable : (prefixWord ++ tailWord_1406232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406232).length < 2 ^ (prefixWord ++ tailWord_1406232).sum := by decide
  have hdescent : baseEnd_1406232 < baseStart_1406232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406236 : List Nat := [2, 2, 3, 1, 1, 1, 2, 6, 1, 3]
def baseStart_1406236 : Nat := 118140960795 + 1406236 * 2 ^ 59
def prefixEnd_1406236 : Nat := 4983230072969 + 3 ^ 40 * 1406236 * 2
def baseEnd_1406236 : Nat := 481383321104043552588563

theorem tailTrace_1406236 : CollatzResearch.WordTrace tailWord_1406236 prefixEnd_1406236 481383321104043552588563 := by
  unfold tailWord_1406236
  simp only [CollatzResearch.WordTrace]
  refine ⟨25644820266727306416659281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34193093688969741888879041 25644820266727306416659281)
  ·
    refine ⟨19233615200045479812494461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25644820266727306416659281 19233615200045479812494461)
    ·
      refine ⟨7212605700017054929685423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19233615200045479812494461 7212605700017054929685423)
      ·
        refine ⟨10818908550025582394528135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7212605700017054929685423 10818908550025582394528135)
        ·
          refine ⟨16228362825038373591792203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10818908550025582394528135 16228362825038373591792203)
          ·
            refine ⟨24342544237557560387688305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16228362825038373591792203 24342544237557560387688305)
            ·
              refine ⟨18256908178168170290766229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24342544237557560387688305 18256908178168170290766229)
              ·
                refine ⟨855792570851632982379667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18256908178168170290766229 855792570851632982379667)
                ·
                  refine ⟨1283688856277449473569501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855792570851632982379667 1283688856277449473569501)
                  ·
                    refine ⟨481383321104043552588563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283688856277449473569501 481383321104043552588563)
                    ·
                      rfl

theorem cell22_1406236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_1406236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406236 prefixEnd_1406236 := by exact prefixLift 1406236
  have htrace : WordTrace (prefixWord ++ tailWord_1406236) baseStart_1406236 baseEnd_1406236 := by
    simpa [prefixWord, tailWord_1406236, baseEnd_1406236] using wordTrace_append hprefix tailTrace_1406236
  have hstable : (prefixWord ++ tailWord_1406236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406236).length < 2 ^ (prefixWord ++ tailWord_1406236).sum := by decide
  have hdescent : baseEnd_1406236 < baseStart_1406236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406309 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_1406309 : Nat := 118140960795 + 1406309 * 2 ^ 59
def prefixEnd_1406309 : Nat := 4983230072969 + 3 ^ 40 * 1406309 * 2
def baseEnd_1406309 : Nat := 481408310495895695513339

theorem tailTrace_1406309 : CollatzResearch.WordTrace tailWord_1406309 prefixEnd_1406309 481408310495895695513339 := by
  unfold tailWord_1406309
  simp only [CollatzResearch.WordTrace]
  refine ⟨51292303062190146300725981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34194868708126764200483987 51292303062190146300725981)
  ·
    refine ⟨19234613648321304862772243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51292303062190146300725981 19234613648321304862772243)
    ·
      refine ⟨28851920472481957294158365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19234613648321304862772243 28851920472481957294158365)
      ·
        refine ⟨10819470177180733985309387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28851920472481957294158365 10819470177180733985309387)
        ·
          refine ⟨16229205265771100977964081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10819470177180733985309387 16229205265771100977964081)
          ·
            refine ⟨12171903949328325733473061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16229205265771100977964081 12171903949328325733473061)
            ·
              refine ⟨2282231990499061075026199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12171903949328325733473061 2282231990499061075026199)
              ·
                refine ⟨3423347985748591612539299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282231990499061075026199 3423347985748591612539299)
                ·
                  refine ⟨5135021978622887418808949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423347985748591612539299 5135021978622887418808949)
                  ·
                    refine ⟨481408310495895695513339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5135021978622887418808949 481408310495895695513339)
                    ·
                      rfl

theorem cell22_1406309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_1406309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406309 prefixEnd_1406309 := by exact prefixLift 1406309
  have htrace : WordTrace (prefixWord ++ tailWord_1406309) baseStart_1406309 baseEnd_1406309 := by
    simpa [prefixWord, tailWord_1406309, baseEnd_1406309] using wordTrace_append hprefix tailTrace_1406309
  have hstable : (prefixWord ++ tailWord_1406309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406309).length < 2 ^ (prefixWord ++ tailWord_1406309).sum := by decide
  have hdescent : baseEnd_1406309 < baseStart_1406309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406343 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 2, 3]
def baseStart_1406343 : Nat := 118140960795 + 1406343 * 2 ^ 59
def prefixEnd_1406343 : Nat := 4983230072969 + 3 ^ 40 * 1406343 * 2
def baseEnd_1406343 : Nat := 481419949390730940163235

theorem tailTrace_1406343 : CollatzResearch.WordTrace tailWord_1406343 prefixEnd_1406343 481419949390730940163235 := by
  unfold tailWord_1406343
  simp only [CollatzResearch.WordTrace]
  refine ⟨51293543144066970107463683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34195695429377980071642455 51293543144066970107463683)
  ·
    refine ⟨76940314716100455161195525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51293543144066970107463683 76940314716100455161195525)
    ·
      refine ⟨14426309009268835342724161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76940314716100455161195525 14426309009268835342724161)
      ·
        refine ⟨10819731756951626507043121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14426309009268835342724161 10819731756951626507043121)
        ·
          refine ⟨8114798817713719880282341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10819731756951626507043121 8114798817713719880282341)
          ·
            refine ⟨1521524778321322477552939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8114798817713719880282341 1521524778321322477552939)
            ·
              refine ⟨2282287167481983716329409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521524778321322477552939 2282287167481983716329409)
              ·
                refine ⟨1711715375611487787247057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2282287167481983716329409 1711715375611487787247057)
                ·
                  refine ⟨1283786531708615840435293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711715375611487787247057 1283786531708615840435293)
                  ·
                    refine ⟨481419949390730940163235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283786531708615840435293 481419949390730940163235)
                    ·
                      rfl

theorem cell22_1406343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_1406343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406343 prefixEnd_1406343 := by exact prefixLift 1406343
  have htrace : WordTrace (prefixWord ++ tailWord_1406343) baseStart_1406343 baseEnd_1406343 := by
    simpa [prefixWord, tailWord_1406343, baseEnd_1406343] using wordTrace_append hprefix tailTrace_1406343
  have hstable : (prefixWord ++ tailWord_1406343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406343).length < 2 ^ (prefixWord ++ tailWord_1406343).sum := by decide
  have hdescent : baseEnd_1406343 < baseStart_1406343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406360 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 2, 3]
def baseStart_1406360 : Nat := 118140960795 + 1406360 * 2 ^ 59
def prefixEnd_1406360 : Nat := 4983230072969 + 3 ^ 40 * 1406360 * 2
def baseEnd_1406360 : Nat := 481425768838148562488183

theorem tailTrace_1406360 : CollatzResearch.WordTrace tailWord_1406360 prefixEnd_1406360 481425768838148562488183 := by
  unfold tailWord_1406360
  simp only [CollatzResearch.WordTrace]
  refine ⟨25647081592502691005416267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34196108790003588007221689 25647081592502691005416267)
  ·
    refine ⟨38470622388754036508124401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25647081592502691005416267 38470622388754036508124401)
    ·
      refine ⟨28852966791565527381093301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38470622388754036508124401 28852966791565527381093301)
      ·
        refine ⟨2704965636709268191977497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28852966791565527381093301 2704965636709268191977497)
        ·
          refine ⟨2028724227531951143983123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2704965636709268191977497 2028724227531951143983123)
          ·
            refine ⟨3043086341297926715974685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028724227531951143983123 3043086341297926715974685)
            ·
              refine ⟨1141157377986722518490507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3043086341297926715974685 1141157377986722518490507)
              ·
                refine ⟨1711736066980083777735761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141157377986722518490507 1711736066980083777735761)
                ·
                  refine ⟨1283802050235062833301821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711736066980083777735761 1283802050235062833301821)
                  ·
                    refine ⟨481425768838148562488183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283802050235062833301821 481425768838148562488183)
                    ·
                      rfl

theorem cell22_1406360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_1406360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406360 prefixEnd_1406360 := by exact prefixLift 1406360
  have htrace : WordTrace (prefixWord ++ tailWord_1406360) baseStart_1406360 baseEnd_1406360 := by
    simpa [prefixWord, tailWord_1406360, baseEnd_1406360] using wordTrace_append hprefix tailTrace_1406360
  have hstable : (prefixWord ++ tailWord_1406360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406360).length < 2 ^ (prefixWord ++ tailWord_1406360).sum := by decide
  have hdescent : baseEnd_1406360 < baseStart_1406360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406448 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 1, 4]
def baseStart_1406448 : Nat := 118140960795 + 1406448 * 2 ^ 59
def prefixEnd_1406448 : Nat := 4983230072969 + 3 ^ 40 * 1406448 * 2
def baseEnd_1406448 : Nat := 481455893036545666287913

theorem tailTrace_1406448 : CollatzResearch.WordTrace tailWord_1406448 prefixEnd_1406448 481455893036545666287913 := by
  unfold tailWord_1406448
  simp only [CollatzResearch.WordTrace]
  refine ⟨25648686404343286520017999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34198248539124382026690665 25648686404343286520017999)
  ·
    refine ⟨38473029606514929780026999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25648686404343286520017999 38473029606514929780026999)
    ·
      refine ⟨57709544409772394670040499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38473029606514929780026999 57709544409772394670040499)
      ·
        refine ⟨86564316614658592005060749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57709544409772394670040499 86564316614658592005060749)
        ·
          refine ⟨32461618730496972001897781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86564316614658592005060749 32461618730496972001897781)
          ·
            refine ⟨3043276755984091125177917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32461618730496972001897781 3043276755984091125177917)
            ·
              refine ⟨1141228783494034171941719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3043276755984091125177917 1141228783494034171941719)
              ·
                refine ⟨1711843175241051257912579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141228783494034171941719 1711843175241051257912579)
                ·
                  refine ⟨2567764762861576886868869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711843175241051257912579 2567764762861576886868869)
                  ·
                    refine ⟨481455893036545666287913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2567764762861576886868869 481455893036545666287913)
                    ·
                      rfl

theorem cell22_1406448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 4].length) (baseStart_1406448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406448 prefixEnd_1406448 := by exact prefixLift 1406448
  have htrace : WordTrace (prefixWord ++ tailWord_1406448) baseStart_1406448 baseEnd_1406448 := by
    simpa [prefixWord, tailWord_1406448, baseEnd_1406448] using wordTrace_append hprefix tailTrace_1406448
  have hstable : (prefixWord ++ tailWord_1406448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406448).length < 2 ^ (prefixWord ++ tailWord_1406448).sum := by decide
  have hdescent : baseEnd_1406448 < baseStart_1406448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406478 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_1406478 : Nat := 118140960795 + 1406478 * 2 ^ 59
def prefixEnd_1406478 : Nat := 4983230072969 + 3 ^ 40 * 1406478 * 2
def baseEnd_1406478 : Nat := 481466162649635588037821

theorem tailTrace_1406478 : CollatzResearch.WordTrace tailWord_1406478 prefixEnd_1406478 481466162649635588037821 := by
  unfold tailWord_1406478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412308374822236020453511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34198977999051925442418725 6412308374822236020453511)
  ·
    refine ⟨9618462562233354030680267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6412308374822236020453511 9618462562233354030680267)
    ·
      refine ⟨14427693843350031046020401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9618462562233354030680267 14427693843350031046020401)
      ·
        refine ⟨10820770382512523284515301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14427693843350031046020401 10820770382512523284515301)
        ·
          refine ⟨2028894446721098115846619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10820770382512523284515301 2028894446721098115846619)
          ·
            refine ⟨3043341670081647173769929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028894446721098115846619 3043341670081647173769929)
            ·
              refine ⟨2282506252561235380327447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3043341670081647173769929 2282506252561235380327447)
              ·
                refine ⟨3423759378841853070491171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282506252561235380327447 3423759378841853070491171)
                ·
                  refine ⟨5135639068262779605736757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423759378841853070491171 5135639068262779605736757)
                  ·
                    refine ⟨481466162649635588037821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5135639068262779605736757 481466162649635588037821)
                    ·
                      rfl

theorem cell22_1406478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_1406478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406478 prefixEnd_1406478 := by exact prefixLift 1406478
  have htrace : WordTrace (prefixWord ++ tailWord_1406478) baseStart_1406478 baseEnd_1406478 := by
    simpa [prefixWord, tailWord_1406478, baseEnd_1406478] using wordTrace_append hprefix tailTrace_1406478
  have hstable : (prefixWord ++ tailWord_1406478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406478).length < 2 ^ (prefixWord ++ tailWord_1406478).sum := by decide
  have hdescent : baseEnd_1406478 < baseStart_1406478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406574 : List Nat := [4, 1, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_1406574 : Nat := 118140960795 + 1406574 * 2 ^ 59
def prefixEnd_1406574 : Nat := 4983230072969 + 3 ^ 40 * 1406574 * 2
def baseEnd_1406574 : Nat := 481499025411523337637527

theorem tailTrace_1406574 : CollatzResearch.WordTrace tailWord_1406574 prefixEnd_1406574 481499025411523337637527 := by
  unfold tailWord_1406574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412746050778762069890347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34201312270820064372748517 6412746050778762069890347)
  ·
    refine ⟨9619119076168143104835521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6412746050778762069890347 9619119076168143104835521)
    ·
      refine ⟨7214339307126107328626641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9619119076168143104835521 7214339307126107328626641)
      ·
        refine ⟨5410754480344580496469981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7214339307126107328626641 5410754480344580496469981)
        ·
          refine ⟨2029032930129217686176243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5410754480344580496469981 2029032930129217686176243)
          ·
            refine ⟨3043549395193826529264365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029032930129217686176243 3043549395193826529264365)
            ·
              refine ⟨1141331023197684948474137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3043549395193826529264365 1141331023197684948474137)
              ·
                refine ⟨855998267398263711355603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141331023197684948474137 855998267398263711355603)
                ·
                  refine ⟨1283997401097395567033405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855998267398263711355603 1283997401097395567033405)
                  ·
                    refine ⟨481499025411523337637527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283997401097395567033405 481499025411523337637527)
                    ·
                      rfl

theorem cell22_1406574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_1406574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406574 prefixEnd_1406574 := by exact prefixLift 1406574
  have htrace : WordTrace (prefixWord ++ tailWord_1406574) baseStart_1406574 baseEnd_1406574 := by
    simpa [prefixWord, tailWord_1406574, baseEnd_1406574] using wordTrace_append hprefix tailTrace_1406574
  have hstable : (prefixWord ++ tailWord_1406574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406574).length < 2 ^ (prefixWord ++ tailWord_1406574).sum := by decide
  have hdescent : baseEnd_1406574 < baseStart_1406574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406600 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 3, 4]
def baseStart_1406600 : Nat := 118140960795 + 1406600 * 2 ^ 59
def prefixEnd_1406600 : Nat := 4983230072969 + 3 ^ 40 * 1406600 * 2
def baseEnd_1406600 : Nat := 481507925742867936487447

theorem tailTrace_1406600 : CollatzResearch.WordTrace tailWord_1406600 prefixEnd_1406600 481507925742867936487447 := by
  unfold tailWord_1406600
  simp only [CollatzResearch.WordTrace]
  refine ⟨25651458352067951499784627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34201944469423935333046169 25651458352067951499784627)
  ·
    refine ⟨38477187528101927249676941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25651458352067951499784627 38477187528101927249676941)
    ·
      refine ⟨14428945323038222718628853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38477187528101927249676941 14428945323038222718628853)
      ·
        refine ⟨1352713624034833379871455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14428945323038222718628853 1352713624034833379871455)
        ·
          refine ⟨2029070436052250069807183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352713624034833379871455 2029070436052250069807183)
          ·
            refine ⟨3043605654078375104710775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029070436052250069807183 3043605654078375104710775)
            ·
              refine ⟨4565408481117562657066163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043605654078375104710775 4565408481117562657066163)
              ·
                refine ⟨6848112721676343985599245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565408481117562657066163 6848112721676343985599245)
                ·
                  refine ⟨2568042270628628994599717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6848112721676343985599245 2568042270628628994599717)
                  ·
                    refine ⟨481507925742867936487447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2568042270628628994599717 481507925742867936487447)
                    ·
                      rfl

theorem cell22_1406600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_1406600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406600 prefixEnd_1406600 := by exact prefixLift 1406600
  have htrace : WordTrace (prefixWord ++ tailWord_1406600) baseStart_1406600 baseEnd_1406600 := by
    simpa [prefixWord, tailWord_1406600, baseEnd_1406600] using wordTrace_append hprefix tailTrace_1406600
  have hstable : (prefixWord ++ tailWord_1406600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406600).length < 2 ^ (prefixWord ++ tailWord_1406600).sum := by decide
  have hdescent : baseEnd_1406600 < baseStart_1406600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406628 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_1406628 : Nat := 118140960795 + 1406628 * 2 ^ 59
def prefixEnd_1406628 : Nat := 4983230072969 + 3 ^ 40 * 1406628 * 2
def baseEnd_1406628 : Nat := 481517510715085196787361

theorem tailTrace_1406628 : CollatzResearch.WordTrace tailWord_1406628 prefixEnd_1406628 481517510715085196787361 := by
  unfold tailWord_1406628
  simp only [CollatzResearch.WordTrace]
  refine ⟨25651968974017231890794269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34202625298689642521059025 25651968974017231890794269)
  ·
    refine ⟨9619488365256461959047851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25651968974017231890794269 9619488365256461959047851)
    ·
      refine ⟨14429232547884692938571777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9619488365256461959047851 14429232547884692938571777)
      ·
        refine ⟨10821924410913519703928833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14429232547884692938571777 10821924410913519703928833)
        ·
          refine ⟨8116443308185139777946625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10821924410913519703928833 8116443308185139777946625)
          ·
            refine ⟨6087332481138854833459969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8116443308185139777946625 6087332481138854833459969)
            ·
              refine ⟨4565499360854141125094977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087332481138854833459969 4565499360854141125094977)
              ·
                refine ⟨3424124520640605843821233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4565499360854141125094977 3424124520640605843821233)
                ·
                  refine ⟨2568093390480454382865925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3424124520640605843821233 2568093390480454382865925)
                  ·
                    refine ⟨481517510715085196787361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2568093390480454382865925 481517510715085196787361)
                    ·
                      rfl

theorem cell22_1406628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_1406628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406628 prefixEnd_1406628 := by exact prefixLift 1406628
  have htrace : WordTrace (prefixWord ++ tailWord_1406628) baseStart_1406628 baseEnd_1406628 := by
    simpa [prefixWord, tailWord_1406628, baseEnd_1406628] using wordTrace_append hprefix tailTrace_1406628
  have hstable : (prefixWord ++ tailWord_1406628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406628).length < 2 ^ (prefixWord ++ tailWord_1406628).sum := by decide
  have hdescent : baseEnd_1406628 < baseStart_1406628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406656 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_1406656 : Nat := 118140960795 + 1406656 * 2 ^ 59
def prefixEnd_1406656 : Nat := 4983230072969 + 3 ^ 40 * 1406656 * 2
def baseEnd_1406656 : Nat := 481527095687302457087275

theorem tailTrace_1406656 : CollatzResearch.WordTrace tailWord_1406656 prefixEnd_1406656 481527095687302457087275 := by
  unfold tailWord_1406656
  simp only [CollatzResearch.WordTrace]
  refine ⟨25652479595966512281803911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34203306127955349709071881 25652479595966512281803911)
  ·
    refine ⟨38478719393949768422705867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25652479595966512281803911 38478719393949768422705867)
    ·
      refine ⟨57718079090924652634058801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38478719393949768422705867 57718079090924652634058801)
      ·
        refine ⟨43288559318193489475544101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57718079090924652634058801 43288559318193489475544101)
        ·
          refine ⟨8116604872161279276664519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43288559318193489475544101 8116604872161279276664519)
          ·
            refine ⟨12174907308241918914996779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8116604872161279276664519 12174907308241918914996779)
            ·
              refine ⟨18262360962362878372495169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12174907308241918914996779 18262360962362878372495169)
              ·
                refine ⟨13696770721772158779371377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18262360962362878372495169 13696770721772158779371377)
                ·
                  refine ⟨10272578041329119084528533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13696770721772158779371377 10272578041329119084528533)
                  ·
                    refine ⟨481527095687302457087275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10272578041329119084528533 481527095687302457087275)
                    ·
                      rfl

theorem cell22_1406656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_1406656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406656 prefixEnd_1406656 := by exact prefixLift 1406656
  have htrace : WordTrace (prefixWord ++ tailWord_1406656) baseStart_1406656 baseEnd_1406656 := by
    simpa [prefixWord, tailWord_1406656, baseEnd_1406656] using wordTrace_append hprefix tailTrace_1406656
  have hstable : (prefixWord ++ tailWord_1406656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406656).length < 2 ^ (prefixWord ++ tailWord_1406656).sum := by decide
  have hdescent : baseEnd_1406656 < baseStart_1406656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406662 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1406662 : Nat := 118140960795 + 1406662 * 2 ^ 59
def prefixEnd_1406662 : Nat := 4983230072969 + 3 ^ 40 * 1406662 * 2
def baseEnd_1406662 : Nat := 481529149609920441437257

theorem tailTrace_1406662 : CollatzResearch.WordTrace tailWord_1406662 prefixEnd_1406662 481529149609920441437257 := by
  unfold tailWord_1406662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1603286813434727737135195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34203452019940858392217493 1603286813434727737135195)
  ·
    refine ⟨2404930220152091605702793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1603286813434727737135195 2404930220152091605702793)
    ·
      refine ⟨1803697665114068704277095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2404930220152091605702793 1803697665114068704277095)
      ·
        refine ⟨2705546497671103056415643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803697665114068704277095 2705546497671103056415643)
        ·
          refine ⟨4058319746506654584623465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705546497671103056415643 4058319746506654584623465)
          ·
            refine ⟨3043739809879990938467599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4058319746506654584623465 3043739809879990938467599)
            ·
              refine ⟨4565609714819986407701399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043739809879990938467599 4565609714819986407701399)
              ·
                refine ⟨6848414572229979611552099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565609714819986407701399 6848414572229979611552099)
                ·
                  refine ⟨10272621858344969417328149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6848414572229979611552099 10272621858344969417328149)
                  ·
                    refine ⟨481529149609920441437257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10272621858344969417328149 481529149609920441437257)
                    ·
                      rfl

theorem cell22_1406662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1406662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406662 prefixEnd_1406662 := by exact prefixLift 1406662
  have htrace : WordTrace (prefixWord ++ tailWord_1406662) baseStart_1406662 baseEnd_1406662 := by
    simpa [prefixWord, tailWord_1406662, baseEnd_1406662] using wordTrace_append hprefix tailTrace_1406662
  have hstable : (prefixWord ++ tailWord_1406662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406662).length < 2 ^ (prefixWord ++ tailWord_1406662).sum := by decide
  have hdescent : baseEnd_1406662 < baseStart_1406662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406688 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 5]
def baseStart_1406688 : Nat := 118140960795 + 1406688 * 2 ^ 59
def prefixEnd_1406688 : Nat := 4983230072969 + 3 ^ 40 * 1406688 * 2
def baseEnd_1406688 : Nat := 160512683313755013429059

theorem tailTrace_1406688 : CollatzResearch.WordTrace tailWord_1406688 prefixEnd_1406688 160512683313755013429059 := by
  unfold tailWord_1406688
  simp only [CollatzResearch.WordTrace]
  refine ⟨25653063163908547014386359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34204084218544729352515145 25653063163908547014386359)
  ·
    refine ⟨38479594745862820521579539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25653063163908547014386359 38479594745862820521579539)
    ·
      refine ⟨57719392118794230782369309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38479594745862820521579539 57719392118794230782369309)
      ·
        refine ⟨21644772044547836543388491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57719392118794230782369309 21644772044547836543388491)
        ·
          refine ⟨32467158066821754815082737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21644772044547836543388491 32467158066821754815082737)
          ·
            refine ⟨24350368550116316111312053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32467158066821754815082737 24350368550116316111312053)
            ·
              refine ⟨2282847051573404635435505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24350368550116316111312053 2282847051573404635435505)
              ·
                refine ⟨1712135288680053476576629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2282847051573404635435505 1712135288680053476576629)
                ·
                  refine ⟨160512683313755013429059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1712135288680053476576629 160512683313755013429059)
                  ·
                    rfl

theorem cell22_1406688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_1406688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406688 prefixEnd_1406688 := by exact prefixLift 1406688
  have htrace : WordTrace (prefixWord ++ tailWord_1406688) baseStart_1406688 baseEnd_1406688 := by
    simpa [prefixWord, tailWord_1406688, baseEnd_1406688] using wordTrace_append hprefix tailTrace_1406688
  have hstable : (prefixWord ++ tailWord_1406688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406688).length < 2 ^ (prefixWord ++ tailWord_1406688).sum := by decide
  have hdescent : baseEnd_1406688 < baseStart_1406688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406705 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 5]
def baseStart_1406705 : Nat := 118140960795 + 1406705 * 2 ^ 59
def prefixEnd_1406705 : Nat := 4983230072969 + 3 ^ 40 * 1406705 * 2
def baseEnd_1406705 : Nat := 160514623129560887537375

theorem tailTrace_1406705 : CollatzResearch.WordTrace tailWord_1406705 prefixEnd_1406705 160514623129560887537375 := by
  unfold tailWord_1406705
  simp only [CollatzResearch.WordTrace]
  refine ⟨51306746368755505932141569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34204497579170337288094379 51306746368755505932141569)
  ·
    refine ⟨38480059776566629449106177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51306746368755505932141569 38480059776566629449106177)
    ·
      refine ⟨28860044832424972086829633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38480059776566629449106177 28860044832424972086829633)
      ·
        refine ⟨21645033624318729065122225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28860044832424972086829633 21645033624318729065122225)
        ·
          refine ⟨16233775218239046798841669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21645033624318729065122225 16233775218239046798841669)
          ·
            refine ⟨3043832853419821274782813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16233775218239046798841669 3043832853419821274782813)
            ·
              refine ⟨1141437320032432978043555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3043832853419821274782813 1141437320032432978043555)
              ·
                refine ⟨1712155980048649467065333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141437320032432978043555 1712155980048649467065333)
                ·
                  refine ⟨160514623129560887537375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1712155980048649467065333 160514623129560887537375)
                  ·
                    rfl

theorem cell22_1406705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 5].length) (baseStart_1406705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406705 prefixEnd_1406705 := by exact prefixLift 1406705
  have htrace : WordTrace (prefixWord ++ tailWord_1406705) baseStart_1406705 baseEnd_1406705 := by
    simpa [prefixWord, tailWord_1406705, baseEnd_1406705] using wordTrace_append hprefix tailTrace_1406705
  have hstable : (prefixWord ++ tailWord_1406705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406705).length < 2 ^ (prefixWord ++ tailWord_1406705).sum := by decide
  have hdescent : baseEnd_1406705 < baseStart_1406705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406778 : List Nat := [3, 1, 1, 1, 5, 1, 2, 8]
def baseStart_1406778 : Nat := 118140960795 + 1406778 * 2 ^ 59
def prefixEnd_1406778 : Nat := 4983230072969 + 3 ^ 40 * 1406778 * 2
def baseEnd_1406778 : Nat := 53507650975614978392989

theorem tailTrace_1406778 : CollatzResearch.WordTrace tailWord_1406778 prefixEnd_1406778 53507650975614978392989 := by
  unfold tailWord_1406778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12827352224372759849887247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34206272598327359599699325 12827352224372759849887247)
  ·
    refine ⟨19241028336559139774830871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12827352224372759849887247 19241028336559139774830871)
    ·
      refine ⟨28861542504838709662246307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19241028336559139774830871 28861542504838709662246307)
      ·
        refine ⟨43292313757258064493369461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28861542504838709662246307 43292313757258064493369461)
        ·
          refine ⟨4058654414742943546253387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43292313757258064493369461 4058654414742943546253387)
          ·
            refine ⟨6087981622114415319380081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058654414742943546253387 6087981622114415319380081)
            ·
              refine ⟨4565986216585811489535061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087981622114415319380081 4565986216585811489535061)
              ·
                refine ⟨53507650975614978392989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4565986216585811489535061 53507650975614978392989)
                ·
                  rfl

theorem cell22_1406778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_1406778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406778 prefixEnd_1406778 := by exact prefixLift 1406778
  have htrace : WordTrace (prefixWord ++ tailWord_1406778) baseStart_1406778 baseEnd_1406778 := by
    simpa [prefixWord, tailWord_1406778, baseEnd_1406778] using wordTrace_append hprefix tailTrace_1406778
  have hstable : (prefixWord ++ tailWord_1406778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406778).length < 2 ^ (prefixWord ++ tailWord_1406778).sum := by decide
  have hdescent : baseEnd_1406778 < baseStart_1406778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406797 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1406797 : Nat := 118140960795 + 1406797 * 2 ^ 59
def prefixEnd_1406797 : Nat := 4983230072969 + 3 ^ 40 * 1406797 * 2
def baseEnd_1406797 : Nat := 481575362868825089311843

theorem tailTrace_1406797 : CollatzResearch.WordTrace tailWord_1406797 prefixEnd_1406797 481575362868825089311843 := by
  unfold tailWord_1406797
  simp only [CollatzResearch.WordTrace]
  refine ⟨51310101884422205644490645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34206734589614803762993763 51310101884422205644490645)
  ·
    refine ⟨2405161025832290889585499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51310101884422205644490645 2405161025832290889585499)
    ·
      refine ⟨3607741538748436334378249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2405161025832290889585499 3607741538748436334378249)
      ·
        refine ⟨2705806154061327250783687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3607741538748436334378249 2705806154061327250783687)
        ·
          refine ⟨4058709231091990876175531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705806154061327250783687 4058709231091990876175531)
          ·
            refine ⟨6088063846637986314263297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058709231091990876175531 6088063846637986314263297)
            ·
              refine ⟨4566047884978489735697473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6088063846637986314263297 4566047884978489735697473)
              ·
                refine ⟨3424535913733867301773105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4566047884978489735697473 3424535913733867301773105)
                ·
                  refine ⟨2568401935300400476329829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3424535913733867301773105 2568401935300400476329829)
                  ·
                    refine ⟨481575362868825089311843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2568401935300400476329829 481575362868825089311843)
                    ·
                      rfl

theorem cell22_1406797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1406797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406797 prefixEnd_1406797 := by exact prefixLift 1406797
  have htrace : WordTrace (prefixWord ++ tailWord_1406797) baseStart_1406797 baseEnd_1406797 := by
    simpa [prefixWord, tailWord_1406797, baseEnd_1406797] using wordTrace_append hprefix tailTrace_1406797
  have hstable : (prefixWord ++ tailWord_1406797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406797).length < 2 ^ (prefixWord ++ tailWord_1406797).sum := by decide
  have hdescent : baseEnd_1406797 < baseStart_1406797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406810 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_1406810 : Nat := 118140960795 + 1406810 * 2 ^ 59
def prefixEnd_1406810 : Nat := 4983230072969 + 3 ^ 40 * 1406810 * 2
def baseEnd_1406810 : Nat := 481579813034497388736803

theorem tailTrace_1406810 : CollatzResearch.WordTrace tailWord_1406810 prefixEnd_1406810 481579813034497388736803 := by
  unfold tailWord_1406810
  simp only [CollatzResearch.WordTrace]
  refine ⟨12827644008343777216178471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34207050688916739243142589 12827644008343777216178471)
  ·
    refine ⟨19241466012515665824267707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12827644008343777216178471 19241466012515665824267707)
    ·
      refine ⟨28862199018773498736401561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19241466012515665824267707 28862199018773498736401561)
      ·
        refine ⟨21646649264080124052301171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28862199018773498736401561 21646649264080124052301171)
        ·
          refine ⟨32469973896120186078451757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21646649264080124052301171 32469973896120186078451757)
          ·
            refine ⟨12176240211045069779419409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32469973896120186078451757 12176240211045069779419409)
            ·
              refine ⟨9132180158283802334564557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12176240211045069779419409 9132180158283802334564557)
              ·
                refine ⟨3424567559356425875461709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9132180158283802334564557 3424567559356425875461709)
                ·
                  refine ⟨1284212834758659703298141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3424567559356425875461709 1284212834758659703298141)
                  ·
                    refine ⟨481579813034497388736803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1284212834758659703298141 481579813034497388736803)
                    ·
                      rfl

theorem cell22_1406810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_1406810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406810 prefixEnd_1406810 := by exact prefixLift 1406810
  have htrace : WordTrace (prefixWord ++ tailWord_1406810) baseStart_1406810 baseEnd_1406810 := by
    simpa [prefixWord, tailWord_1406810, baseEnd_1406810] using wordTrace_append hprefix tailTrace_1406810
  have hstable : (prefixWord ++ tailWord_1406810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406810).length < 2 ^ (prefixWord ++ tailWord_1406810).sum := by decide
  have hdescent : baseEnd_1406810 < baseStart_1406810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406812 : List Nat := [2, 2, 4, 2, 2, 2, 1, 7]
def baseStart_1406812 : Nat := 118140960795 + 1406812 * 2 ^ 59
def prefixEnd_1406812 : Nat := 4983230072969 + 3 ^ 40 * 1406812 * 2
def baseEnd_1406812 : Nat := 53508944186152227798533

theorem tailTrace_1406812 : CollatzResearch.WordTrace tailWord_1406812 prefixEnd_1406812 53508944186152227798533 := by
  unfold tailWord_1406812
  simp only [CollatzResearch.WordTrace]
  refine ⟨25655324489683931603143345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34207099319578575470857793 25655324489683931603143345)
  ·
    refine ⟨19241493367262948702357509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25655324489683931603143345 19241493367262948702357509)
    ·
      refine ⟨3607780006361802881692033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19241493367262948702357509 3607780006361802881692033)
      ·
        refine ⟨2705835004771352161269025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3607780006361802881692033 2705835004771352161269025)
        ·
          refine ⟨2029376253578514120951769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2705835004771352161269025 2029376253578514120951769)
          ·
            refine ⟨1522032190183885590713827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2029376253578514120951769 1522032190183885590713827)
            ·
              refine ⟨2283048285275828386070741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522032190183885590713827 2283048285275828386070741)
              ·
                refine ⟨53508944186152227798533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2283048285275828386070741 53508944186152227798533)
                ·
                  rfl

theorem cell22_1406812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 7].length) (baseStart_1406812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406812 prefixEnd_1406812 := by exact prefixLift 1406812
  have htrace : WordTrace (prefixWord ++ tailWord_1406812) baseStart_1406812 baseEnd_1406812 := by
    simpa [prefixWord, tailWord_1406812, baseEnd_1406812] using wordTrace_append hprefix tailTrace_1406812
  have hstable : (prefixWord ++ tailWord_1406812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406812).length < 2 ^ (prefixWord ++ tailWord_1406812).sum := by decide
  have hdescent : baseEnd_1406812 < baseStart_1406812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406887 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1406887 : Nat := 118140960795 + 1406887 * 2 ^ 59
def prefixEnd_1406887 : Nat := 4983230072969 + 3 ^ 40 * 1406887 * 2
def baseEnd_1406887 : Nat := 481606171708094854561567

theorem tailTrace_1406887 : CollatzResearch.WordTrace tailWord_1406887 prefixEnd_1406887 481606171708094854561567 := by
  unfold tailWord_1406887
  simp only [CollatzResearch.WordTrace]
  refine ⟨51313384454096151015266915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34208922969397434010177943 51313384454096151015266915)
  ·
    refine ⟨76970076681144226522900373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51313384454096151015266915 76970076681144226522900373)
    ·
      refine ⟨3607972344428635618260955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76970076681144226522900373 3607972344428635618260955)
      ·
        refine ⟨5411958516642953427391433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607972344428635618260955 5411958516642953427391433)
        ·
          refine ⟨4058968887482215070543575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5411958516642953427391433 4058968887482215070543575)
          ·
            refine ⟨6088453331223322605815363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058968887482215070543575 6088453331223322605815363)
            ·
              refine ⟨9132679996834983908723045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088453331223322605815363 9132679996834983908723045)
              ·
                refine ⟨1712377499406559482885571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9132679996834983908723045 1712377499406559482885571)
                ·
                  refine ⟨2568566249109839224328357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712377499406559482885571 2568566249109839224328357)
                  ·
                    refine ⟨481606171708094854561567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2568566249109839224328357 481606171708094854561567)
                    ·
                      rfl

theorem cell22_1406887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1406887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1406887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1406887 prefixEnd_1406887 := by exact prefixLift 1406887
  have htrace : WordTrace (prefixWord ++ tailWord_1406887) baseStart_1406887 baseEnd_1406887 := by
    simpa [prefixWord, tailWord_1406887, baseEnd_1406887] using wordTrace_append hprefix tailTrace_1406887
  have hstable : (prefixWord ++ tailWord_1406887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406887).length < 2 ^ (prefixWord ++ tailWord_1406887).sum := by decide
  have hdescent : baseEnd_1406887 < baseStart_1406887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407037 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 6]
def baseStart_1407037 : Nat := 118140960795 + 1407037 * 2 ^ 59
def prefixEnd_1407037 : Nat := 4983230072969 + 3 ^ 40 * 1407037 * 2
def baseEnd_1407037 : Nat := 160552506591181487770369

theorem tailTrace_1407037 : CollatzResearch.WordTrace tailWord_1407037 prefixEnd_1407037 160552506591181487770369 := by
  unfold tailWord_1407037
  simp only [CollatzResearch.WordTrace]
  refine ⟨51318855403552726633227365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34212570269035151088818243 51318855403552726633227365)
  ·
    refine ⟨9622285388166136243730131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51318855403552726633227365 9622285388166136243730131)
    ·
      refine ⟨14433428082249204365595197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9622285388166136243730131 14433428082249204365595197)
      ·
        refine ⟨5412535530843451637098199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14433428082249204365595197 5412535530843451637098199)
        ·
          refine ⟨8118803296265177455647299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412535530843451637098199 8118803296265177455647299)
          ·
            refine ⟨12178204944397766183470949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118803296265177455647299 12178204944397766183470949)
            ·
              refine ⟨2283413427074581159400803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12178204944397766183470949 2283413427074581159400803)
              ·
                refine ⟨3425120140611871739101205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283413427074581159400803 3425120140611871739101205)
                ·
                  refine ⟨160552506591181487770369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3425120140611871739101205 160552506591181487770369)
                  ·
                    rfl

theorem cell22_1407037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_1407037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407037 prefixEnd_1407037 := by exact prefixLift 1407037
  have htrace : WordTrace (prefixWord ++ tailWord_1407037) baseStart_1407037 baseEnd_1407037 := by
    simpa [prefixWord, tailWord_1407037, baseEnd_1407037] using wordTrace_append hprefix tailTrace_1407037
  have hstable : (prefixWord ++ tailWord_1407037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407037).length < 2 ^ (prefixWord ++ tailWord_1407037).sum := by decide
  have hdescent : baseEnd_1407037 < baseStart_1407037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407052 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_1407052 : Nat := 118140960795 + 1407052 * 2 ^ 59
def prefixEnd_1407052 : Nat := 4983230072969 + 3 ^ 40 * 1407052 * 2
def baseEnd_1407052 : Nat := 481662654580089424186061

theorem tailTrace_1407052 : CollatzResearch.WordTrace tailWord_1407052 prefixEnd_1407052 481662654580089424186061 := by
  unfold tailWord_1407052
  simp only [CollatzResearch.WordTrace]
  refine ⟨25659701249249192097511705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34212934998998922796682273 25659701249249192097511705)
  ·
    refine ⟨19244775936936894073133779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25659701249249192097511705 19244775936936894073133779)
    ·
      refine ⟨28867163905405341109700669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19244775936936894073133779 28867163905405341109700669)
      ·
        refine ⟨10825186464527002916137751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28867163905405341109700669 10825186464527002916137751)
        ·
          refine ⟨16237779696790504374206627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10825186464527002916137751 16237779696790504374206627)
          ·
            refine ⟨24356669545185756561309941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16237779696790504374206627 24356669545185756561309941)
            ·
              refine ⟨2283437769861164677622807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24356669545185756561309941 2283437769861164677622807)
              ·
                refine ⟨3425156654791747016434211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283437769861164677622807 3425156654791747016434211)
                ·
                  refine ⟨5137734982187620524651317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425156654791747016434211 5137734982187620524651317)
                  ·
                    refine ⟨481662654580089424186061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5137734982187620524651317 481662654580089424186061)
                    ·
                      rfl

theorem cell22_1407052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_1407052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407052 prefixEnd_1407052 := by exact prefixLift 1407052
  have htrace : WordTrace (prefixWord ++ tailWord_1407052) baseStart_1407052 baseEnd_1407052 := by
    simpa [prefixWord, tailWord_1407052, baseEnd_1407052] using wordTrace_append hprefix tailTrace_1407052
  have hstable : (prefixWord ++ tailWord_1407052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407052).length < 2 ^ (prefixWord ++ tailWord_1407052).sum := by decide
  have hdescent : baseEnd_1407052 < baseStart_1407052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407065 : List Nat := [1, 2, 1, 2, 2, 1, 5, 8]
def baseStart_1407065 : Nat := 118140960795 + 1407065 * 2 ^ 59
def prefixEnd_1407065 : Nat := 4983230072969 + 3 ^ 40 * 1407065 * 2
def baseEnd_1407065 : Nat := 53518567193973524845669

theorem tailTrace_1407065 : CollatzResearch.WordTrace tailWord_1407065 prefixEnd_1407065 53518567193973524845669 := by
  unfold tailWord_1407065
  simp only [CollatzResearch.WordTrace]
  refine ⟨51319876647451287415246649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34213251098300858276831099 51319876647451287415246649)
  ·
    refine ⟨38489907485588465561434987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51319876647451287415246649 38489907485588465561434987)
    ·
      refine ⟨57734861228382698342152481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38489907485588465561434987 57734861228382698342152481)
      ·
        refine ⟨43301145921287023756614361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57734861228382698342152481 43301145921287023756614361)
        ·
          refine ⟨32475859440965267817460771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43301145921287023756614361 32475859440965267817460771)
          ·
            refine ⟨48713789161447901726191157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32475859440965267817460771 48713789161447901726191157)
            ·
              refine ⟨4566917733885740786830421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48713789161447901726191157 4566917733885740786830421)
              ·
                refine ⟨53518567193973524845669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4566917733885740786830421 53518567193973524845669)
                ·
                  rfl

theorem cell22_1407065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 8].length) (baseStart_1407065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407065 prefixEnd_1407065 := by exact prefixLift 1407065
  have htrace : WordTrace (prefixWord ++ tailWord_1407065) baseStart_1407065 baseEnd_1407065 := by
    simpa [prefixWord, tailWord_1407065, baseEnd_1407065] using wordTrace_append hprefix tailTrace_1407065
  have hstable : (prefixWord ++ tailWord_1407065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407065).length < 2 ^ (prefixWord ++ tailWord_1407065).sum := by decide
  have hdescent : baseEnd_1407065 < baseStart_1407065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407272 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1407272 : Nat := 118140960795 + 1407272 * 2 ^ 59
def prefixEnd_1407272 : Nat := 4983230072969 + 3 ^ 40 * 1407272 * 2
def baseEnd_1407272 : Nat := 481737965076082183685387

theorem tailTrace_1407272 : CollatzResearch.WordTrace tailWord_1407272 prefixEnd_1407272 481737965076082183685387 := by
  unfold tailWord_1407272
  simp only [CollatzResearch.WordTrace]
  refine ⟨25663713278850680884016035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34218284371800907845354713 25663713278850680884016035)
  ·
    refine ⟨38495569918276021326024053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25663713278850680884016035 38495569918276021326024053)
    ·
      refine ⟨3608959679838376999314755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38495569918276021326024053 3608959679838376999314755)
      ·
        refine ⟨5413439519757565498972133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608959679838376999314755 5413439519757565498972133)
        ·
          refine ⟨1015019909954543531057275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5413439519757565498972133 1015019909954543531057275)
          ·
            refine ⟨1522529864931815296585913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015019909954543531057275 1522529864931815296585913)
            ·
              refine ⟨1141897398698861472439435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1522529864931815296585913 1141897398698861472439435)
              ·
                refine ⟨1712846098048292208659153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141897398698861472439435 1712846098048292208659153)
                ·
                  refine ⟨1284634573536219156494365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1712846098048292208659153 1284634573536219156494365)
                  ·
                    refine ⟨481737965076082183685387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1284634573536219156494365 481737965076082183685387)
                    ·
                      rfl

theorem cell22_1407272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1407272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407272 prefixEnd_1407272 := by exact prefixLift 1407272
  have htrace : WordTrace (prefixWord ++ tailWord_1407272) baseStart_1407272 baseEnd_1407272 := by
    simpa [prefixWord, tailWord_1407272, baseEnd_1407272] using wordTrace_append hprefix tailTrace_1407272
  have hstable : (prefixWord ++ tailWord_1407272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407272).length < 2 ^ (prefixWord ++ tailWord_1407272).sum := by decide
  have hdescent : baseEnd_1407272 < baseStart_1407272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407307 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 10]
def baseStart_1407307 : Nat := 118140960795 + 1407307 * 2 ^ 59
def prefixEnd_1407307 : Nat := 4983230072969 + 3 ^ 40 * 1407307 * 2
def baseEnd_1407307 : Nat := 160583315430451253020093

theorem tailTrace_1407307 : CollatzResearch.WordTrace tailWord_1407307 prefixEnd_1407307 160583315430451253020093 := by
  unfold tailWord_1407307
  simp only [CollatzResearch.WordTrace]
  refine ⟨51328703112574562745556175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34219135408383041830370783 51328703112574562745556175)
  ·
    refine ⟨76993054668861844118334263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51328703112574562745556175 76993054668861844118334263)
    ·
      refine ⟨115489582003292766177501395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76993054668861844118334263 115489582003292766177501395)
      ·
        refine ⟨173234373004939149266252093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115489582003292766177501395 173234373004939149266252093)
        ·
          refine ⟨64962889876852180974844535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173234373004939149266252093 64962889876852180974844535)
          ·
            refine ⟨97444334815278271462266803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64962889876852180974844535 97444334815278271462266803)
            ·
              refine ⟨146166502222917407193400205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97444334815278271462266803 146166502222917407193400205)
              ·
                refine ⟨54812438333594027697525077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146166502222917407193400205 54812438333594027697525077)
                ·
                  refine ⟨160583315430451253020093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 54812438333594027697525077 160583315430451253020093)
                  ·
                    rfl

theorem cell22_1407307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 10].length) (baseStart_1407307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407307 prefixEnd_1407307 := by exact prefixLift 1407307
  have htrace : WordTrace (prefixWord ++ tailWord_1407307) baseStart_1407307 baseEnd_1407307 := by
    simpa [prefixWord, tailWord_1407307, baseEnd_1407307] using wordTrace_append hprefix tailTrace_1407307
  have hstable : (prefixWord ++ tailWord_1407307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407307).length < 2 ^ (prefixWord ++ tailWord_1407307).sum := by decide
  have hdescent : baseEnd_1407307 < baseStart_1407307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407317 : List Nat := [1, 3, 2, 2, 4, 2, 2, 2, 1, 3]
def baseStart_1407317 : Nat := 118140960795 + 1407317 * 2 ^ 59
def prefixEnd_1407317 : Nat := 4983230072969 + 3 ^ 40 * 1407317 * 2
def baseEnd_1407317 : Nat := 481753369495717066310249

theorem tailTrace_1407317 : CollatzResearch.WordTrace tailWord_1407317 prefixEnd_1407317 481753369495717066310249 := by
  unfold tailWord_1407317
  simp only [CollatzResearch.WordTrace]
  refine ⟨51329067842538334453420205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34219378561692222968946803 51329067842538334453420205)
  ·
    refine ⟨19248400440951875420032577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51329067842538334453420205 19248400440951875420032577)
    ·
      refine ⟨14436300330713906565024433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19248400440951875420032577 14436300330713906565024433)
      ·
        refine ⟨10827225248035429923768325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14436300330713906565024433 10827225248035429923768325)
        ·
          refine ⟨2030104734006643110706561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10827225248035429923768325 2030104734006643110706561)
          ·
            refine ⟨1522578550504982333029921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2030104734006643110706561 1522578550504982333029921)
            ·
              refine ⟨1141933912878736749772441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1522578550504982333029921 1141933912878736749772441)
              ·
                refine ⟨856450434659052562329331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141933912878736749772441 856450434659052562329331)
                ·
                  refine ⟨1284675651988578843493997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856450434659052562329331 1284675651988578843493997)
                  ·
                    refine ⟨481753369495717066310249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1284675651988578843493997 481753369495717066310249)
                    ·
                      rfl

theorem cell22_1407317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_1407317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407317 prefixEnd_1407317 := by exact prefixLift 1407317
  have htrace : WordTrace (prefixWord ++ tailWord_1407317) baseStart_1407317 baseEnd_1407317 := by
    simpa [prefixWord, tailWord_1407317, baseEnd_1407317] using wordTrace_append hprefix tailTrace_1407317
  have hstable : (prefixWord ++ tailWord_1407317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407317).length < 2 ^ (prefixWord ++ tailWord_1407317).sum := by decide
  have hdescent : baseEnd_1407317 < baseStart_1407317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407369 : List Nat := [1, 2, 1, 1, 6, 2, 9]
def baseStart_1407369 : Nat := 118140960795 + 1407369 * 2 ^ 59
def prefixEnd_1407369 : Nat := 4983230072969 + 3 ^ 40 * 1407369 * 2
def baseEnd_1407369 : Nat := 17843376672533565333707

theorem tailTrace_1407369 : CollatzResearch.WordTrace tailWord_1407369 prefixEnd_1407369 17843376672533565333707 := by
  unfold tailWord_1407369
  simp only [CollatzResearch.WordTrace]
  refine ⟨51330964438349947334313161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34220642958899964889542107 51330964438349947334313161)
  ·
    refine ⟨38498223328762460500734871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51330964438349947334313161 38498223328762460500734871)
    ·
      refine ⟨57747334993143690751102307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38498223328762460500734871 57747334993143690751102307)
      ·
        refine ⟨86621002489715536126653461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57747334993143690751102307 86621002489715536126653461)
        ·
          refine ⟨4060359491705415755936881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86621002489715536126653461 4060359491705415755936881)
          ·
            refine ⟨3045269618779061816952661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4060359491705415755936881 3045269618779061816952661)
            ·
              refine ⟨17843376672533565333707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3045269618779061816952661 17843376672533565333707)
              ·
                rfl

theorem cell22_1407369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 9].length) (baseStart_1407369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407369 prefixEnd_1407369 := by exact prefixLift 1407369
  have htrace : WordTrace (prefixWord ++ tailWord_1407369) baseStart_1407369 baseEnd_1407369 := by
    simpa [prefixWord, tailWord_1407369, baseEnd_1407369] using wordTrace_append hprefix tailTrace_1407369
  have hstable : (prefixWord ++ tailWord_1407369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407369).length < 2 ^ (prefixWord ++ tailWord_1407369).sum := by decide
  have hdescent : baseEnd_1407369 < baseStart_1407369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407390 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1407390 : Nat := 118140960795 + 1407390 * 2 ^ 59
def prefixEnd_1407390 : Nat := 4983230072969 + 3 ^ 40 * 1407390 * 2
def baseEnd_1407390 : Nat := 481778358887569209235025

theorem tailTrace_1407390 : CollatzResearch.WordTrace tailWord_1407390 prefixEnd_1407390 481778358887569209235025 := by
  unfold tailWord_1407390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416466296409233490103453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34221153580849245280551749 6416466296409233490103453)
  ·
    refine ⟨2406174861153462558788795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6416466296409233490103453 2406174861153462558788795)
    ·
      refine ⟨3609262291730193838183193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2406174861153462558788795 3609262291730193838183193)
      ·
        refine ⟨2706946718797645378637395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3609262291730193838183193 2706946718797645378637395)
        ·
          refine ⟨4060420078196468067956093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706946718797645378637395 4060420078196468067956093)
          ·
            refine ⟨1522657529323675525483535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4060420078196468067956093 1522657529323675525483535)
            ·
              refine ⟨2283986293985513288225303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522657529323675525483535 2283986293985513288225303)
              ·
                refine ⟨3425979440978269932337955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283986293985513288225303 3425979440978269932337955)
                ·
                  refine ⟨5138969161467404898506933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425979440978269932337955 5138969161467404898506933)
                  ·
                    refine ⟨481778358887569209235025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5138969161467404898506933 481778358887569209235025)
                    ·
                      rfl

theorem cell22_1407390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1407390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407390 prefixEnd_1407390 := by exact prefixLift 1407390
  have htrace : WordTrace (prefixWord ++ tailWord_1407390) baseStart_1407390 baseEnd_1407390 := by
    simpa [prefixWord, tailWord_1407390, baseEnd_1407390] using wordTrace_append hprefix tailTrace_1407390
  have hstable : (prefixWord ++ tailWord_1407390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407390).length < 2 ^ (prefixWord ++ tailWord_1407390).sum := by decide
  have hdescent : baseEnd_1407390 < baseStart_1407390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407523 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 2, 4]
def baseStart_1407523 : Nat := 118140960795 + 1407523 * 2 ^ 59
def prefixEnd_1407523 : Nat := 4983230072969 + 3 ^ 40 * 1407523 * 2
def baseEnd_1407523 : Nat := 481823887505601195659617

theorem tailTrace_1407523 : CollatzResearch.WordTrace tailWord_1407523 prefixEnd_1407523 481823887505601195659617 := by
  unfold tailWord_1407523
  simp only [CollatzResearch.WordTrace]
  refine ⟨51336581279792031635419223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34224387519861354423612815 51336581279792031635419223)
  ·
    refine ⟨77004871919688047453128835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51336581279792031635419223 77004871919688047453128835)
    ·
      refine ⟨115507307879532071179693253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77004871919688047453128835 115507307879532071179693253)
      ·
        refine ⟨21657620227412263346192485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115507307879532071179693253 21657620227412263346192485)
        ·
          refine ⟨4060803792639799377411091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21657620227412263346192485 4060803792639799377411091)
          ·
            refine ⟨6091205688959699066116637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4060803792639799377411091 6091205688959699066116637)
            ·
              refine ⟨2284202133359887149793739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6091205688959699066116637 2284202133359887149793739)
              ·
                refine ⟨3426303200039830724690609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284202133359887149793739 3426303200039830724690609)
                ·
                  refine ⟨2569727400029873043517957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426303200039830724690609 2569727400029873043517957)
                  ·
                    refine ⟨481823887505601195659617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2569727400029873043517957 481823887505601195659617)
                    ·
                      rfl

theorem cell22_1407523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 4].length) (baseStart_1407523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407523 prefixEnd_1407523 := by exact prefixLift 1407523
  have htrace : WordTrace (prefixWord ++ tailWord_1407523) baseStart_1407523 baseEnd_1407523 := by
    simpa [prefixWord, tailWord_1407523, baseEnd_1407523] using wordTrace_append hprefix tailTrace_1407523
  have hstable : (prefixWord ++ tailWord_1407523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407523).length < 2 ^ (prefixWord ++ tailWord_1407523).sum := by decide
  have hdescent : baseEnd_1407523 < baseStart_1407523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407542 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1407542 : Nat := 118140960795 + 1407542 * 2 ^ 59
def prefixEnd_1407542 : Nat := 4983230072969 + 3 ^ 40 * 1407542 * 2
def baseEnd_1407542 : Nat := 481830391593891479434559

theorem tailTrace_1407542 : CollatzResearch.WordTrace tailWord_1407542 prefixEnd_1407542 481830391593891479434559 := by
  unfold tailWord_1407542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3208579641670199867522555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34224849511148798586907253 3208579641670199867522555)
  ·
    refine ⟨4812869462505299801283833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3208579641670199867522555 4812869462505299801283833)
    ·
      refine ⟨3609652096878974850962875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4812869462505299801283833 3609652096878974850962875)
      ·
        refine ⟨5414478145318462276444313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3609652096878974850962875 5414478145318462276444313)
        ·
          refine ⟨4060858608988846707333235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5414478145318462276444313 4060858608988846707333235)
          ·
            refine ⟨6091287913483270060999853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4060858608988846707333235 6091287913483270060999853)
            ·
              refine ⟨2284232967556226272874945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6091287913483270060999853 2284232967556226272874945)
              ·
                refine ⟨1713174725667169704656209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284232967556226272874945 1713174725667169704656209)
                ·
                  refine ⟨1284881044250377278492157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1713174725667169704656209 1284881044250377278492157)
                  ·
                    refine ⟨481830391593891479434559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1284881044250377278492157 481830391593891479434559)
                    ·
                      rfl

theorem cell22_1407542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1407542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407542 prefixEnd_1407542 := by exact prefixLift 1407542
  have htrace : WordTrace (prefixWord ++ tailWord_1407542) baseStart_1407542 baseEnd_1407542 := by
    simpa [prefixWord, tailWord_1407542, baseEnd_1407542] using wordTrace_append hprefix tailTrace_1407542
  have hstable : (prefixWord ++ tailWord_1407542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407542).length < 2 ^ (prefixWord ++ tailWord_1407542).sum := by decide
  have hdescent : baseEnd_1407542 < baseStart_1407542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407611 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 6]
def baseStart_1407611 : Nat := 118140960795 + 1407611 * 2 ^ 59
def prefixEnd_1407611 : Nat := 4983230072969 + 3 ^ 40 * 1407611 * 2
def baseEnd_1407611 : Nat := 160618003901332766486449

theorem tailTrace_1407611 : CollatzResearch.WordTrace tailWord_1407611 prefixEnd_1407611 160618003901332766486449 := by
  unfold tailWord_1407611
  simp only [CollatzResearch.WordTrace]
  refine ⟨51339790903473222664622687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34226527268982148443081791 51339790903473222664622687)
  ·
    refine ⟨77009686355209833996934031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51339790903473222664622687 77009686355209833996934031)
    ·
      refine ⟨115514529532814750995401047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77009686355209833996934031 115514529532814750995401047)
      ·
        refine ⟨173271794299222126493101571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115514529532814750995401047 173271794299222126493101571)
        ·
          refine ⟨259907691448833189739652357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173271794299222126493101571 259907691448833189739652357)
          ·
            refine ⟨48732692146656223076184817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259907691448833189739652357 48732692146656223076184817)
            ·
              refine ⟨36549519109992167307138613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48732692146656223076184817 36549519109992167307138613)
              ·
                refine ⟨3426517416561765685044245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36549519109992167307138613 3426517416561765685044245)
                ·
                  refine ⟨160618003901332766486449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3426517416561765685044245 160618003901332766486449)
                  ·
                    rfl

theorem cell22_1407611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 6].length) (baseStart_1407611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407611 prefixEnd_1407611 := by exact prefixLift 1407611
  have htrace : WordTrace (prefixWord ++ tailWord_1407611) baseStart_1407611 baseEnd_1407611 := by
    simpa [prefixWord, tailWord_1407611, baseEnd_1407611] using wordTrace_append hprefix tailTrace_1407611
  have hstable : (prefixWord ++ tailWord_1407611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407611).length < 2 ^ (prefixWord ++ tailWord_1407611).sum := by decide
  have hdescent : baseEnd_1407611 < baseStart_1407611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407690 : List Nat := [3, 1, 2, 1, 4, 2, 3, 6]
def baseStart_1407690 : Nat := 118140960795 + 1407690 * 2 ^ 59
def prefixEnd_1407690 : Nat := 4983230072969 + 3 ^ 40 * 1407690 * 2
def baseEnd_1407690 : Nat := 53542339446496491859345

theorem tailTrace_1407690 : CollatzResearch.WordTrace tailWord_1407690 prefixEnd_1407690 53542339446496491859345 := by
  unfold tailWord_1407690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12835668067546754789187131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34228448180124679437832349 12835668067546754789187131)
  ·
    refine ⟨19253502101320132183780697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12835668067546754789187131 19253502101320132183780697)
    ·
      refine ⟨14440126575990099137835523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19253502101320132183780697 14440126575990099137835523)
      ·
        refine ⟨21660189863985148706753285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14440126575990099137835523 21660189863985148706753285)
        ·
          refine ⟨4061285599497215382516241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21660189863985148706753285 4061285599497215382516241)
          ·
            refine ⟨3045964199622911536887181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4061285599497215382516241 3045964199622911536887181)
            ·
              refine ⟨1142236574858591826332693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3045964199622911536887181 1142236574858591826332693)
              ·
                refine ⟨53542339446496491859345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1142236574858591826332693 53542339446496491859345)
                ·
                  rfl

theorem cell22_1407690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_1407690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407690 prefixEnd_1407690 := by exact prefixLift 1407690
  have htrace : WordTrace (prefixWord ++ tailWord_1407690) baseStart_1407690 baseEnd_1407690 := by
    simpa [prefixWord, tailWord_1407690, baseEnd_1407690] using wordTrace_append hprefix tailTrace_1407690
  have hstable : (prefixWord ++ tailWord_1407690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407690).length < 2 ^ (prefixWord ++ tailWord_1407690).sum := by decide
  have hdescent : baseEnd_1407690 < baseStart_1407690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407692 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_1407692 : Nat := 118140960795 + 1407692 * 2 ^ 59
def prefixEnd_1407692 : Nat := 4983230072969 + 3 ^ 40 * 1407692 * 2
def baseEnd_1407692 : Nat := 481881739659341088184099

theorem tailTrace_1407692 : CollatzResearch.WordTrace tailWord_1407692 prefixEnd_1407692 481881739659341088184099 := by
  unfold tailWord_1407692
  simp only [CollatzResearch.WordTrace]
  refine ⟨25671372608089886749160665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34228496810786515665547553 25671372608089886749160665)
  ·
    refine ⟨19253529456067415061870499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25671372608089886749160665 19253529456067415061870499)
    ·
      refine ⟨28880294184101122592805749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19253529456067415061870499 28880294184101122592805749)
      ·
        refine ⟨2707527579759480243075539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28880294184101122592805749 2707527579759480243075539)
        ·
          refine ⟨4061291369639220364613309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707527579759480243075539 4061291369639220364613309)
          ·
            refine ⟨1522984263614707636729991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4061291369639220364613309 1522984263614707636729991)
            ·
              refine ⟨2284476395422061455094987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522984263614707636729991 2284476395422061455094987)
              ·
                refine ⟨3426714593133092182642481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284476395422061455094987 3426714593133092182642481)
                ·
                  refine ⟨2570035944849819136981861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426714593133092182642481 2570035944849819136981861)
                  ·
                    refine ⟨481881739659341088184099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570035944849819136981861 481881739659341088184099)
                    ·
                      rfl

theorem cell22_1407692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_1407692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407692 prefixEnd_1407692 := by exact prefixLift 1407692
  have htrace : WordTrace (prefixWord ++ tailWord_1407692) baseStart_1407692 baseEnd_1407692 := by
    simpa [prefixWord, tailWord_1407692, baseEnd_1407692] using wordTrace_append hprefix tailTrace_1407692
  have hstable : (prefixWord ++ tailWord_1407692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407692).length < 2 ^ (prefixWord ++ tailWord_1407692).sum := by decide
  have hdescent : baseEnd_1407692 < baseStart_1407692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407765 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_1407765 : Nat := 118140960795 + 1407765 * 2 ^ 59
def prefixEnd_1407765 : Nat := 4983230072969 + 3 ^ 40 * 1407765 * 2
def baseEnd_1407765 : Nat := 481906729051193231108875

theorem tailTrace_1407765 : CollatzResearch.WordTrace tailWord_1407765 prefixEnd_1407765 481906729051193231108875 := by
  unfold tailWord_1407765
  simp only [CollatzResearch.WordTrace]
  refine ⟨51345407744915306965728749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34230271829943537977152499 51345407744915306965728749)
  ·
    refine ⟨19254527904343240112148281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51345407744915306965728749 19254527904343240112148281)
    ·
      refine ⟨14440895928257430084111211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19254527904343240112148281 14440895928257430084111211)
      ·
        refine ⟨21661343892386145126166817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14440895928257430084111211 21661343892386145126166817)
        ·
          refine ⟨16246007919289608844625113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21661343892386145126166817 16246007919289608844625113)
          ·
            refine ⟨12184505939467206633468835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16246007919289608844625113 12184505939467206633468835)
            ·
              refine ⟨18276758909200809950203253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12184505939467206633468835 18276758909200809950203253)
              ·
                refine ⟨1713446147737575932831555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18276758909200809950203253 1713446147737575932831555)
                ·
                  refine ⟨2570169221606363899247333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713446147737575932831555 2570169221606363899247333)
                  ·
                    refine ⟨481906729051193231108875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570169221606363899247333 481906729051193231108875)
                    ·
                      rfl

theorem cell22_1407765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_1407765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407765 prefixEnd_1407765 := by exact prefixLift 1407765
  have htrace : WordTrace (prefixWord ++ tailWord_1407765) baseStart_1407765 baseEnd_1407765 := by
    simpa [prefixWord, tailWord_1407765, baseEnd_1407765] using wordTrace_append hprefix tailTrace_1407765
  have hstable : (prefixWord ++ tailWord_1407765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407765).length < 2 ^ (prefixWord ++ tailWord_1407765).sum := by decide
  have hdescent : baseEnd_1407765 < baseStart_1407765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407773 : List Nat := [1, 4, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_1407773 : Nat := 118140960795 + 1407773 * 2 ^ 59
def prefixEnd_1407773 : Nat := 4983230072969 + 3 ^ 40 * 1407773 * 2
def baseEnd_1407773 : Nat := 481909467614683876908851

theorem tailTrace_1407773 : CollatzResearch.WordTrace tailWord_1407773 prefixEnd_1407773 481909467614683876908851 := by
  unfold tailWord_1407773
  simp only [CollatzResearch.WordTrace]
  refine ⟨51345699528886324332019973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34230466352590882888013315 51345699528886324332019973)
  ·
    refine ⟨9627318661666185812253745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51345699528886324332019973 9627318661666185812253745)
    ·
      refine ⟨7220488996249639359190309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9627318661666185812253745 7220488996249639359190309)
      ·
        refine ⟨1353841686796807379848183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7220488996249639359190309 1353841686796807379848183)
        ·
          refine ⟨2030762530195211069772275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353841686796807379848183 2030762530195211069772275)
          ·
            refine ⟨3046143795292816604658413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030762530195211069772275 3046143795292816604658413)
            ·
              refine ⟨1142303923234806226746905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3046143795292816604658413 1142303923234806226746905)
              ·
                refine ⟨856727942426104670060179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142303923234806226746905 856727942426104670060179)
                ·
                  refine ⟨1285091913639157005090269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856727942426104670060179 1285091913639157005090269)
                  ·
                    refine ⟨481909467614683876908851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285091913639157005090269 481909467614683876908851)
                    ·
                      rfl

theorem cell22_1407773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_1407773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407773 prefixEnd_1407773 := by exact prefixLift 1407773
  have htrace : WordTrace (prefixWord ++ tailWord_1407773) baseStart_1407773 baseEnd_1407773 := by
    simpa [prefixWord, tailWord_1407773, baseEnd_1407773] using wordTrace_append hprefix tailTrace_1407773
  have hstable : (prefixWord ++ tailWord_1407773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407773).length < 2 ^ (prefixWord ++ tailWord_1407773).sum := by decide
  have hdescent : baseEnd_1407773 < baseStart_1407773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407786 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_1407786 : Nat := 118140960795 + 1407786 * 2 ^ 59
def prefixEnd_1407786 : Nat := 4983230072969 + 3 ^ 40 * 1407786 * 2
def baseEnd_1407786 : Nat := 160637972593452058777937

theorem tailTrace_1407786 : CollatzResearch.WordTrace tailWord_1407786 prefixEnd_1407786 160637972593452058777937 := by
  unfold tailWord_1407786
  simp only [CollatzResearch.WordTrace]
  refine ⟨12836543419459806888060803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34230782451892818368162141 12836543419459806888060803)
  ·
    refine ⟨19254815129189710332091205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12836543419459806888060803 19254815129189710332091205)
    ·
      refine ⟨3610277836723070687267101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19254815129189710332091205 3610277836723070687267101)
      ·
        refine ⟨1353854188771151507725163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3610277836723070687267101 1353854188771151507725163)
        ·
          refine ⟨2030781283156727261587745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353854188771151507725163 2030781283156727261587745)
          ·
            refine ⟨1523085962367545446190809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2030781283156727261587745 1523085962367545446190809)
            ·
              refine ⟨1142314471775659084643107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523085962367545446190809 1142314471775659084643107)
              ·
                refine ⟨1713471707663488626964661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142314471775659084643107 1713471707663488626964661)
                ·
                  refine ⟨160637972593452058777937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1713471707663488626964661 160637972593452058777937)
                  ·
                    rfl

theorem cell22_1407786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_1407786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407786 prefixEnd_1407786 := by exact prefixLift 1407786
  have htrace : WordTrace (prefixWord ++ tailWord_1407786) baseStart_1407786 baseEnd_1407786 := by
    simpa [prefixWord, tailWord_1407786, baseEnd_1407786] using wordTrace_append hprefix tailTrace_1407786
  have hstable : (prefixWord ++ tailWord_1407786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407786).length < 2 ^ (prefixWord ++ tailWord_1407786).sum := by decide
  have hdescent : baseEnd_1407786 < baseStart_1407786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407825 : List Nat := [1, 2, 2, 1, 7, 9]
def baseStart_1407825 : Nat := 118140960795 + 1407825 * 2 ^ 59
def prefixEnd_1407825 : Nat := 4983230072969 + 3 ^ 40 * 1407825 * 2
def baseEnd_1407825 : Nat := 5949719361449050303811

theorem tailTrace_1407825 : CollatzResearch.WordTrace tailWord_1407825 prefixEnd_1407825 5949719361449050303811 := by
  unfold tailWord_1407825
  simp only [CollatzResearch.WordTrace]
  refine ⟨51347596124697937212912929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34231730749798624808608619 51347596124697937212912929)
  ·
    refine ⟨38510697093523452909684697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51347596124697937212912929 38510697093523452909684697)
    ·
      refine ⟨28883022820142589682263523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38510697093523452909684697 28883022820142589682263523)
      ·
        refine ⟨43324534230213884523395285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28883022820142589682263523 43324534230213884523395285)
        ·
          refine ⟨1015418771020637918517077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43324534230213884523395285 1015418771020637918517077)
          ·
            refine ⟨5949719361449050303811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1015418771020637918517077 5949719361449050303811)
            ·
              rfl

theorem cell22_1407825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 9].length) (baseStart_1407825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407825 prefixEnd_1407825 := by exact prefixLift 1407825
  have htrace : WordTrace (prefixWord ++ tailWord_1407825) baseStart_1407825 baseEnd_1407825 := by
    simpa [prefixWord, tailWord_1407825, baseEnd_1407825] using wordTrace_append hprefix tailTrace_1407825
  have hstable : (prefixWord ++ tailWord_1407825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407825).length < 2 ^ (prefixWord ++ tailWord_1407825).sum := by decide
  have hdescent : baseEnd_1407825 < baseStart_1407825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407857 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 3, 3]
def baseStart_1407857 : Nat := 118140960795 + 1407857 * 2 ^ 59
def prefixEnd_1407857 : Nat := 4983230072969 + 3 ^ 40 * 1407857 * 2
def baseEnd_1407857 : Nat := 481938222531335657808593

theorem tailTrace_1407857 : CollatzResearch.WordTrace tailWord_1407857 prefixEnd_1407857 481938222531335657808593 := by
  unfold tailWord_1407857
  simp only [CollatzResearch.WordTrace]
  refine ⟨51348763260582006678077825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34232508840388004452051883 51348763260582006678077825)
  ·
    refine ⟨38511572445436505008558369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51348763260582006678077825 38511572445436505008558369)
    ·
      refine ⟨28883679334077378756418777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38511572445436505008558369 28883679334077378756418777)
      ·
        refine ⟨21662759500558034067314083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28883679334077378756418777 21662759500558034067314083)
        ·
          refine ⟨32494139250837051100971125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21662759500558034067314083 32494139250837051100971125)
          ·
            refine ⟨3046325554765973540716043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32494139250837051100971125 3046325554765973540716043)
            ·
              refine ⟨4569488332148960311074065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046325554765973540716043 4569488332148960311074065)
              ·
                refine ⟨3427116249111720233305549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4569488332148960311074065 3427116249111720233305549)
                ·
                  refine ⟨1285168593416895087489581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3427116249111720233305549 1285168593416895087489581)
                  ·
                    refine ⟨481938222531335657808593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285168593416895087489581 481938222531335657808593)
                    ·
                      rfl

theorem cell22_1407857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_1407857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407857 prefixEnd_1407857 := by exact prefixLift 1407857
  have htrace : WordTrace (prefixWord ++ tailWord_1407857) baseStart_1407857 baseEnd_1407857 := by
    simpa [prefixWord, tailWord_1407857, baseEnd_1407857] using wordTrace_append hprefix tailTrace_1407857
  have hstable : (prefixWord ++ tailWord_1407857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407857).length < 2 ^ (prefixWord ++ tailWord_1407857).sum := by decide
  have hdescent : baseEnd_1407857 < baseStart_1407857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407930 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_1407930 : Nat := 118140960795 + 1407930 * 2 ^ 59
def prefixEnd_1407930 : Nat := 4983230072969 + 3 ^ 40 * 1407930 * 2
def baseEnd_1407930 : Nat := 481963211923187800733369

theorem tailTrace_1407930 : CollatzResearch.WordTrace tailWord_1407930 prefixEnd_1407930 481963211923187800733369 := by
  unfold tailWord_1407930
  simp only [CollatzResearch.WordTrace]
  refine ⟨12837856447329385036371311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34234283859545026763656829 12837856447329385036371311)
  ·
    refine ⟨19256784670994077554556967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12837856447329385036371311 19256784670994077554556967)
    ·
      refine ⟨28885177006491116331835451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19256784670994077554556967 28885177006491116331835451)
      ·
        refine ⟨43327765509736674497753177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28885177006491116331835451 43327765509736674497753177)
        ·
          refine ⟨32495824132302505873314883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43327765509736674497753177 32495824132302505873314883)
          ·
            refine ⟨48743736198453758809972325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32495824132302505873314883 48743736198453758809972325)
            ·
              refine ⟨9139450537210079776869811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48743736198453758809972325 9139450537210079776869811)
              ·
                refine ⟨13709175805815119665304717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9139450537210079776869811 13709175805815119665304717)
                ·
                  refine ⟨5140940927180669874489269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13709175805815119665304717 5140940927180669874489269)
                  ·
                    refine ⟨481963211923187800733369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5140940927180669874489269 481963211923187800733369)
                    ·
                      rfl

theorem cell22_1407930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_1407930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407930 prefixEnd_1407930 := by exact prefixLift 1407930
  have htrace : WordTrace (prefixWord ++ tailWord_1407930) baseStart_1407930 baseEnd_1407930 := by
    simpa [prefixWord, tailWord_1407930, baseEnd_1407930] using wordTrace_append hprefix tailTrace_1407930
  have hstable : (prefixWord ++ tailWord_1407930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407930).length < 2 ^ (prefixWord ++ tailWord_1407930).sum := by decide
  have hdescent : baseEnd_1407930 < baseStart_1407930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407942 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1407942 : Nat := 118140960795 + 1407942 * 2 ^ 59
def prefixEnd_1407942 : Nat := 4983230072969 + 3 ^ 40 * 1407942 * 2
def baseEnd_1407942 : Nat := 481967319768423769433333

theorem tailTrace_1407942 : CollatzResearch.WordTrace tailWord_1407942 prefixEnd_1407942 481967319768423769433333 := by
  unfold tailWord_1407942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604745733289814568591315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34234575643516044129948053 1604745733289814568591315)
  ·
    refine ⟨2407118599934721852886973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1604745733289814568591315 2407118599934721852886973)
    ·
      refine ⟨902669474975520694832615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2407118599934721852886973 902669474975520694832615)
      ·
        refine ⟨1354004212463281042248923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902669474975520694832615 1354004212463281042248923)
        ·
          refine ⟨2031006318694921563373385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354004212463281042248923 2031006318694921563373385)
          ·
            refine ⟨1523254739021191172530039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2031006318694921563373385 1523254739021191172530039)
            ·
              refine ⟨2284882108531786758795059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523254739021191172530039 2284882108531786758795059)
              ·
                refine ⟨3427323162797680138192589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284882108531786758795059 3427323162797680138192589)
                ·
                  refine ⟨1285246186049130051822221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3427323162797680138192589 1285246186049130051822221)
                  ·
                    refine ⟨481967319768423769433333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285246186049130051822221 481967319768423769433333)
                    ·
                      rfl

theorem cell22_1407942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1407942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407942 prefixEnd_1407942 := by exact prefixLift 1407942
  have htrace : WordTrace (prefixWord ++ tailWord_1407942) baseStart_1407942 baseEnd_1407942 := by
    simpa [prefixWord, tailWord_1407942, baseEnd_1407942] using wordTrace_append hprefix tailTrace_1407942
  have hstable : (prefixWord ++ tailWord_1407942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407942).length < 2 ^ (prefixWord ++ tailWord_1407942).sum := by decide
  have hdescent : baseEnd_1407942 < baseStart_1407942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407947 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 4, 3]
def baseStart_1407947 : Nat := 118140960795 + 1407947 * 2 ^ 59
def prefixEnd_1407947 : Nat := 4983230072969 + 3 ^ 40 * 1407947 * 2
def baseEnd_1407947 : Nat := 481969031370605423058317

theorem tailTrace_1407947 : CollatzResearch.WordTrace tailWord_1407947 prefixEnd_1407947 481969031370605423058317 := by
  unfold tailWord_1407947
  simp only [CollatzResearch.WordTrace]
  refine ⟨51352045830255952048854095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34234697220170634699236063 51352045830255952048854095)
  ·
    refine ⟨77028068745383928073281143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51352045830255952048854095 77028068745383928073281143)
    ·
      refine ⟨115542103118075892109921715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77028068745383928073281143 115542103118075892109921715)
      ·
        refine ⟨173313154677113838164882573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115542103118075892109921715 173313154677113838164882573)
        ·
          refine ⟨64992433003917689311830965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173313154677113838164882573 64992433003917689311830965)
          ·
            refine ⟨6093040594117283372984153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64992433003917689311830965 6093040594117283372984153)
            ·
              refine ⟨4569780445587962529738115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6093040594117283372984153 4569780445587962529738115)
              ·
                refine ⟨6854670668381943794607173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569780445587962529738115 6854670668381943794607173)
                ·
                  refine ⟨1285250750321614461488845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6854670668381943794607173 1285250750321614461488845)
                  ·
                    refine ⟨481969031370605423058317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285250750321614461488845 481969031370605423058317)
                    ·
                      rfl

theorem cell22_1407947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 3].length) (baseStart_1407947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407947 prefixEnd_1407947 := by exact prefixLift 1407947
  have htrace : WordTrace (prefixWord ++ tailWord_1407947) baseStart_1407947 baseEnd_1407947 := by
    simpa [prefixWord, tailWord_1407947, baseEnd_1407947] using wordTrace_append hprefix tailTrace_1407947
  have hstable : (prefixWord ++ tailWord_1407947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407947).length < 2 ^ (prefixWord ++ tailWord_1407947).sum := by decide
  have hdescent : baseEnd_1407947 < baseStart_1407947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407960 : List Nat := [2, 1, 2, 2, 2, 3, 1, 9]
def baseStart_1407960 : Nat := 118140960795 + 1407960 * 2 ^ 59
def prefixEnd_1407960 : Nat := 4983230072969 + 3 ^ 40 * 1407960 * 2
def baseEnd_1407960 : Nat := 53552609059586413609253

theorem tailTrace_1407960 : CollatzResearch.WordTrace tailWord_1407960 prefixEnd_1407960 53552609059586413609253 := by
  unfold tailWord_1407960
  simp only [CollatzResearch.WordTrace]
  refine ⟨25676259989604427634538667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34235013319472570179384889 25676259989604427634538667)
  ·
    refine ⟨38514389984406641451808001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25676259989604427634538667 38514389984406641451808001)
    ·
      refine ⟨28885792488304981088856001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38514389984406641451808001 28885792488304981088856001)
      ·
        refine ⟨21664344366228735816642001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28885792488304981088856001 21664344366228735816642001)
        ·
          refine ⟨16248258274671551862481501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21664344366228735816642001 16248258274671551862481501)
          ·
            refine ⟨6093096853001831948430563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16248258274671551862481501 6093096853001831948430563)
            ·
              refine ⟨9139645279502747922645845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093096853001831948430563 9139645279502747922645845)
              ·
                refine ⟨53552609059586413609253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9139645279502747922645845 53552609059586413609253)
                ·
                  rfl

theorem cell22_1407960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 9].length) (baseStart_1407960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407960 prefixEnd_1407960 := by exact prefixLift 1407960
  have htrace : WordTrace (prefixWord ++ tailWord_1407960) baseStart_1407960 baseEnd_1407960 := by
    simpa [prefixWord, tailWord_1407960, baseEnd_1407960] using wordTrace_append hprefix tailTrace_1407960
  have hstable : (prefixWord ++ tailWord_1407960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407960).length < 2 ^ (prefixWord ++ tailWord_1407960).sum := by decide
  have hdescent : baseEnd_1407960 < baseStart_1407960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407998 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1407998 : Nat := 118140960795 + 1407998 * 2 ^ 59
def prefixEnd_1407998 : Nat := 4983230072969 + 3 ^ 40 * 1407998 * 2
def baseEnd_1407998 : Nat := 481986489712858290033161

theorem tailTrace_1407998 : CollatzResearch.WordTrace tailWord_1407998 prefixEnd_1407998 481986489712858290033161 := by
  unfold tailWord_1407998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419238244133898469870081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34235937302047458505973765 6419238244133898469870081)
  ·
    refine ⟨4814428683100423852402561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6419238244133898469870081 4814428683100423852402561)
    ·
      refine ⟨3610821512325317889301921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4814428683100423852402561 3610821512325317889301921)
      ·
        refine ⟨2708116134243988416976441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3610821512325317889301921 2708116134243988416976441)
        ·
          refine ⟨2031087100682991312732331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2708116134243988416976441 2031087100682991312732331)
          ·
            refine ⟨3046630651024486969098497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031087100682991312732331 3046630651024486969098497)
            ·
              refine ⟨2284972988268365226823873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046630651024486969098497 2284972988268365226823873)
              ·
                refine ⟨1713729741201273920117905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284972988268365226823873 1713729741201273920117905)
                ·
                  refine ⟨1285297305900955440088429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1713729741201273920117905 1285297305900955440088429)
                  ·
                    refine ⟨481986489712858290033161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285297305900955440088429 481986489712858290033161)
                    ·
                      rfl

theorem cell22_1407998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1407998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1407998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1407998 prefixEnd_1407998 := by exact prefixLift 1407998
  have htrace : WordTrace (prefixWord ++ tailWord_1407998) baseStart_1407998 baseEnd_1407998 := by
    simpa [prefixWord, tailWord_1407998, baseEnd_1407998] using wordTrace_append hprefix tailTrace_1407998
  have hstable : (prefixWord ++ tailWord_1407998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407998).length < 2 ^ (prefixWord ++ tailWord_1407998).sum := by decide
  have hdescent : baseEnd_1407998 < baseStart_1407998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408054 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1408054 : Nat := 118140960795 + 1408054 * 2 ^ 59
def prefixEnd_1408054 : Nat := 4983230072969 + 3 ^ 40 * 1408054 * 2
def baseEnd_1408054 : Nat := 482005659657292810632989

theorem tailTrace_1408054 : CollatzResearch.WordTrace tailWord_1408054 prefixEnd_1408054 482005659657292810632989 := by
  unfold tailWord_1408054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3209746777554269332687451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34237298960578872881999477 3209746777554269332687451)
  ·
    refine ⟨4814620166331403999031177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3209746777554269332687451 4814620166331403999031177)
    ·
      refine ⟨3610965124748552999273383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4814620166331403999031177 3610965124748552999273383)
      ·
        refine ⟨5416447687122829498910075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3610965124748552999273383 5416447687122829498910075)
        ·
          refine ⟨8124671530684244248365113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5416447687122829498910075 8124671530684244248365113)
          ·
            refine ⟨6093503648013183186273835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8124671530684244248365113 6093503648013183186273835)
            ·
              refine ⟨9140255472019774779410753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093503648013183186273835 9140255472019774779410753)
              ·
                refine ⟨6855191604014831084558065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9140255472019774779410753 6855191604014831084558065)
                ·
                  refine ⟨5141393703011123313418549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6855191604014831084558065 5141393703011123313418549)
                  ·
                    refine ⟨482005659657292810632989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5141393703011123313418549 482005659657292810632989)
                    ·
                      rfl

theorem cell22_1408054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1408054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408054 prefixEnd_1408054 := by exact prefixLift 1408054
  have htrace : WordTrace (prefixWord ++ tailWord_1408054) baseStart_1408054 baseEnd_1408054 := by
    simpa [prefixWord, tailWord_1408054, baseEnd_1408054] using wordTrace_append hprefix tailTrace_1408054
  have hstable : (prefixWord ++ tailWord_1408054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408054).length < 2 ^ (prefixWord ++ tailWord_1408054).sum := by decide
  have hdescent : baseEnd_1408054 < baseStart_1408054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408067 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 6]
def baseStart_1408067 : Nat := 118140960795 + 1408067 * 2 ^ 59
def prefixEnd_1408067 : Nat := 4983230072969 + 3 ^ 40 * 1408067 * 2
def baseEnd_1408067 : Nat := 160670036607655036685983

theorem tailTrace_1408067 : CollatzResearch.WordTrace tailWord_1408067 prefixEnd_1408067 160670036607655036685983 := by
  unfold tailWord_1408067
  simp only [CollatzResearch.WordTrace]
  refine ⟨51356422589821212543222455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34237615059880808362148303 51356422589821212543222455)
  ·
    refine ⟨77034633884731818814833683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51356422589821212543222455 77034633884731818814833683)
    ·
      refine ⟨115551950827097728222250525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77034633884731818814833683 115551950827097728222250525)
      ·
        refine ⟨43331981560161648083343947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115551950827097728222250525 43331981560161648083343947)
        ·
          refine ⟨64997972340242472125015921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43331981560161648083343947 64997972340242472125015921)
          ·
            refine ⟨48748479255181854093761941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64997972340242472125015921 48748479255181854093761941)
            ·
              refine ⟨2285084965086649410645091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48748479255181854093761941 2285084965086649410645091)
              ·
                refine ⟨3427627447629974115967637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2285084965086649410645091 3427627447629974115967637)
                ·
                  refine ⟨160670036607655036685983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3427627447629974115967637 160670036607655036685983)
                  ·
                    rfl

theorem cell22_1408067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 6].length) (baseStart_1408067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408067 prefixEnd_1408067 := by exact prefixLift 1408067
  have htrace : WordTrace (prefixWord ++ tailWord_1408067) baseStart_1408067 baseEnd_1408067 := by
    simpa [prefixWord, tailWord_1408067, baseEnd_1408067] using wordTrace_append hprefix tailTrace_1408067
  have hstable : (prefixWord ++ tailWord_1408067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408067).length < 2 ^ (prefixWord ++ tailWord_1408067).sum := by decide
  have hdescent : baseEnd_1408067 < baseStart_1408067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408097 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_1408097 : Nat := 118140960795 + 1408097 * 2 ^ 59
def prefixEnd_1408097 : Nat := 4983230072969 + 3 ^ 40 * 1408097 * 2
def baseEnd_1408097 : Nat := 482020379436055031807857

theorem tailTrace_1408097 : CollatzResearch.WordTrace tailWord_1408097 prefixEnd_1408097 482020379436055031807857 := by
  unfold tailWord_1408097
  simp only [CollatzResearch.WordTrace]
  refine ⟨51357516779712527666814545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34238344519808351777876363 51357516779712527666814545)
  ·
    refine ⟨38518137584784395750110909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51357516779712527666814545 38518137584784395750110909)
    ·
      refine ⟨14444301594294148406291591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38518137584784395750110909 14444301594294148406291591)
      ·
        refine ⟨21666452391441222609437387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14444301594294148406291591 21666452391441222609437387)
        ·
          refine ⟨32499678587161833914156081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21666452391441222609437387 32499678587161833914156081)
          ·
            refine ⟨24374758940371375435617061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32499678587161833914156081 24374758940371375435617061)
            ·
              refine ⟨4570267301319632894178199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24374758940371375435617061 4570267301319632894178199)
              ·
                refine ⟨6855400951979449341267299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570267301319632894178199 6855400951979449341267299)
                ·
                  refine ⟨10283101427969174011900949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6855400951979449341267299 10283101427969174011900949)
                  ·
                    refine ⟨482020379436055031807857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10283101427969174011900949 482020379436055031807857)
                    ·
                      rfl

theorem cell22_1408097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_1408097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408097 prefixEnd_1408097 := by exact prefixLift 1408097
  have htrace : WordTrace (prefixWord ++ tailWord_1408097) baseStart_1408097 baseEnd_1408097 := by
    simpa [prefixWord, tailWord_1408097, baseEnd_1408097] using wordTrace_append hprefix tailTrace_1408097
  have hstable : (prefixWord ++ tailWord_1408097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408097).length < 2 ^ (prefixWord ++ tailWord_1408097).sum := by decide
  have hdescent : baseEnd_1408097 < baseStart_1408097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408114 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_1408114 : Nat := 118140960795 + 1408114 * 2 ^ 59
def prefixEnd_1408114 : Nat := 4983230072969 + 3 ^ 40 * 1408114 * 2
def baseEnd_1408114 : Nat := 482026198883472654132805

theorem tailTrace_1408114 : CollatzResearch.WordTrace tailWord_1408114 prefixEnd_1408114 482026198883472654132805 := by
  unfold tailWord_1408114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12839534205162734892545849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34238757880433959713455597 12839534205162734892545849)
  ·
    refine ⟨9629650653872051169409387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12839534205162734892545849 9629650653872051169409387)
    ·
      refine ⟨14444475980808076754114081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9629650653872051169409387 14444475980808076754114081)
      ·
        refine ⟨10833356985606057565585561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14444475980808076754114081 10833356985606057565585561)
        ·
          refine ⟨8125017739204543174189171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10833356985606057565585561 8125017739204543174189171)
          ·
            refine ⟨12187526608806814761283757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125017739204543174189171 12187526608806814761283757)
            ·
              refine ⟨4570322478302555535481409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12187526608806814761283757 4570322478302555535481409)
              ·
                refine ⟨3427741858726916651611057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570322478302555535481409 3427741858726916651611057)
                ·
                  refine ⟨2570806394045187488708293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3427741858726916651611057 2570806394045187488708293)
                  ·
                    refine ⟨482026198883472654132805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570806394045187488708293 482026198883472654132805)
                    ·
                      rfl

theorem cell22_1408114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_1408114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408114 prefixEnd_1408114 := by exact prefixLift 1408114
  have htrace : WordTrace (prefixWord ++ tailWord_1408114) baseStart_1408114 baseEnd_1408114 := by
    simpa [prefixWord, tailWord_1408114, baseEnd_1408114] using wordTrace_append hprefix tailTrace_1408114
  have hstable : (prefixWord ++ tailWord_1408114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408114).length < 2 ^ (prefixWord ++ tailWord_1408114).sum := by decide
  have hdescent : baseEnd_1408114 < baseStart_1408114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408118 : List Nat := [5, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_1408118 : Nat := 118140960795 + 1408118 * 2 ^ 59
def prefixEnd_1408118 : Nat := 4983230072969 + 3 ^ 40 * 1408118 * 2
def baseEnd_1408118 : Nat := 160675856055072659010931

theorem tailTrace_1408118 : CollatzResearch.WordTrace tailWord_1408118 prefixEnd_1408118 160675856055072659010931 := by
  unfold tailWord_1408118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3209892669539778015833063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34238855141757632168886005 3209892669539778015833063)
  ·
    refine ⟨4814839004309667023749595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3209892669539778015833063 4814839004309667023749595)
    ·
      refine ⟨7222258506464500535624393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4814839004309667023749595 7222258506464500535624393)
      ·
        refine ⟨5416693879848375401718295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7222258506464500535624393 5416693879848375401718295)
        ·
          refine ⟨8125040819772563102577443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5416693879848375401718295 8125040819772563102577443)
          ·
            refine ⟨12187561229658844653866165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125040819772563102577443 12187561229658844653866165)
            ·
              refine ⟨1142583865280516686299953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12187561229658844653866165 1142583865280516686299953)
              ·
                refine ⟨856937898960387514724965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142583865280516686299953 856937898960387514724965)
                ·
                  refine ⟨160675856055072659010931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 856937898960387514724965 160675856055072659010931)
                  ·
                    rfl

theorem cell22_1408118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_1408118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408118 prefixEnd_1408118 := by exact prefixLift 1408118
  have htrace : WordTrace (prefixWord ++ tailWord_1408118) baseStart_1408118 baseEnd_1408118 := by
    simpa [prefixWord, tailWord_1408118, baseEnd_1408118] using wordTrace_append hprefix tailTrace_1408118
  have hstable : (prefixWord ++ tailWord_1408118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408118).length < 2 ^ (prefixWord ++ tailWord_1408118).sum := by decide
  have hdescent : baseEnd_1408118 < baseStart_1408118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408129 : List Nat := [1, 2, 4, 2, 2, 2, 2, 7]
def baseStart_1408129 : Nat := 118140960795 + 1408129 * 2 ^ 59
def prefixEnd_1408129 : Nat := 4983230072969 + 3 ^ 40 * 1408129 * 2
def baseEnd_1408129 : Nat := 53559037076668623889751

theorem tailTrace_1408129 : CollatzResearch.WordTrace tailWord_1408129 prefixEnd_1408129 53559037076668623889751 := by
  unfold tailWord_1408129
  simp only [CollatzResearch.WordTrace]
  refine ⟨51358683915596597131979441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34239122610397731421319627 51358683915596597131979441)
  ·
    refine ⟨38519012936697447848984581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51358683915596597131979441 38519012936697447848984581)
    ·
      refine ⟨7222314925630771471684609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38519012936697447848984581 7222314925630771471684609)
      ·
        refine ⟨5416736194223078603763457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7222314925630771471684609 5416736194223078603763457)
        ·
          refine ⟨4062552145667308952822593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5416736194223078603763457 4062552145667308952822593)
          ·
            refine ⟨3046914109250481714616945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4062552145667308952822593 3046914109250481714616945)
            ·
              refine ⟨2285185581937861285962709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046914109250481714616945 2285185581937861285962709)
              ·
                refine ⟨53559037076668623889751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2285185581937861285962709 53559037076668623889751)
                ·
                  rfl

theorem cell22_1408129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 7].length) (baseStart_1408129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408129 prefixEnd_1408129 := by exact prefixLift 1408129
  have htrace : WordTrace (prefixWord ++ tailWord_1408129) baseStart_1408129 baseEnd_1408129 := by
    simpa [prefixWord, tailWord_1408129, baseEnd_1408129] using wordTrace_append hprefix tailTrace_1408129
  have hstable : (prefixWord ++ tailWord_1408129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408129).length < 2 ^ (prefixWord ++ tailWord_1408129).sum := by decide
  have hdescent : baseEnd_1408129 < baseStart_1408129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408178 : List Nat := [3, 2, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_1408178 : Nat := 118140960795 + 1408178 * 2 ^ 59
def prefixEnd_1408178 : Nat := 4983230072969 + 3 ^ 40 * 1408178 * 2
def baseEnd_1408178 : Nat := 482048107391397820532609

theorem tailTrace_1408178 : CollatzResearch.WordTrace tailWord_1408178 prefixEnd_1408178 482048107391397820532609 := by
  unfold tailWord_1408178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12840117773104769625128297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34240314061612719000342125 12840117773104769625128297)
  ·
    refine ⟨9630088329828577218846223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12840117773104769625128297 9630088329828577218846223)
    ·
      refine ⟨14445132494742865828269335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9630088329828577218846223 14445132494742865828269335)
      ·
        refine ⟨21667698742114298742404003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14445132494742865828269335 21667698742114298742404003)
        ·
          refine ⟨32501548113171448113606005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21667698742114298742404003 32501548113171448113606005)
          ·
            refine ⟨3047020135609823260650563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32501548113171448113606005 3047020135609823260650563)
            ·
              refine ⟨4570530203414734890975845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047020135609823260650563 4570530203414734890975845)
              ·
                refine ⟨856974413140262792057971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4570530203414734890975845 856974413140262792057971)
                ·
                  refine ⟨1285461619710394188086957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856974413140262792057971 1285461619710394188086957)
                  ·
                    refine ⟨482048107391397820532609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285461619710394188086957 482048107391397820532609)
                    ·
                      rfl

theorem cell22_1408178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_1408178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408178 prefixEnd_1408178 := by exact prefixLift 1408178
  have htrace : WordTrace (prefixWord ++ tailWord_1408178) baseStart_1408178 baseEnd_1408178 := by
    simpa [prefixWord, tailWord_1408178, baseEnd_1408178] using wordTrace_append hprefix tailTrace_1408178
  have hstable : (prefixWord ++ tailWord_1408178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408178).length < 2 ^ (prefixWord ++ tailWord_1408178).sum := by decide
  have hdescent : baseEnd_1408178 < baseStart_1408178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408212 : List Nat := [2, 4, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_1408212 : Nat := 118140960795 + 1408212 * 2 ^ 59
def prefixEnd_1408212 : Nat := 4983230072969 + 3 ^ 40 * 1408212 * 2
def baseEnd_1408212 : Nat := 482059746286233065182505

theorem tailTrace_1408212 : CollatzResearch.WordTrace tailWord_1408212 prefixEnd_1408212 482059746286233065182505 := by
  unfold tailWord_1408212
  simp only [CollatzResearch.WordTrace]
  refine ⟨25680855587147951153625445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34241140782863934871500593 25680855587147951153625445)
  ·
    refine ⟨4815160422590240841304771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25680855587147951153625445 4815160422590240841304771)
    ·
      refine ⟨7222740633885361261957157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4815160422590240841304771 7222740633885361261957157)
      ·
        refine ⟨1354263868853505236616967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7222740633885361261957157 1354263868853505236616967)
        ·
          refine ⟨2031395803280257854925451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354263868853505236616967 2031395803280257854925451)
          ·
            refine ⟨3047093704920386782388177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031395803280257854925451 3047093704920386782388177)
            ·
              refine ⟨2285320278690290086791133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3047093704920386782388177 2285320278690290086791133)
              ·
                refine ⟨856995104508858782546675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2285320278690290086791133 856995104508858782546675)
                ·
                  refine ⟨1285492656763288173820013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856995104508858782546675 1285492656763288173820013)
                  ·
                    refine ⟨482059746286233065182505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285492656763288173820013 482059746286233065182505)
                    ·
                      rfl

theorem cell22_1408212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_1408212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408212 prefixEnd_1408212 := by exact prefixLift 1408212
  have htrace : WordTrace (prefixWord ++ tailWord_1408212) baseStart_1408212 baseEnd_1408212 := by
    simpa [prefixWord, tailWord_1408212, baseEnd_1408212] using wordTrace_append hprefix tailTrace_1408212
  have hstable : (prefixWord ++ tailWord_1408212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408212).length < 2 ^ (prefixWord ++ tailWord_1408212).sum := by decide
  have hdescent : baseEnd_1408212 < baseStart_1408212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408236 : List Nat := [2, 2, 1, 1, 2, 4, 2, 4, 4]
def baseStart_1408236 : Nat := 118140960795 + 1408236 * 2 ^ 59
def prefixEnd_1408236 : Nat := 4983230072969 + 3 ^ 40 * 1408236 * 2
def baseEnd_1408236 : Nat := 160689320658901667527477

theorem tailTrace_1408236 : CollatzResearch.WordTrace tailWord_1408236 prefixEnd_1408236 160689320658901667527477 := by
  unfold tailWord_1408236
  simp only [CollatzResearch.WordTrace]
  refine ⟨25681293263104477203062281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34241724350805969604083041 25681293263104477203062281)
  ·
    refine ⟨19260969947328357902296711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25681293263104477203062281 19260969947328357902296711)
    ·
      refine ⟨28891454920992536853445067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19260969947328357902296711 28891454920992536853445067)
      ·
        refine ⟨43337182381488805280167601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28891454920992536853445067 43337182381488805280167601)
        ·
          refine ⟨32502886786116603960125701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43337182381488805280167601 32502886786116603960125701)
          ·
            refine ⟨6094291272396863242523569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32502886786116603960125701 6094291272396863242523569)
            ·
              refine ⟨4570718454297647431892677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6094291272396863242523569 4570718454297647431892677)
              ·
                refine ⟨857009710180808893479877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4570718454297647431892677 857009710180808893479877)
                ·
                  refine ⟨160689320658901667527477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857009710180808893479877 160689320658901667527477)
                  ·
                    rfl

theorem cell22_1408236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_1408236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408236 prefixEnd_1408236 := by exact prefixLift 1408236
  have htrace : WordTrace (prefixWord ++ tailWord_1408236) baseStart_1408236 baseEnd_1408236 := by
    simpa [prefixWord, tailWord_1408236, baseEnd_1408236] using wordTrace_append hprefix tailTrace_1408236
  have hstable : (prefixWord ++ tailWord_1408236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408236).length < 2 ^ (prefixWord ++ tailWord_1408236).sum := by decide
  have hdescent : baseEnd_1408236 < baseStart_1408236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408356 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_1408356 : Nat := 118140960795 + 1408356 * 2 ^ 59
def prefixEnd_1408356 : Nat := 4983230072969 + 3 ^ 40 * 1408356 * 2
def baseEnd_1408356 : Nat := 482109040429064689582063

theorem tailTrace_1408356 : CollatzResearch.WordTrace tailWord_1408356 prefixEnd_1408356 482109040429064689582063 := by
  unfold tailWord_1408356
  simp only [CollatzResearch.WordTrace]
  refine ⟨25683481642887107450246461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34244642190516143266995281 25683481642887107450246461)
  ·
    refine ⟨9631305616082665293842423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25683481642887107450246461 9631305616082665293842423)
    ·
      refine ⟨14446958424123997940763635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9631305616082665293842423 14446958424123997940763635)
      ·
        refine ⟨21670437636185996911145453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14446958424123997940763635 21670437636185996911145453)
        ·
          refine ⟨8126414113569748841679545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21670437636185996911145453 8126414113569748841679545)
          ·
            refine ⟨6094810585177311631259659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8126414113569748841679545 6094810585177311631259659)
            ·
              refine ⟨9142215877765967446889489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6094810585177311631259659 9142215877765967446889489)
              ·
                refine ⟨6856661908324475585167117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9142215877765967446889489 6856661908324475585167117)
                ·
                  refine ⟨2571248215621678344437669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6856661908324475585167117 2571248215621678344437669)
                  ·
                    refine ⟨482109040429064689582063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2571248215621678344437669 482109040429064689582063)
                    ·
                      rfl

theorem cell22_1408356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_1408356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408356 prefixEnd_1408356 := by exact prefixLift 1408356
  have htrace : WordTrace (prefixWord ++ tailWord_1408356) baseStart_1408356 baseEnd_1408356 := by
    simpa [prefixWord, tailWord_1408356, baseEnd_1408356] using wordTrace_append hprefix tailTrace_1408356
  have hstable : (prefixWord ++ tailWord_1408356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408356).length < 2 ^ (prefixWord ++ tailWord_1408356).sum := by decide
  have hdescent : baseEnd_1408356 < baseStart_1408356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408388 : List Nat := [2, 3, 2, 1, 1, 3, 1, 5, 4]
def baseStart_1408388 : Nat := 118140960795 + 1408388 * 2 ^ 59
def prefixEnd_1408388 : Nat := 4983230072969 + 3 ^ 40 * 1408388 * 2
def baseEnd_1408388 : Nat := 160706664894342424260655

theorem tailTrace_1408388 : CollatzResearch.WordTrace tailWord_1408388 prefixEnd_1408388 160706664894342424260655 := by
  unfold tailWord_1408388
  simp only [CollatzResearch.WordTrace]
  refine ⟨25684065210829142182828909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34245420281105522910438545 25684065210829142182828909)
  ·
    refine ⟨9631524454060928318560841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25684065210829142182828909 9631524454060928318560841)
    ·
      refine ⟨7223643340545696238920631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9631524454060928318560841 7223643340545696238920631)
      ·
        refine ⟨10835465010818544358380947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7223643340545696238920631 10835465010818544358380947)
        ·
          refine ⟨16253197516227816537571421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10835465010818544358380947 16253197516227816537571421)
          ·
            refine ⟨6094949068585431201589283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16253197516227816537571421 6094949068585431201589283)
            ·
              refine ⟨9142423602878146802383925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6094949068585431201589283 9142423602878146802383925)
              ·
                refine ⟨857102212769826262723493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9142423602878146802383925 857102212769826262723493)
                ·
                  refine ⟨160706664894342424260655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857102212769826262723493 160706664894342424260655)
                  ·
                    rfl

theorem cell22_1408388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_1408388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408388 prefixEnd_1408388 := by exact prefixLift 1408388
  have htrace : WordTrace (prefixWord ++ tailWord_1408388) baseStart_1408388 baseEnd_1408388 := by
    simpa [prefixWord, tailWord_1408388, baseEnd_1408388] using wordTrace_append hprefix tailTrace_1408388
  have hstable : (prefixWord ++ tailWord_1408388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408388).length < 2 ^ (prefixWord ++ tailWord_1408388).sum := by decide
  have hdescent : baseEnd_1408388 < baseStart_1408388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408446 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1408446 : Nat := 118140960795 + 1408446 * 2 ^ 59
def prefixEnd_1408446 : Nat := 4983230072969 + 3 ^ 40 * 1408446 * 2
def baseEnd_1408446 : Nat := 482139849268334454831787

theorem tailTrace_1408446 : CollatzResearch.WordTrace tailWord_1408446 prefixEnd_1408446 482139849268334454831787 := by
  unfold tailWord_1408446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6421280731931020033908649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34246830570298773514179461 6421280731931020033908649)
  ·
    refine ⟨4815960548948265025431487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6421280731931020033908649 4815960548948265025431487)
    ·
      refine ⟨7223940823422397538147231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4815960548948265025431487 7223940823422397538147231)
      ·
        refine ⟨10835911235133596307220847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7223940823422397538147231 10835911235133596307220847)
        ·
          refine ⟨16253866852700394460831271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10835911235133596307220847 16253866852700394460831271)
          ·
            refine ⟨24380800279050591691246907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16253866852700394460831271 24380800279050591691246907)
            ·
              refine ⟨36571200418575887536870361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24380800279050591691246907 36571200418575887536870361)
              ·
                refine ⟨27428400313931915652652771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36571200418575887536870361 27428400313931915652652771)
                ·
                  refine ⟨41142600470897873478979157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27428400313931915652652771 41142600470897873478979157)
                  ·
                    refine ⟨482139849268334454831787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41142600470897873478979157 482139849268334454831787)
                    ·
                      rfl

theorem cell22_1408446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1408446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408446 prefixEnd_1408446 := by exact prefixLift 1408446
  have htrace : WordTrace (prefixWord ++ tailWord_1408446) baseStart_1408446 baseEnd_1408446 := by
    simpa [prefixWord, tailWord_1408446, baseEnd_1408446] using wordTrace_append hprefix tailTrace_1408446
  have hstable : (prefixWord ++ tailWord_1408446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408446).length < 2 ^ (prefixWord ++ tailWord_1408446).sum := by decide
  have hdescent : baseEnd_1408446 < baseStart_1408446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408508 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_1408508 : Nat := 118140960795 + 1408508 * 2 ^ 59
def prefixEnd_1408508 : Nat := 4983230072969 + 3 ^ 40 * 1408508 * 2
def baseEnd_1408508 : Nat := 482161073135386959781597

theorem tailTrace_1408508 : CollatzResearch.WordTrace tailWord_1408508 prefixEnd_1408508 482161073135386959781597 := by
  unfold tailWord_1408508
  simp only [CollatzResearch.WordTrace]
  refine ⟨25686253590611772430013089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34248338120815696573350785 25686253590611772430013089)
  ·
    refine ⟨19264690192958829322509817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25686253590611772430013089 19264690192958829322509817)
    ·
      refine ⟨14448517644719121991882363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19264690192958829322509817 14448517644719121991882363)
      ·
        refine ⟨21672776467078682987823545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14448517644719121991882363 21672776467078682987823545)
        ·
          refine ⟨16254582350309012240867659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21672776467078682987823545 16254582350309012240867659)
          ·
            refine ⟨24381873525463518361301489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16254582350309012240867659 24381873525463518361301489)
            ·
              refine ⟨18286405144097638770976117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24381873525463518361301489 18286405144097638770976117)
              ·
                refine ⟨1714350482259153634779011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18286405144097638770976117 1714350482259153634779011)
                ·
                  refine ⟨2571525723388730452168517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714350482259153634779011 2571525723388730452168517)
                  ·
                    refine ⟨482161073135386959781597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2571525723388730452168517 482161073135386959781597)
                    ·
                      rfl

theorem cell22_1408508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_1408508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408508 prefixEnd_1408508 := by exact prefixLift 1408508
  have htrace : WordTrace (prefixWord ++ tailWord_1408508) baseStart_1408508 baseEnd_1408508 := by
    simpa [prefixWord, tailWord_1408508, baseEnd_1408508] using wordTrace_append hprefix tailTrace_1408508
  have hstable : (prefixWord ++ tailWord_1408508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408508).length < 2 ^ (prefixWord ++ tailWord_1408508).sum := by decide
  have hdescent : baseEnd_1408508 < baseStart_1408508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408516 : List Nat := [2, 3, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_1408516 : Nat := 118140960795 + 1408516 * 2 ^ 59
def prefixEnd_1408516 : Nat := 4983230072969 + 3 ^ 40 * 1408516 * 2
def baseEnd_1408516 : Nat := 482163811698877605581573

theorem tailTrace_1408516 : CollatzResearch.WordTrace tailWord_1408516 prefixEnd_1408516 482163811698877605581573 := by
  unfold tailWord_1408516
  simp only [CollatzResearch.WordTrace]
  refine ⟨25686399482597281113158701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34248532643463041484211601 25686399482597281113158701)
  ·
    refine ⟨9632399805973980417434513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25686399482597281113158701 9632399805973980417434513)
    ·
      refine ⟨7224299854480485313075885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9632399805973980417434513 7224299854480485313075885)
      ·
        refine ⟨2709112445430181992403457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7224299854480485313075885 2709112445430181992403457)
        ·
          refine ⟨2031834334072636494302593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2709112445430181992403457 2031834334072636494302593)
          ·
            refine ⟨1523875750554477370726945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2031834334072636494302593 1523875750554477370726945)
            ·
              refine ⟨1142906812915858028045209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523875750554477370726945 1142906812915858028045209)
              ·
                refine ⟨857180109686893521033907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142906812915858028045209 857180109686893521033907)
                ·
                  refine ⟨1285770164530340281550861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857180109686893521033907 1285770164530340281550861)
                  ·
                    refine ⟨482163811698877605581573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285770164530340281550861 482163811698877605581573)
                    ·
                      rfl

theorem cell22_1408516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_1408516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408516 prefixEnd_1408516 := by exact prefixLift 1408516
  have htrace : WordTrace (prefixWord ++ tailWord_1408516) baseStart_1408516 baseEnd_1408516 := by
    simpa [prefixWord, tailWord_1408516, baseEnd_1408516] using wordTrace_append hprefix tailTrace_1408516
  have hstable : (prefixWord ++ tailWord_1408516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408516).length < 2 ^ (prefixWord ++ tailWord_1408516).sum := by decide
  have hdescent : baseEnd_1408516 < baseStart_1408516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408521 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_1408521 : Nat := 118140960795 + 1408521 * 2 ^ 59
def prefixEnd_1408521 : Nat := 4983230072969 + 3 ^ 40 * 1408521 * 2
def baseEnd_1408521 : Nat := 482165523301059259206557

theorem tailTrace_1408521 : CollatzResearch.WordTrace tailWord_1408521 prefixEnd_1408521 482165523301059259206557 := by
  unfold tailWord_1408521
  simp only [CollatzResearch.WordTrace]
  refine ⟨51372981330176448080249417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34248654220117632053499611 51372981330176448080249417)
  ·
    refine ⟨38529735997632336060187063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51372981330176448080249417 38529735997632336060187063)
    ·
      refine ⟨57794603996448504090280595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38529735997632336060187063 57794603996448504090280595)
      ·
        refine ⟨86691905994672756135420893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57794603996448504090280595 86691905994672756135420893)
        ·
          refine ⟨32509464748002283550782835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86691905994672756135420893 32509464748002283550782835)
          ·
            refine ⟨48764197122003425326174253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32509464748002283550782835 48764197122003425326174253)
            ·
              refine ⟨18286573920751284497315345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48764197122003425326174253 18286573920751284497315345)
              ·
                refine ⟨13714930440563463372986509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18286573920751284497315345 13714930440563463372986509)
                ·
                  refine ⟨5143098915211298764869941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13714930440563463372986509 5143098915211298764869941)
                  ·
                    refine ⟨482165523301059259206557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5143098915211298764869941 482165523301059259206557)
                    ·
                      rfl

theorem cell22_1408521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_1408521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408521 prefixEnd_1408521 := by exact prefixLift 1408521
  have htrace : WordTrace (prefixWord ++ tailWord_1408521) baseStart_1408521 baseEnd_1408521 := by
    simpa [prefixWord, tailWord_1408521, baseEnd_1408521] using wordTrace_append hprefix tailTrace_1408521
  have hstable : (prefixWord ++ tailWord_1408521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408521).length < 2 ^ (prefixWord ++ tailWord_1408521).sum := by decide
  have hdescent : baseEnd_1408521 < baseStart_1408521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408538 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_1408538 : Nat := 118140960795 + 1408538 * 2 ^ 59
def prefixEnd_1408538 : Nat := 4983230072969 + 3 ^ 40 * 1408538 * 2
def baseEnd_1408538 : Nat := 482171342748476881531505

theorem tailTrace_1408538 : CollatzResearch.WordTrace tailWord_1408538 prefixEnd_1408538 482171342748476881531505 := by
  unfold tailWord_1408538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843400342778714995904567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34249067580743239989078845 12843400342778714995904567)
  ·
    refine ⟨19265100514168072493856851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12843400342778714995904567 19265100514168072493856851)
    ·
      refine ⟨28897650771252108740785277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19265100514168072493856851 28897650771252108740785277)
      ·
        refine ⟨10836619039219540777794479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28897650771252108740785277 10836619039219540777794479)
        ·
          refine ⟨16254928558829311166691719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10836619039219540777794479 16254928558829311166691719)
          ·
            refine ⟨24382392838243966750037579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16254928558829311166691719 24382392838243966750037579)
            ·
              refine ⟨36573589257365950125056369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24382392838243966750037579 36573589257365950125056369)
              ·
                refine ⟨27430191943024462593792277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36573589257365950125056369 27430191943024462593792277)
                ·
                  refine ⟨1285790247329271684084013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27430191943024462593792277 1285790247329271684084013)
                  ·
                    refine ⟨482171342748476881531505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285790247329271684084013 482171342748476881531505)
                    ·
                      rfl

theorem cell22_1408538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_1408538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408538 prefixEnd_1408538 := by exact prefixLift 1408538
  have htrace : WordTrace (prefixWord ++ tailWord_1408538) baseStart_1408538 baseEnd_1408538 := by
    simpa [prefixWord, tailWord_1408538, baseEnd_1408538] using wordTrace_append hprefix tailTrace_1408538
  have hstable : (prefixWord ++ tailWord_1408538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408538).length < 2 ^ (prefixWord ++ tailWord_1408538).sum := by decide
  have hdescent : baseEnd_1408538 < baseStart_1408538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408589 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_1408589 : Nat := 118140960795 + 1408589 * 2 ^ 59
def prefixEnd_1408589 : Nat := 4983230072969 + 3 ^ 40 * 1408589 * 2
def baseEnd_1408589 : Nat := 482188801090729748506349

theorem tailTrace_1408589 : CollatzResearch.WordTrace tailWord_1408589 prefixEnd_1408589 482188801090729748506349 := by
  unfold tailWord_1408589
  simp only [CollatzResearch.WordTrace]
  refine ⟨51375461493930095693724821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34250307662620063795816547 51375461493930095693724821)
  ·
    refine ⟨2408224757527973235643351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51375461493930095693724821 2408224757527973235643351)
    ·
      refine ⟨3612337136291959853465027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2408224757527973235643351 3612337136291959853465027)
      ·
        refine ⟨5418505704437939780197541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3612337136291959853465027 5418505704437939780197541)
        ·
          refine ⟨1015969819582113708787039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5418505704437939780197541 1015969819582113708787039)
          ·
            refine ⟨1523954729373170563180559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015969819582113708787039 1523954729373170563180559)
            ·
              refine ⟨2285932094059755844770839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523954729373170563180559 2285932094059755844770839)
              ·
                refine ⟨3428898141089633767156259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2285932094059755844770839 3428898141089633767156259)
                ·
                  refine ⟨5143347211634450650734389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428898141089633767156259 5143347211634450650734389)
                  ·
                    refine ⟨482188801090729748506349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5143347211634450650734389 482188801090729748506349)
                    ·
                      rfl

theorem cell22_1408589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_1408589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408589 prefixEnd_1408589 := by exact prefixLift 1408589
  have htrace : WordTrace (prefixWord ++ tailWord_1408589) baseStart_1408589 baseEnd_1408589 := by
    simpa [prefixWord, tailWord_1408589, baseEnd_1408589] using wordTrace_append hprefix tailTrace_1408589
  have hstable : (prefixWord ++ tailWord_1408589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408589).length < 2 ^ (prefixWord ++ tailWord_1408589).sum := by decide
  have hdescent : baseEnd_1408589 < baseStart_1408589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408613 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 7]
def baseStart_1408613 : Nat := 118140960795 + 1408613 * 2 ^ 59
def prefixEnd_1408613 : Nat := 4983230072969 + 3 ^ 40 * 1408613 * 2
def baseEnd_1408613 : Nat := 160732338927067228635425

theorem tailTrace_1408613 : CollatzResearch.WordTrace tailWord_1408613 prefixEnd_1408613 160732338927067228635425 := by
  unfold tailWord_1408613
  simp only [CollatzResearch.WordTrace]
  refine ⟨51376336845843147792598493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34250891230562098528398995 51376336845843147792598493)
  ·
    refine ⟨19266126317191180422224435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51376336845843147792598493 19266126317191180422224435)
    ·
      refine ⟨28899189475786770633336653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19266126317191180422224435 28899189475786770633336653)
      ·
        refine ⟨10837196053420038987501245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28899189475786770633336653 10837196053420038987501245)
        ·
          refine ⟨4063948520032514620312967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10837196053420038987501245 4063948520032514620312967)
          ·
            refine ⟨6095922780048771930469451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063948520032514620312967 6095922780048771930469451)
            ·
              refine ⟨9143884170073157895704177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6095922780048771930469451 9143884170073157895704177)
              ·
                refine ⟨6857913127554868421778133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9143884170073157895704177 6857913127554868421778133)
                ·
                  refine ⟨160732338927067228635425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6857913127554868421778133 160732338927067228635425)
                  ·
                    rfl

theorem cell22_1408613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_1408613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408613 prefixEnd_1408613 := by exact prefixLift 1408613
  have htrace : WordTrace (prefixWord ++ tailWord_1408613) baseStart_1408613 baseEnd_1408613 := by
    simpa [prefixWord, tailWord_1408613, baseEnd_1408613] using wordTrace_append hprefix tailTrace_1408613
  have hstable : (prefixWord ++ tailWord_1408613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408613).length < 2 ^ (prefixWord ++ tailWord_1408613).sum := by decide
  have hdescent : baseEnd_1408613 < baseStart_1408613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408617 : List Nat := [1, 2, 1, 1, 1, 4, 5, 3, 1, 3]
def baseStart_1408617 : Nat := 118140960795 + 1408617 * 2 ^ 59
def prefixEnd_1408617 : Nat := 4983230072969 + 3 ^ 40 * 1408617 * 2
def baseEnd_1408617 : Nat := 482198386062947008806263

theorem tailTrace_1408617 : CollatzResearch.WordTrace tailWord_1408617 prefixEnd_1408617 482198386062947008806263 := by
  unfold tailWord_1408617
  simp only [CollatzResearch.WordTrace]
  refine ⟨51376482737828656475744105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34250988491885770983829403 51376482737828656475744105)
  ·
    refine ⟨38532362053371492356808079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51376482737828656475744105 38532362053371492356808079)
    ·
      refine ⟨57798543080057238535212119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38532362053371492356808079 57798543080057238535212119)
      ·
        refine ⟨86697814620085857802818179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57798543080057238535212119 86697814620085857802818179)
        ·
          refine ⟨130046721930128786704227269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86697814620085857802818179 130046721930128786704227269)
          ·
            refine ⟨24383760361899147507042613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130046721930128786704227269 24383760361899147507042613)
            ·
              refine ⟨2285977533928045078785245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24383760361899147507042613 2285977533928045078785245)
              ·
                refine ⟨857241575223016904544467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2285977533928045078785245 857241575223016904544467)
                ·
                  refine ⟨1285862362834525356816701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857241575223016904544467 1285862362834525356816701)
                  ·
                    refine ⟨482198386062947008806263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285862362834525356816701 482198386062947008806263)
                    ·
                      rfl

theorem cell22_1408617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 3].length) (baseStart_1408617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408617 prefixEnd_1408617 := by exact prefixLift 1408617
  have htrace : WordTrace (prefixWord ++ tailWord_1408617) baseStart_1408617 baseEnd_1408617 := by
    simpa [prefixWord, tailWord_1408617, baseEnd_1408617] using wordTrace_append hprefix tailTrace_1408617
  have hstable : (prefixWord ++ tailWord_1408617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408617).length < 2 ^ (prefixWord ++ tailWord_1408617).sum := by decide
  have hdescent : baseEnd_1408617 < baseStart_1408617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408630 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1408630 : Nat := 118140960795 + 1408630 * 2 ^ 59
def prefixEnd_1408630 : Nat := 4983230072969 + 3 ^ 40 * 1408630 * 2
def baseEnd_1408630 : Nat := 160734278742873102743741

theorem tailTrace_1408630 : CollatzResearch.WordTrace tailWord_1408630 prefixEnd_1408630 160734278742873102743741 := by
  unfold tailWord_1408630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3211059805423847480997959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34251304591187706463978229 3211059805423847480997959)
  ·
    refine ⟨4816589708135771221496939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3211059805423847480997959 4816589708135771221496939)
    ·
      refine ⟨7224884562203656832245409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4816589708135771221496939 7224884562203656832245409)
      ·
        refine ⟨5418663421652742624184057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7224884562203656832245409 5418663421652742624184057)
        ·
          refine ⟨4063997566239556968138043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5418663421652742624184057 4063997566239556968138043)
          ·
            refine ⟨6095996349359335452207065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063997566239556968138043 6095996349359335452207065)
            ·
              refine ⟨4571997262019501589155299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6095996349359335452207065 4571997262019501589155299)
              ·
                refine ⟨6857995893029252383732949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571997262019501589155299 6857995893029252383732949)
                ·
                  refine ⟨160734278742873102743741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6857995893029252383732949 160734278742873102743741)
                  ·
                    rfl

theorem cell22_1408630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1408630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408630 prefixEnd_1408630 := by exact prefixLift 1408630
  have htrace : WordTrace (prefixWord ++ tailWord_1408630) baseStart_1408630 baseEnd_1408630 := by
    simpa [prefixWord, tailWord_1408630, baseEnd_1408630] using wordTrace_append hprefix tailTrace_1408630
  have hstable : (prefixWord ++ tailWord_1408630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408630).length < 2 ^ (prefixWord ++ tailWord_1408630).sum := by decide
  have hdescent : baseEnd_1408630 < baseStart_1408630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408643 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 3, 4]
def baseStart_1408643 : Nat := 118140960795 + 1408643 * 2 ^ 59
def prefixEnd_1408643 : Nat := 4983230072969 + 3 ^ 40 * 1408643 * 2
def baseEnd_1408643 : Nat := 482207286394291607656183

theorem tailTrace_1408643 : CollatzResearch.WordTrace tailWord_1408643 prefixEnd_1408643 482207286394291607656183 := by
  unfold tailWord_1408643
  simp only [CollatzResearch.WordTrace]
  refine ⟨51377431035734462916190583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34251620690489641944127055 51377431035734462916190583)
  ·
    refine ⟨77066146553601694374285875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51377431035734462916190583 77066146553601694374285875)
    ·
      refine ⟨115599219830402541561428813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77066146553601694374285875 115599219830402541561428813)
      ·
        refine ⟨43349707436400953085535805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115599219830402541561428813 43349707436400953085535805)
        ·
          refine ⟨16256140288650357407075927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43349707436400953085535805 16256140288650357407075927)
          ·
            refine ⟨24384210432975536110613891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16256140288650357407075927 24384210432975536110613891)
            ·
              refine ⟨36576315649463304165920837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24384210432975536110613891 36576315649463304165920837)
              ·
                refine ⟨6858059184274369531110157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36576315649463304165920837 6858059184274369531110157)
                ·
                  refine ⟨2571772194102888574166309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6858059184274369531110157 2571772194102888574166309)
                  ·
                    refine ⟨482207286394291607656183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2571772194102888574166309 482207286394291607656183)
                    ·
                      rfl

theorem cell22_1408643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 4].length) (baseStart_1408643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408643 prefixEnd_1408643 := by exact prefixLift 1408643
  have htrace : WordTrace (prefixWord ++ tailWord_1408643) baseStart_1408643 baseEnd_1408643 := by
    simpa [prefixWord, tailWord_1408643, baseEnd_1408643] using wordTrace_append hprefix tailTrace_1408643
  have hstable : (prefixWord ++ tailWord_1408643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408643).length < 2 ^ (prefixWord ++ tailWord_1408643).sum := by decide
  have hdescent : baseEnd_1408643 < baseStart_1408643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408647 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 5]
def baseStart_1408647 : Nat := 118140960795 + 1408647 * 2 ^ 59
def prefixEnd_1408647 : Nat := 4983230072969 + 3 ^ 40 * 1408647 * 2
def baseEnd_1408647 : Nat := 160736218558678976852057

theorem tailTrace_1408647 : CollatzResearch.WordTrace tailWord_1408647 prefixEnd_1408647 160736218558678976852057 := by
  unfold tailWord_1408647
  simp only [CollatzResearch.WordTrace]
  refine ⟨51377576927719971599336195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34251717951813314399557463 51377576927719971599336195)
  ·
    refine ⟨77066365391579957399004293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51377576927719971599336195 77066365391579957399004293)
    ·
      refine ⟨14449943510921242012313305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77066365391579957399004293 14449943510921242012313305)
      ·
        refine ⟨10837457633190931509234979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14449943510921242012313305 10837457633190931509234979)
        ·
          refine ⟨16256186449786397263852469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10837457633190931509234979 16256186449786397263852469)
          ·
            refine ⟨1524017479667474743486169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16256186449786397263852469 1524017479667474743486169)
            ·
              refine ⟨1143013109750606057614627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1524017479667474743486169 1143013109750606057614627)
              ·
                refine ⟨1714519664625909086421941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143013109750606057614627 1714519664625909086421941)
                ·
                  refine ⟨160736218558678976852057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1714519664625909086421941 160736218558678976852057)
                  ·
                    rfl

theorem cell22_1408647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 5].length) (baseStart_1408647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408647 prefixEnd_1408647 := by exact prefixLift 1408647
  have htrace : WordTrace (prefixWord ++ tailWord_1408647) baseStart_1408647 baseEnd_1408647 := by
    simpa [prefixWord, tailWord_1408647, baseEnd_1408647] using wordTrace_append hprefix tailTrace_1408647
  have hstable : (prefixWord ++ tailWord_1408647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408647).length < 2 ^ (prefixWord ++ tailWord_1408647).sum := by decide
  have hdescent : baseEnd_1408647 < baseStart_1408647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408675 : List Nat := [1, 1, 1, 4, 1, 1, 4, 5, 4]
def baseStart_1408675 : Nat := 118140960795 + 1408675 * 2 ^ 59
def prefixEnd_1408675 : Nat := 4983230072969 + 3 ^ 40 * 1408675 * 2
def baseEnd_1408675 : Nat := 160739413549418063618695

theorem tailTrace_1408675 : CollatzResearch.WordTrace tailWord_1408675 prefixEnd_1408675 160739413549418063618695 := by
  unfold tailWord_1408675
  simp only [CollatzResearch.WordTrace]
  refine ⟨51378598171618532381355479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34252398781079021587570319 51378598171618532381355479)
  ·
    refine ⟨77067897257427798572033219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51378598171618532381355479 77067897257427798572033219)
    ·
      refine ⟨115601845886141697858049829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77067897257427798572033219 115601845886141697858049829)
      ·
        refine ⟨21675346103651568348384343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115601845886141697858049829 21675346103651568348384343)
        ·
          refine ⟨32513019155477352522576515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21675346103651568348384343 32513019155477352522576515)
          ·
            refine ⟨48769528733216028783864773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32513019155477352522576515 48769528733216028783864773)
            ·
              refine ⟨9144286637478005396974645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48769528733216028783864773 9144286637478005396974645)
              ·
                refine ⟨857276872263563005966373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9144286637478005396974645 857276872263563005966373)
                ·
                  refine ⟨160739413549418063618695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857276872263563005966373 160739413549418063618695)
                  ·
                    rfl

theorem cell22_1408675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 4].length) (baseStart_1408675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408675 prefixEnd_1408675 := by exact prefixLift 1408675
  have htrace : WordTrace (prefixWord ++ tailWord_1408675) baseStart_1408675 baseEnd_1408675 := by
    simpa [prefixWord, tailWord_1408675, baseEnd_1408675] using wordTrace_append hprefix tailTrace_1408675
  have hstable : (prefixWord ++ tailWord_1408675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408675).length < 2 ^ (prefixWord ++ tailWord_1408675).sum := by decide
  have hdescent : baseEnd_1408675 < baseStart_1408675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408690 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_1408690 : Nat := 118140960795 + 1408690 * 2 ^ 59
def prefixEnd_1408690 : Nat := 4983230072969 + 3 ^ 40 * 1408690 * 2
def baseEnd_1408690 : Nat := 482223375454799151731039

theorem tailTrace_1408690 : CollatzResearch.WordTrace tailWord_1408690 prefixEnd_1408690 482223375454799151731039 := by
  unfold tailWord_1408690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12844786316641047485787881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34252763511042793295434349 12844786316641047485787881)
  ·
    refine ⟨9633589737480785614340911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12844786316641047485787881 9633589737480785614340911)
    ·
      refine ⟨14450384606221178421511367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9633589737480785614340911 14450384606221178421511367)
      ·
        refine ⟨21675576909331767632267051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14450384606221178421511367 21675576909331767632267051)
        ·
          refine ⟨32513365363997651448400577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21675576909331767632267051 32513365363997651448400577)
          ·
            refine ⟨24385024022998238586300433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32513365363997651448400577 24385024022998238586300433)
            ·
              refine ⟨18288768017248678939725325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24385024022998238586300433 18288768017248678939725325)
              ·
                refine ⟨6858288006468254602396997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18288768017248678939725325 6858288006468254602396997)
                ·
                  refine ⟨1285929001212797737949437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6858288006468254602396997 1285929001212797737949437)
                  ·
                    refine ⟨482223375454799151731039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285929001212797737949437 482223375454799151731039)
                    ·
                      rfl

theorem cell22_1408690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_1408690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408690 prefixEnd_1408690 := by exact prefixLift 1408690
  have htrace : WordTrace (prefixWord ++ tailWord_1408690) baseStart_1408690 baseEnd_1408690 := by
    simpa [prefixWord, tailWord_1408690, baseEnd_1408690] using wordTrace_append hprefix tailTrace_1408690
  have hstable : (prefixWord ++ tailWord_1408690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408690).length < 2 ^ (prefixWord ++ tailWord_1408690).sum := by decide
  have hdescent : baseEnd_1408690 < baseStart_1408690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408722 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_1408722 : Nat := 118140960795 + 1408722 * 2 ^ 59
def prefixEnd_1408722 : Nat := 4983230072969 + 3 ^ 40 * 1408722 * 2
def baseEnd_1408722 : Nat := 482234329708761734930941

theorem tailTrace_1408722 : CollatzResearch.WordTrace tailWord_1408722 prefixEnd_1408722 482234329708761734930941 := by
  unfold tailWord_1408722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12845078100612064852079105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34253541601632172938877613 12845078100612064852079105)
  ·
    refine ⟨9633808575459048639059329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12845078100612064852079105 9633808575459048639059329)
    ·
      refine ⟨7225356431594286479294497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9633808575459048639059329 7225356431594286479294497)
      ·
        refine ⟨5419017323695714859470873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7225356431594286479294497 5419017323695714859470873)
        ·
          refine ⟨4064262992771786144603155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5419017323695714859470873 4064262992771786144603155)
          ·
            refine ⟨6096394489157679216904733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064262992771786144603155 6096394489157679216904733)
            ·
              refine ⟨2286147933434129706339275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6096394489157679216904733 2286147933434129706339275)
              ·
                refine ⟨3429221900151194559508913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286147933434129706339275 3429221900151194559508913)
                ·
                  refine ⟨2571916425113395919631685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3429221900151194559508913 2571916425113395919631685)
                  ·
                    refine ⟨482234329708761734930941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2571916425113395919631685 482234329708761734930941)
                    ·
                      rfl

theorem cell22_1408722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_1408722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408722 prefixEnd_1408722 := by exact prefixLift 1408722
  have htrace : WordTrace (prefixWord ++ tailWord_1408722) baseStart_1408722 baseEnd_1408722 := by
    simpa [prefixWord, tailWord_1408722, baseEnd_1408722] using wordTrace_append hprefix tailTrace_1408722
  have hstable : (prefixWord ++ tailWord_1408722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408722).length < 2 ^ (prefixWord ++ tailWord_1408722).sum := by decide
  have hdescent : baseEnd_1408722 < baseStart_1408722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408735 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 5, 3]
def baseStart_1408735 : Nat := 118140960795 + 1408735 * 2 ^ 59
def prefixEnd_1408735 : Nat := 4983230072969 + 3 ^ 40 * 1408735 * 2
def baseEnd_1408735 : Nat := 482238779874434034355901

theorem tailTrace_1408735 : CollatzResearch.WordTrace tailWord_1408735 prefixEnd_1408735 482238779874434034355901 := by
  unfold tailWord_1408735
  simp only [CollatzResearch.WordTrace]
  refine ⟨51380786551401162628539659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34253857700934108419026439 51380786551401162628539659)
  ·
    refine ⟨77071179827101743942809489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51380786551401162628539659 77071179827101743942809489)
    ·
      refine ⟨57803384870326307957107117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77071179827101743942809489 57803384870326307957107117)
      ·
        refine ⟨21676269326372365483915169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57803384870326307957107117 21676269326372365483915169)
        ·
          refine ⟨16257201994779274112936377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21676269326372365483915169 16257201994779274112936377)
          ·
            refine ⟨12192901496084455584702283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16257201994779274112936377 12192901496084455584702283)
            ·
              refine ⟨18289352244126683377053425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12192901496084455584702283 18289352244126683377053425)
              ·
                refine ⟨13717014183095012532790069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18289352244126683377053425 13717014183095012532790069)
                ·
                  refine ⟨1285970079665157424949069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13717014183095012532790069 1285970079665157424949069)
                  ·
                    refine ⟨482238779874434034355901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1285970079665157424949069 482238779874434034355901)
                    ·
                      rfl

theorem cell22_1408735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_1408735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408735 prefixEnd_1408735 := by exact prefixLift 1408735
  have htrace : WordTrace (prefixWord ++ tailWord_1408735) baseStart_1408735 baseEnd_1408735 := by
    simpa [prefixWord, tailWord_1408735, baseEnd_1408735] using wordTrace_append hprefix tailTrace_1408735
  have hstable : (prefixWord ++ tailWord_1408735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408735).length < 2 ^ (prefixWord ++ tailWord_1408735).sum := by decide
  have hdescent : baseEnd_1408735 < baseStart_1408735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408763 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 1, 7]
def baseStart_1408763 : Nat := 118140960795 + 1408763 * 2 ^ 59
def prefixEnd_1408763 : Nat := 4983230072969 + 3 ^ 40 * 1408763 * 2
def baseEnd_1408763 : Nat := 482248364846651294655815

theorem tailTrace_1408763 : CollatzResearch.WordTrace tailWord_1408763 prefixEnd_1408763 482248364846651294655815 := by
  unfold tailWord_1408763
  simp only [CollatzResearch.WordTrace]
  refine ⟨51381807795299723410558943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34254538530199815607039295 51381807795299723410558943)
  ·
    refine ⟨77072711692949585115838415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51381807795299723410558943 77072711692949585115838415)
    ·
      refine ⟨115609067539424377673757623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77072711692949585115838415 115609067539424377673757623)
      ·
        refine ⟨173413601309136566510636435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115609067539424377673757623 173413601309136566510636435)
        ·
          refine ⟨260120401963704849765954653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173413601309136566510636435 260120401963704849765954653)
          ·
            refine ⟨97545150736389318662232995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260120401963704849765954653 97545150736389318662232995)
            ·
              refine ⟨146317726104583977993349493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97545150736389318662232995 146317726104583977993349493)
              ·
                refine ⟨13717286822304747936876515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146317726104583977993349493 13717286822304747936876515)
                ·
                  refine ⟨20575930233457121905314773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13717286822304747936876515 20575930233457121905314773)
                  ·
                    refine ⟨482248364846651294655815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20575930233457121905314773 482248364846651294655815)
                    ·
                      rfl

theorem cell22_1408763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_1408763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408763 prefixEnd_1408763 := by exact prefixLift 1408763
  have htrace : WordTrace (prefixWord ++ tailWord_1408763) baseStart_1408763 baseEnd_1408763 := by
    simpa [prefixWord, tailWord_1408763, baseEnd_1408763] using wordTrace_append hprefix tailTrace_1408763
  have hstable : (prefixWord ++ tailWord_1408763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408763).length < 2 ^ (prefixWord ++ tailWord_1408763).sum := by decide
  have hdescent : baseEnd_1408763 < baseStart_1408763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408829 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_1408829 : Nat := 118140960795 + 1408829 * 2 ^ 59
def prefixEnd_1408829 : Nat := 4983230072969 + 3 ^ 40 * 1408829 * 2
def baseEnd_1408829 : Nat := 482270957995449122505613

theorem tailTrace_1408829 : CollatzResearch.WordTrace tailWord_1408829 prefixEnd_1408829 482270957995449122505613 := by
  unfold tailWord_1408829
  simp only [CollatzResearch.WordTrace]
  refine ⟨51384215013060616682461541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34256143342040411121641027 51384215013060616682461541)
  ·
    refine ⟨9634540314948865627961539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51384215013060616682461541 9634540314948865627961539)
    ·
      refine ⟨14451810472423298441942309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9634540314948865627961539 14451810472423298441942309)
      ·
        refine ⟨2709714463579368457864183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14451810472423298441942309 2709714463579368457864183)
        ·
          refine ⟨4064571695369052686796275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709714463579368457864183 4064571695369052686796275)
          ·
            refine ⟨6096857543053579030194413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064571695369052686796275 6096857543053579030194413)
            ·
              refine ⟨2286321578645092136322905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6096857543053579030194413 2286321578645092136322905)
              ·
                refine ⟨1714741183983819102242179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2286321578645092136322905 1714741183983819102242179)
                ·
                  refine ⟨2572111775975728653363269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714741183983819102242179 2572111775975728653363269)
                  ·
                    refine ⟨482270957995449122505613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2572111775975728653363269 482270957995449122505613)
                    ·
                      rfl

theorem cell22_1408829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_1408829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408829 prefixEnd_1408829 := by exact prefixLift 1408829
  have htrace : WordTrace (prefixWord ++ tailWord_1408829) baseStart_1408829 baseEnd_1408829 := by
    simpa [prefixWord, tailWord_1408829, baseEnd_1408829] using wordTrace_append hprefix tailTrace_1408829
  have hstable : (prefixWord ++ tailWord_1408829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408829).length < 2 ^ (prefixWord ++ tailWord_1408829).sum := by decide
  have hdescent : baseEnd_1408829 < baseStart_1408829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408855 : List Nat := [1, 1, 3, 2, 5, 10]
def baseStart_1408855 : Nat := 118140960795 + 1408855 * 2 ^ 59
def prefixEnd_1408855 : Nat := 4983230072969 + 3 ^ 40 * 1408855 * 2
def baseEnd_1408855 : Nat := 5954072325022144708093

theorem tailTrace_1408855 : CollatzResearch.WordTrace tailWord_1408855 prefixEnd_1408855 5954072325022144708093 := by
  unfold tailWord_1408855
  simp only [CollatzResearch.WordTrace]
  refine ⟨51385163310966423122908019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34256775540644282081938679 51385163310966423122908019)
  ·
    refine ⟨77077744966449634684362029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51385163310966423122908019 77077744966449634684362029)
    ·
      refine ⟨28904154362418613006635761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77077744966449634684362029 28904154362418613006635761)
      ·
        refine ⟨21678115771813959754976821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28904154362418613006635761 21678115771813959754976821)
        ·
          refine ⟨2032323353607558727029077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21678115771813959754976821 2032323353607558727029077)
          ·
            refine ⟨5954072325022144708093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2032323353607558727029077 5954072325022144708093)
            ·
              rfl

theorem cell22_1408855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 10].length) (baseStart_1408855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408855 prefixEnd_1408855 := by exact prefixLift 1408855
  have htrace : WordTrace (prefixWord ++ tailWord_1408855) baseStart_1408855 baseEnd_1408855 := by
    simpa [prefixWord, tailWord_1408855, baseEnd_1408855] using wordTrace_append hprefix tailTrace_1408855
  have hstable : (prefixWord ++ tailWord_1408855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408855).length < 2 ^ (prefixWord ++ tailWord_1408855).sum := by decide
  have hdescent : baseEnd_1408855 < baseStart_1408855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408910 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_1408910 : Nat := 118140960795 + 1408910 * 2 ^ 59
def prefixEnd_1408910 : Nat := 4983230072969 + 3 ^ 40 * 1408910 * 2
def baseEnd_1408910 : Nat := 482298685950791911230365

theorem tailTrace_1408910 : CollatzResearch.WordTrace tailWord_1408910 prefixEnd_1408910 482298685950791911230365 := by
  unfold tailWord_1408910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6423396165720895939520023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34258112883844778344106789 6423396165720895939520023)
  ·
    refine ⟨9635094248581343909280035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6423396165720895939520023 9635094248581343909280035)
    ·
      refine ⟨14452641372872015863920053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9635094248581343909280035 14452641372872015863920053)
      ·
        refine ⟨1354935128706751487242505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14452641372872015863920053 1354935128706751487242505)
        ·
          refine ⟨1016201346530063615431879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1354935128706751487242505 1016201346530063615431879)
          ·
            refine ⟨1524302019795095423147819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016201346530063615431879 1524302019795095423147819)
            ·
              refine ⟨2286453029692643134721729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524302019795095423147819 2286453029692643134721729)
              ·
                refine ⟨1714839772269482351041297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2286453029692643134721729 1714839772269482351041297)
                ·
                  refine ⟨1286129829202111763280973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1714839772269482351041297 1286129829202111763280973)
                  ·
                    refine ⟨482298685950791911230365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1286129829202111763280973 482298685950791911230365)
                    ·
                      rfl

theorem cell22_1408910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_1408910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408910 prefixEnd_1408910 := by exact prefixLift 1408910
  have htrace : WordTrace (prefixWord ++ tailWord_1408910) baseStart_1408910 baseEnd_1408910 := by
    simpa [prefixWord, tailWord_1408910, baseEnd_1408910] using wordTrace_append hprefix tailTrace_1408910
  have hstable : (prefixWord ++ tailWord_1408910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408910).length < 2 ^ (prefixWord ++ tailWord_1408910).sum := by decide
  have hdescent : baseEnd_1408910 < baseStart_1408910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408932 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1408932 : Nat := 118140960795 + 1408932 * 2 ^ 59
def prefixEnd_1408932 : Nat := 4983230072969 + 3 ^ 40 * 1408932 * 2
def baseEnd_1408932 : Nat := 482306217000391187180297

theorem tailTrace_1408932 : CollatzResearch.WordTrace tailWord_1408932 prefixEnd_1408932 482306217000391187180297 := by
  unfold tailWord_1408932
  simp only [CollatzResearch.WordTrace]
  refine ⟨25693985865843732636730525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34258647821124976848974033 25693985865843732636730525)
  ·
    refine ⟨9635244699691399738773947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25693985865843732636730525 9635244699691399738773947)
    ·
      refine ⟨14452867049537099608160921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9635244699691399738773947 14452867049537099608160921)
      ·
        refine ⟨10839650287152824706120691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14452867049537099608160921 10839650287152824706120691)
        ·
          refine ⟨16259475430729237059181037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10839650287152824706120691 16259475430729237059181037)
          ·
            refine ⟨6097303286523463897192889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16259475430729237059181037 6097303286523463897192889)
            ·
              refine ⟨4572977464892597922894667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6097303286523463897192889 4572977464892597922894667)
              ·
                refine ⟨6859466197338896884342001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4572977464892597922894667 6859466197338896884342001)
                ·
                  refine ⟨5144599648004172663256501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6859466197338896884342001 5144599648004172663256501)
                  ·
                    refine ⟨482306217000391187180297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5144599648004172663256501 482306217000391187180297)
                    ·
                      rfl

theorem cell22_1408932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1408932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1408932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1408932 prefixEnd_1408932 := by exact prefixLift 1408932
  have htrace : WordTrace (prefixWord ++ tailWord_1408932) baseStart_1408932 baseEnd_1408932 := by
    simpa [prefixWord, tailWord_1408932, baseEnd_1408932] using wordTrace_append hprefix tailTrace_1408932
  have hstable : (prefixWord ++ tailWord_1408932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408932).length < 2 ^ (prefixWord ++ tailWord_1408932).sum := by decide
  have hdescent : baseEnd_1408932 < baseStart_1408932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409073 : List Nat := [1, 2, 2, 3, 1, 4, 2, 3, 1, 3]
def baseStart_1409073 : Nat := 118140960795 + 1409073 * 2 ^ 59
def prefixEnd_1409073 : Nat := 4983230072969 + 3 ^ 40 * 1409073 * 2
def baseEnd_1409073 : Nat := 482354484181913819404865

theorem tailTrace_1409073 : CollatzResearch.WordTrace tailWord_1409073 prefixEnd_1409073 482354484181913819404865 := by
  unfold tailWord_1409073
  simp only [CollatzResearch.WordTrace]
  refine ⟨51393114424176646354343873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34262076282784430902895915 51393114424176646354343873)
  ·
    refine ⟨38544835818132484765757905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51393114424176646354343873 38544835818132484765757905)
    ·
      refine ⟨28908626863599363574318429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38544835818132484765757905 28908626863599363574318429)
      ·
        refine ⟨10840735073849761340369411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28908626863599363574318429 10840735073849761340369411)
        ·
          refine ⟨16261102610774642010554117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10840735073849761340369411 16261102610774642010554117)
          ·
            refine ⟨3048956739520245376978897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16261102610774642010554117 3048956739520245376978897)
            ·
              refine ⟨2286717554640184032734173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048956739520245376978897 2286717554640184032734173)
              ·
                refine ⟨857519082990069012275315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2286717554640184032734173 857519082990069012275315)
                ·
                  refine ⟨1286278624485103518412973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857519082990069012275315 1286278624485103518412973)
                  ·
                    refine ⟨482354484181913819404865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1286278624485103518412973 482354484181913819404865)
                    ·
                      rfl

theorem cell22_1409073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_1409073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409073 prefixEnd_1409073 := by exact prefixLift 1409073
  have htrace : WordTrace (prefixWord ++ tailWord_1409073) baseStart_1409073 baseEnd_1409073 := by
    simpa [prefixWord, tailWord_1409073, baseEnd_1409073] using wordTrace_append hprefix tailTrace_1409073
  have hstable : (prefixWord ++ tailWord_1409073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409073).length < 2 ^ (prefixWord ++ tailWord_1409073).sum := by decide
  have hdescent : baseEnd_1409073 < baseStart_1409073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409086 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1409086 : Nat := 118140960795 + 1409086 * 2 ^ 59
def prefixEnd_1409086 : Nat := 4983230072969 + 3 ^ 40 * 1409086 * 2
def baseEnd_1409086 : Nat := 160786311449195372943275

theorem tailTrace_1409086 : CollatzResearch.WordTrace tailWord_1409086 prefixEnd_1409086 160786311449195372943275 := by
  unfold tailWord_1409086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424198571641193696820889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34262392382086366383044741 6424198571641193696820889)
  ·
    refine ⟨4818148928730895272615667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6424198571641193696820889 4818148928730895272615667)
    ·
      refine ⟨7227223393096342908923501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4818148928730895272615667 7227223393096342908923501)
      ·
        refine ⟨2710208772411128590846313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7227223393096342908923501 2710208772411128590846313)
        ·
          refine ⟨2032656579308346443134735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2710208772411128590846313 2032656579308346443134735)
          ·
            refine ⟨3048984868962519664702103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032656579308346443134735 3048984868962519664702103)
            ·
              refine ⟨4573477303443779497053155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3048984868962519664702103 4573477303443779497053155)
              ·
                refine ⟨6860215955165669245579733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573477303443779497053155 6860215955165669245579733)
                ·
                  refine ⟨160786311449195372943275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6860215955165669245579733 160786311449195372943275)
                  ·
                    rfl

theorem cell22_1409086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1409086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409086 prefixEnd_1409086 := by exact prefixLift 1409086
  have htrace : WordTrace (prefixWord ++ tailWord_1409086) baseStart_1409086 baseEnd_1409086 := by
    simpa [prefixWord, tailWord_1409086, baseEnd_1409086] using wordTrace_append hprefix tailTrace_1409086
  have hstable : (prefixWord ++ tailWord_1409086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409086).length < 2 ^ (prefixWord ++ tailWord_1409086).sum := by decide
  have hdescent : baseEnd_1409086 < baseStart_1409086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409116 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1409116 : Nat := 118140960795 + 1409116 * 2 ^ 59
def prefixEnd_1409116 : Nat := 4983230072969 + 3 ^ 40 * 1409116 * 2
def baseEnd_1409116 : Nat := 482369203960676040579733

theorem tailTrace_1409116 : CollatzResearch.WordTrace tailWord_1409116 prefixEnd_1409116 482369203960676040579733 := by
  unfold tailWord_1409116
  simp only [CollatzResearch.WordTrace]
  refine ⟨25697341381510432349079601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34263121842013909798772801 25697341381510432349079601)
  ·
    refine ⟨19273006036132824261809701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25697341381510432349079601 19273006036132824261809701)
    ·
      refine ⟨3613688631774904549089319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19273006036132824261809701 3613688631774904549089319)
      ·
        refine ⟨5420532947662356823633979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3613688631774904549089319 5420532947662356823633979)
        ·
          refine ⟨8130799421493535235450969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5420532947662356823633979 8130799421493535235450969)
          ·
            refine ⟨6098099566120151426588227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8130799421493535235450969 6098099566120151426588227)
            ·
              refine ⟨9147149349180227139882341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6098099566120151426588227 9147149349180227139882341)
              ·
                refine ⟨1715090502971292588727939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9147149349180227139882341 1715090502971292588727939)
                ·
                  refine ⟨2572635754456938883091909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715090502971292588727939 2572635754456938883091909)
                  ·
                    refine ⟨482369203960676040579733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2572635754456938883091909 482369203960676040579733)
                    ·
                      rfl

theorem cell22_1409116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1409116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409116 prefixEnd_1409116 := by exact prefixLift 1409116
  have htrace : WordTrace (prefixWord ++ tailWord_1409116) baseStart_1409116 baseEnd_1409116 := by
    simpa [prefixWord, tailWord_1409116, baseEnd_1409116] using wordTrace_append hprefix tailTrace_1409116
  have hstable : (prefixWord ++ tailWord_1409116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409116).length < 2 ^ (prefixWord ++ tailWord_1409116).sum := by decide
  have hdescent : baseEnd_1409116 < baseStart_1409116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409129 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 6, 3]
def baseStart_1409129 : Nat := 118140960795 + 1409129 * 2 ^ 59
def prefixEnd_1409129 : Nat := 4983230072969 + 3 ^ 40 * 1409129 * 2
def baseEnd_1409129 : Nat := 482373654126348340004693

theorem tailTrace_1409129 : CollatzResearch.WordTrace tailWord_1409129 prefixEnd_1409129 482373654126348340004693 := by
  unfold tailWord_1409129
  simp only [CollatzResearch.WordTrace]
  refine ⟨51395156911973767918382441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34263437941315845278921627 51395156911973767918382441)
  ·
    refine ⟨38546367683980325938786831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51395156911973767918382441 38546367683980325938786831)
    ·
      refine ⟨57819551525970488908180247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38546367683980325938786831 57819551525970488908180247)
      ·
        refine ⟨86729327288955733362270371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57819551525970488908180247 86729327288955733362270371)
        ·
          refine ⟨130093990933433600043405557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86729327288955733362270371 130093990933433600043405557)
          ·
            refine ⟨12196311650009400004069271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130093990933433600043405557 12196311650009400004069271)
            ·
              refine ⟨18294467475014100006103907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12196311650009400004069271 18294467475014100006103907)
              ·
                refine ⟨27441701212521150009155861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18294467475014100006103907 27441701212521150009155861)
                ·
                  refine ⟨1286329744336928906679181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27441701212521150009155861 1286329744336928906679181)
                  ·
                    refine ⟨482373654126348340004693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1286329744336928906679181 482373654126348340004693)
                    ·
                      rfl

theorem cell22_1409129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_1409129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409129 prefixEnd_1409129 := by exact prefixLift 1409129
  have htrace : WordTrace (prefixWord ++ tailWord_1409129) baseStart_1409129 baseEnd_1409129 := by
    simpa [prefixWord, tailWord_1409129, baseEnd_1409129] using wordTrace_append hprefix tailTrace_1409129
  have hstable : (prefixWord ++ tailWord_1409129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409129).length < 2 ^ (prefixWord ++ tailWord_1409129).sum := by decide
  have hdescent : baseEnd_1409129 < baseStart_1409129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409148 : List Nat := [2, 2, 2, 1, 1, 5, 3, 2, 4]
def baseStart_1409148 : Nat := 118140960795 + 1409148 * 2 ^ 59
def prefixEnd_1409148 : Nat := 4983230072969 + 3 ^ 40 * 1409148 * 2
def baseEnd_1409148 : Nat := 160793386071546207926545

theorem tailTrace_1409148 : CollatzResearch.WordTrace tailWord_1409148 prefixEnd_1409148 160793386071546207926545 := by
  unfold tailWord_1409148
  simp only [CollatzResearch.WordTrace]
  refine ⟨25697924949452467081662049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34263899932603289442216065 25697924949452467081662049)
  ·
    refine ⟨19273443712089350311246537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25697924949452467081662049 19273443712089350311246537)
    ·
      refine ⟨14455082784067012733434903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19273443712089350311246537 14455082784067012733434903)
      ·
        refine ⟨21682624176100519100152355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14455082784067012733434903 21682624176100519100152355)
        ·
          refine ⟨32523936264150778650228533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21682624176100519100152355 32523936264150778650228533)
          ·
            refine ⟨3049119024764135498458925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32523936264150778650228533 3049119024764135498458925)
            ·
              refine ⟨1143419634286550811922097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3049119024764135498458925 1143419634286550811922097)
              ·
                refine ⟨857564725714913108941573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1143419634286550811922097 857564725714913108941573)
                ·
                  refine ⟨160793386071546207926545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857564725714913108941573 160793386071546207926545)
                  ·
                    rfl

theorem cell22_1409148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_1409148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409148 prefixEnd_1409148 := by exact prefixLift 1409148
  have htrace : WordTrace (prefixWord ++ tailWord_1409148) baseStart_1409148 baseEnd_1409148 := by
    simpa [prefixWord, tailWord_1409148, baseEnd_1409148] using wordTrace_append hprefix tailTrace_1409148
  have hstable : (prefixWord ++ tailWord_1409148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409148).length < 2 ^ (prefixWord ++ tailWord_1409148).sum := by decide
  have hdescent : baseEnd_1409148 < baseStart_1409148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409178 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_1409178 : Nat := 118140960795 + 1409178 * 2 ^ 59
def prefixEnd_1409178 : Nat := 4983230072969 + 3 ^ 40 * 1409178 * 2
def baseEnd_1409178 : Nat := 482390427827728545529543

theorem tailTrace_1409178 : CollatzResearch.WordTrace tailWord_1409178 prefixEnd_1409178 482390427827728545529543 := by
  unfold tailWord_1409178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12849236022199062321729047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34264629392530832857944125 12849236022199062321729047)
  ·
    refine ⟨19273854033298593482593571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12849236022199062321729047 19273854033298593482593571)
    ·
      refine ⟨28910781049947890223890357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19273854033298593482593571 28910781049947890223890357)
      ·
        refine ⟨2710385723432614708489721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28910781049947890223890357 2710385723432614708489721)
        ·
          refine ⟨2032789292574461031367291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2710385723432614708489721 2032789292574461031367291)
          ·
            refine ⟨3049183938861691547050937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032789292574461031367291 3049183938861691547050937)
            ·
              refine ⟨2286887954146268660288203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3049183938861691547050937 2286887954146268660288203)
              ·
                refine ⟨3430331931219402990432305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286887954146268660288203 3430331931219402990432305)
                ·
                  refine ⟨2572748948414552242824229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3430331931219402990432305 2572748948414552242824229)
                  ·
                    refine ⟨482390427827728545529543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2572748948414552242824229 482390427827728545529543)
                    ·
                      rfl

theorem cell22_1409178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_1409178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409178 prefixEnd_1409178 := by exact prefixLift 1409178
  have htrace : WordTrace (prefixWord ++ tailWord_1409178) baseStart_1409178 baseEnd_1409178 := by
    simpa [prefixWord, tailWord_1409178, baseEnd_1409178] using wordTrace_append hprefix tailTrace_1409178
  have hstable : (prefixWord ++ tailWord_1409178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409178).length < 2 ^ (prefixWord ++ tailWord_1409178).sum := by decide
  have hdescent : baseEnd_1409178 < baseStart_1409178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409208 : List Nat := [2, 1, 2, 1, 2, 1, 5, 4, 1, 3]
def baseStart_1409208 : Nat := 118140960795 + 1409208 * 2 ^ 59
def prefixEnd_1409208 : Nat := 4983230072969 + 3 ^ 40 * 1409208 * 2
def baseEnd_1409208 : Nat := 482400697440818467279451

theorem tailTrace_1409208 : CollatzResearch.WordTrace tailWord_1409208 prefixEnd_1409208 482400697440818467279451 := by
  unfold tailWord_1409208
  simp only [CollatzResearch.WordTrace]
  refine ⟨25699019139343782205254139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34265358852458376273672185 25699019139343782205254139)
  ·
    refine ⟨38548528709015673307881209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25699019139343782205254139 38548528709015673307881209)
    ·
      refine ⟨28911396531761754980910907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38548528709015673307881209 28911396531761754980910907)
      ·
        refine ⟨43367094797642632471366361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28911396531761754980910907 43367094797642632471366361)
        ·
          refine ⟨32525321098231974353524771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43367094797642632471366361 32525321098231974353524771)
          ·
            refine ⟨48787981647347961530287157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32525321098231974353524771 48787981647347961530287157)
            ·
              refine ⟨4573873279438871393464421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48787981647347961530287157 4573873279438871393464421)
              ·
                refine ⟨857601239894788386274579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4573873279438871393464421 857601239894788386274579)
                ·
                  refine ⟨1286401859842182579411869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857601239894788386274579 1286401859842182579411869)
                  ·
                    refine ⟨482400697440818467279451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1286401859842182579411869 482400697440818467279451)
                    ·
                      rfl

theorem cell22_1409208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_1409208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409208 prefixEnd_1409208 := by exact prefixLift 1409208
  have htrace : WordTrace (prefixWord ++ tailWord_1409208) baseStart_1409208 baseEnd_1409208 := by
    simpa [prefixWord, tailWord_1409208, baseEnd_1409208] using wordTrace_append hprefix tailTrace_1409208
  have hstable : (prefixWord ++ tailWord_1409208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409208).length < 2 ^ (prefixWord ++ tailWord_1409208).sum := by decide
  have hdescent : baseEnd_1409208 < baseStart_1409208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409249 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 8]
def baseStart_1409249 : Nat := 118140960795 + 1409249 * 2 ^ 59
def prefixEnd_1409249 : Nat := 4983230072969 + 3 ^ 40 * 1409249 * 2
def baseEnd_1409249 : Nat := 160804910859569342334775

theorem tailTrace_1409249 : CollatzResearch.WordTrace tailWord_1409249 prefixEnd_1409249 160804910859569342334775 := by
  unfold tailWord_1409249
  simp only [CollatzResearch.WordTrace]
  refine ⟨51399533671539028412750801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34266355781026018941833867 51399533671539028412750801)
  ·
    refine ⟨38549650253654271309563101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51399533671539028412750801 38549650253654271309563101)
    ·
      refine ⟨14456118845120351741086163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38549650253654271309563101 14456118845120351741086163)
      ·
        refine ⟨21684178267680527611629245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14456118845120351741086163 21684178267680527611629245)
        ·
          refine ⟨8131566850380197854360967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21684178267680527611629245 8131566850380197854360967)
          ·
            refine ⟨12197350275570296781541451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8131566850380197854360967 12197350275570296781541451)
            ·
              refine ⟨18296025413355445172312177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12197350275570296781541451 18296025413355445172312177)
              ·
                refine ⟨13722019060016583879234133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18296025413355445172312177 13722019060016583879234133)
                ·
                  refine ⟨160804910859569342334775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13722019060016583879234133 160804910859569342334775)
                  ·
                    rfl

theorem cell22_1409249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_1409249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409249 prefixEnd_1409249 := by exact prefixLift 1409249
  have htrace : WordTrace (prefixWord ++ tailWord_1409249) baseStart_1409249 baseEnd_1409249 := by
    simpa [prefixWord, tailWord_1409249, baseEnd_1409249] using wordTrace_append hprefix tailTrace_1409249
  have hstable : (prefixWord ++ tailWord_1409249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409249).length < 2 ^ (prefixWord ++ tailWord_1409249).sum := by decide
  have hdescent : baseEnd_1409249 < baseStart_1409249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409264 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_1409264 : Nat := 118140960795 + 1409264 * 2 ^ 59
def prefixEnd_1409264 : Nat := 4983230072969 + 3 ^ 40 * 1409264 * 2
def baseEnd_1409264 : Nat := 482419867385252987879279

theorem tailTrace_1409264 : CollatzResearch.WordTrace tailWord_1409264 prefixEnd_1409264 482419867385252987879279 := by
  unfold tailWord_1409264
  simp only [CollatzResearch.WordTrace]
  refine ⟨25700040383242342987273423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34266720510989790649697897 25700040383242342987273423)
  ·
    refine ⟨38550060574863514480910135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25700040383242342987273423 38550060574863514480910135)
    ·
      refine ⟨57825090862295271721365203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38550060574863514480910135 57825090862295271721365203)
      ·
        refine ⟨86737636293442907582047805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57825090862295271721365203 86737636293442907582047805)
        ·
          refine ⟨32526613610041090343267927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86737636293442907582047805 32526613610041090343267927)
          ·
            refine ⟨48789920415061635514901891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32526613610041090343267927 48789920415061635514901891)
            ·
              refine ⟨73184880622592453272352837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48789920415061635514901891 73184880622592453272352837)
              ·
                refine ⟨13722165116736084988566157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73184880622592453272352837 13722165116736084988566157)
                ·
                  refine ⟨5145811918776031870712309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13722165116736084988566157 5145811918776031870712309)
                  ·
                    refine ⟨482419867385252987879279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5145811918776031870712309 482419867385252987879279)
                    ·
                      rfl

theorem cell22_1409264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_1409264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409264 prefixEnd_1409264 := by exact prefixLift 1409264
  have htrace : WordTrace (prefixWord ++ tailWord_1409264) baseStart_1409264 baseEnd_1409264 := by
    simpa [prefixWord, tailWord_1409264, baseEnd_1409264] using wordTrace_append hprefix tailTrace_1409264
  have hstable : (prefixWord ++ tailWord_1409264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409264).length < 2 ^ (prefixWord ++ tailWord_1409264).sum := by decide
  have hdescent : baseEnd_1409264 < baseStart_1409264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409266 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_1409266 : Nat := 118140960795 + 1409266 * 2 ^ 59
def prefixEnd_1409266 : Nat := 4983230072969 + 3 ^ 40 * 1409266 * 2
def baseEnd_1409266 : Nat := 160806850675375216443091

theorem tailTrace_1409266 : CollatzResearch.WordTrace tailWord_1409266 prefixEnd_1409266 160806850675375216443091 := by
  unfold tailWord_1409266
  simp only [CollatzResearch.WordTrace]
  refine ⟨12850038428119360079029913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34266769141651626877413101 12850038428119360079029913)
  ·
    refine ⟨9637528821089520059272435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12850038428119360079029913 9637528821089520059272435)
    ·
      refine ⟨14456293231634280088908653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9637528821089520059272435 14456293231634280088908653)
      ·
        refine ⟨5421109961862855033340745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14456293231634280088908653 5421109961862855033340745)
        ·
          refine ⟨4065832471397141275005559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5421109961862855033340745 4065832471397141275005559)
          ·
            refine ⟨6098748707095711912508339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4065832471397141275005559 6098748707095711912508339)
            ·
              refine ⟨9148123060643567868762509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6098748707095711912508339 9148123060643567868762509)
              ·
                refine ⟨3430546147741337950785941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9148123060643567868762509 3430546147741337950785941)
                ·
                  refine ⟨160806850675375216443091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3430546147741337950785941 160806850675375216443091)
                  ·
                    rfl

theorem cell22_1409266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_1409266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409266 prefixEnd_1409266 := by exact prefixLift 1409266
  have htrace : WordTrace (prefixWord ++ tailWord_1409266) baseStart_1409266 baseEnd_1409266 := by
    simpa [prefixWord, tailWord_1409266, baseEnd_1409266] using wordTrace_append hprefix tailTrace_1409266
  have hstable : (prefixWord ++ tailWord_1409266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409266).length < 2 ^ (prefixWord ++ tailWord_1409266).sum := by decide
  have hdescent : baseEnd_1409266 < baseStart_1409266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409279 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 3, 6]
def baseStart_1409279 : Nat := 118140960795 + 1409279 * 2 ^ 59
def prefixEnd_1409279 : Nat := 4983230072969 + 3 ^ 40 * 1409279 * 2
def baseEnd_1409279 : Nat := 482425002191797948754233

theorem tailTrace_1409279 : CollatzResearch.WordTrace tailWord_1409279 prefixEnd_1409279 482425002191797948754233 := by
  unfold tailWord_1409279
  simp only [CollatzResearch.WordTrace]
  refine ⟨51400627861430343536342891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34267085240953562357561927 51400627861430343536342891)
  ·
    refine ⟨77100941792145515304514337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51400627861430343536342891 77100941792145515304514337)
    ·
      refine ⟨57825706344109136478385753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77100941792145515304514337 57825706344109136478385753)
      ·
        refine ⟨43369279758081852358789315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57825706344109136478385753 43369279758081852358789315)
        ·
          refine ⟨65053919637122778538183973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43369279758081852358789315 65053919637122778538183973)
          ·
            refine ⟨12197609931960520975909495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65053919637122778538183973 12197609931960520975909495)
            ·
              refine ⟨18296414897940781463864243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12197609931960520975909495 18296414897940781463864243)
              ·
                refine ⟨27444622346911172195796365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18296414897940781463864243 27444622346911172195796365)
                ·
                  refine ⟨10291733380091689573423637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27444622346911172195796365 10291733380091689573423637)
                  ·
                    refine ⟨482425002191797948754233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10291733380091689573423637 482425002191797948754233)
                    ·
                      rfl

theorem cell22_1409279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_1409279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409279 prefixEnd_1409279 := by exact prefixLift 1409279
  have htrace : WordTrace (prefixWord ++ tailWord_1409279) baseStart_1409279 baseEnd_1409279 := by
    simpa [prefixWord, tailWord_1409279, baseEnd_1409279] using wordTrace_append hprefix tailTrace_1409279
  have hstable : (prefixWord ++ tailWord_1409279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409279).length < 2 ^ (prefixWord ++ tailWord_1409279).sum := by decide
  have hdescent : baseEnd_1409279 < baseStart_1409279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409311 : List Nat := [1, 1, 2, 4, 3, 3, 8]
def baseStart_1409311 : Nat := 118140960795 + 1409311 * 2 ^ 59
def prefixEnd_1409311 : Nat := 4983230072969 + 3 ^ 40 * 1409311 * 2
def baseEnd_1409311 : Nat := 17867998386880019702005

theorem tailTrace_1409311 : CollatzResearch.WordTrace tailWord_1409311 prefixEnd_1409311 17867998386880019702005 := by
  unfold tailWord_1409311
  simp only [CollatzResearch.WordTrace]
  refine ⟨51401794997314413001507787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34267863331542942001005191 51401794997314413001507787)
  ·
    refine ⟨77102692495971619502261681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51401794997314413001507787 77102692495971619502261681)
    ·
      refine ⟨57827019371978714626696261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77102692495971619502261681 57827019371978714626696261)
      ·
        refine ⟨10842566132246008992505549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57827019371978714626696261 10842566132246008992505549)
        ·
          refine ⟨4065962299592253372189581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10842566132246008992505549 4065962299592253372189581)
          ·
            refine ⟨1524735862347095014571093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4065962299592253372189581 1524735862347095014571093)
            ·
              refine ⟨17867998386880019702005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1524735862347095014571093 17867998386880019702005)
              ·
                rfl

theorem cell22_1409311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 8].length) (baseStart_1409311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409311 prefixEnd_1409311 := by exact prefixLift 1409311
  have htrace : WordTrace (prefixWord ++ tailWord_1409311) baseStart_1409311 baseEnd_1409311 := by
    simpa [prefixWord, tailWord_1409311, baseEnd_1409311] using wordTrace_append hprefix tailTrace_1409311
  have hstable : (prefixWord ++ tailWord_1409311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409311).length < 2 ^ (prefixWord ++ tailWord_1409311).sum := by decide
  have hdescent : baseEnd_1409311 < baseStart_1409311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409332 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1409332 : Nat := 118140960795 + 1409332 * 2 ^ 59
def prefixEnd_1409332 : Nat := 4983230072969 + 3 ^ 40 * 1409332 * 2
def baseEnd_1409332 : Nat := 482443145174923477179071

theorem tailTrace_1409332 : CollatzResearch.WordTrace tailWord_1409332 prefixEnd_1409332 482443145174923477179071 := by
  unfold tailWord_1409332
  simp only [CollatzResearch.WordTrace]
  refine ⟨25701280465119166794011125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34268373953492222392014833 25701280465119166794011125)
  ·
    refine ⟨2409495043604921886938543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25701280465119166794011125 2409495043604921886938543)
    ·
      refine ⟨3614242565407382830407815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2409495043604921886938543 3614242565407382830407815)
      ·
        refine ⟨5421363848111074245611723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614242565407382830407815 5421363848111074245611723)
        ·
          refine ⟨8132045772166611368417585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5421363848111074245611723 8132045772166611368417585)
          ·
            refine ⟨6099034329124958526313189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8132045772166611368417585 6099034329124958526313189)
            ·
              refine ⟨1143568936710929723683723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6099034329124958526313189 1143568936710929723683723)
              ·
                refine ⟨1715353405066394585525585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143568936710929723683723 1715353405066394585525585)
                ·
                  refine ⟨1286515053799795939144189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1715353405066394585525585 1286515053799795939144189)
                  ·
                    refine ⟨482443145174923477179071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1286515053799795939144189 482443145174923477179071)
                    ·
                      rfl

theorem cell22_1409332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1409332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409332 prefixEnd_1409332 := by exact prefixLift 1409332
  have htrace : WordTrace (prefixWord ++ tailWord_1409332) baseStart_1409332 baseEnd_1409332 := by
    simpa [prefixWord, tailWord_1409332, baseEnd_1409332] using wordTrace_append hprefix tailTrace_1409332
  have hstable : (prefixWord ++ tailWord_1409332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409332).length < 2 ^ (prefixWord ++ tailWord_1409332).sum := by decide
  have hdescent : baseEnd_1409332 < baseStart_1409332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409388 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_1409388 : Nat := 118140960795 + 1409388 * 2 ^ 59
def prefixEnd_1409388 : Nat := 4983230072969 + 3 ^ 40 * 1409388 * 2
def baseEnd_1409388 : Nat := 482462315119357997778899

theorem tailTrace_1409388 : CollatzResearch.WordTrace tailWord_1409388 prefixEnd_1409388 482462315119357997778899 := by
  unfold tailWord_1409388
  simp only [CollatzResearch.WordTrace]
  refine ⟨25702301709017727576030409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34269735612023636768040545 25702301709017727576030409)
  ·
    refine ⟨19276726281763295682022807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25702301709017727576030409 19276726281763295682022807)
    ·
      refine ⟨28915089422644943523034211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19276726281763295682022807 28915089422644943523034211)
      ·
        refine ⟨43372634133967415284551317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28915089422644943523034211 43372634133967415284551317)
        ·
          refine ⟨2033092225029722591463343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43372634133967415284551317 2033092225029722591463343)
          ·
            refine ⟨3049638337544583887195015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033092225029722591463343 3049638337544583887195015)
            ·
              refine ⟨4574457506316875830792523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3049638337544583887195015 4574457506316875830792523)
              ·
                refine ⟨6861686259475313746188785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574457506316875830792523 6861686259475313746188785)
                ·
                  refine ⟨5146264694606485309641589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6861686259475313746188785 5146264694606485309641589)
                  ·
                    refine ⟨482462315119357997778899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5146264694606485309641589 482462315119357997778899)
                    ·
                      rfl

theorem cell22_1409388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_1409388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409388 prefixEnd_1409388 := by exact prefixLift 1409388
  have htrace : WordTrace (prefixWord ++ tailWord_1409388) baseStart_1409388 baseEnd_1409388 := by
    simpa [prefixWord, tailWord_1409388, baseEnd_1409388] using wordTrace_append hprefix tailTrace_1409388
  have hstable : (prefixWord ++ tailWord_1409388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409388).length < 2 ^ (prefixWord ++ tailWord_1409388).sum := by decide
  have hdescent : baseEnd_1409388 < baseStart_1409388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409420 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 1, 4]
def baseStart_1409420 : Nat := 118140960795 + 1409420 * 2 ^ 59
def prefixEnd_1409420 : Nat := 4983230072969 + 3 ^ 40 * 1409420 * 2
def baseEnd_1409420 : Nat := 482473269373320580978801

theorem tailTrace_1409420 : CollatzResearch.WordTrace tailWord_1409420 prefixEnd_1409420 482473269373320580978801 := by
  unfold tailWord_1409420
  simp only [CollatzResearch.WordTrace]
  refine ⟨25702885276959762308612857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34270513702613016411483809 25702885276959762308612857)
  ·
    refine ⟨19277163957719821731459643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25702885276959762308612857 19277163957719821731459643)
    ·
      refine ⟨28915745936579732597189465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19277163957719821731459643 28915745936579732597189465)
      ·
        refine ⟨21686809452434799447892099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28915745936579732597189465 21686809452434799447892099)
        ·
          refine ⟨32530214178652199171838149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21686809452434799447892099 32530214178652199171838149)
          ·
            refine ⟨6099415158497287344719653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32530214178652199171838149 6099415158497287344719653)
            ·
              refine ⟨1143640342218241377134935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6099415158497287344719653 1143640342218241377134935)
              ·
                refine ⟨1715460513327362065702403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143640342218241377134935 1715460513327362065702403)
                ·
                  refine ⟨2573190769991043098553605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715460513327362065702403 2573190769991043098553605)
                  ·
                    refine ⟨482473269373320580978801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2573190769991043098553605 482473269373320580978801)
                    ·
                      rfl

theorem cell22_1409420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_1409420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409420 prefixEnd_1409420 := by exact prefixLift 1409420
  have htrace : WordTrace (prefixWord ++ tailWord_1409420) baseStart_1409420 baseEnd_1409420 := by
    simpa [prefixWord, tailWord_1409420, baseEnd_1409420] using wordTrace_append hprefix tailTrace_1409420
  have hstable : (prefixWord ++ tailWord_1409420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409420).length < 2 ^ (prefixWord ++ tailWord_1409420).sum := by decide
  have hdescent : baseEnd_1409420 < baseStart_1409420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409433 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 4, 3]
def baseStart_1409433 : Nat := 118140960795 + 1409433 * 2 ^ 59
def prefixEnd_1409433 : Nat := 4983230072969 + 3 ^ 40 * 1409433 * 2
def baseEnd_1409433 : Nat := 482477719538992880403761

theorem tailTrace_1409433 : CollatzResearch.WordTrace tailWord_1409433 prefixEnd_1409433 482477719538992880403761 := by
  unfold tailWord_1409433
  simp only [CollatzResearch.WordTrace]
  refine ⟨51406244702872427837448953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34270829801914951891632635 51406244702872427837448953)
  ·
    refine ⟨38554683527154320878086715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51406244702872427837448953 38554683527154320878086715)
    ·
      refine ⟨57832025290731481317130073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38554683527154320878086715 57832025290731481317130073)
      ·
        refine ⟨43374018968048610987847555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57832025290731481317130073 43374018968048610987847555)
        ·
          refine ⟨65061028452072916481771333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43374018968048610987847555 65061028452072916481771333)
          ·
            refine ⟨12198942834763671840332125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65061028452072916481771333 12198942834763671840332125)
            ·
              refine ⟨4574603563036376940124547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12198942834763671840332125 4574603563036376940124547)
              ·
                refine ⟨6861905344554565410186821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574603563036376940124547 6861905344554565410186821)
                ·
                  refine ⟨1286607252103981014410029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6861905344554565410186821 1286607252103981014410029)
                  ·
                    refine ⟨482477719538992880403761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1286607252103981014410029 482477719538992880403761)
                    ·
                      rfl

theorem cell22_1409433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_1409433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409433 prefixEnd_1409433 := by exact prefixLift 1409433
  have htrace : WordTrace (prefixWord ++ tailWord_1409433) baseStart_1409433 baseEnd_1409433 := by
    simpa [prefixWord, tailWord_1409433, baseEnd_1409433] using wordTrace_append hprefix tailTrace_1409433
  have hstable : (prefixWord ++ tailWord_1409433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409433).length < 2 ^ (prefixWord ++ tailWord_1409433).sum := by decide
  have hdescent : baseEnd_1409433 < baseStart_1409433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409463 : List Nat := [1, 1, 3, 1, 3, 3, 4, 6]
def baseStart_1409463 : Nat := 118140960795 + 1409463 * 2 ^ 59
def prefixEnd_1409463 : Nat := 4983230072969 + 3 ^ 40 * 1409463 * 2
def baseEnd_1409463 : Nat := 53609776572453644683741

theorem tailTrace_1409463 : CollatzResearch.WordTrace tailWord_1409463 prefixEnd_1409463 53609776572453644683741 := by
  unfold tailWord_1409463
  simp only [CollatzResearch.WordTrace]
  refine ⟨51407338892763742961041043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34271559261842495307360695 51407338892763742961041043)
  ·
    refine ⟨77111008339145614441561565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51407338892763742961041043 77111008339145614441561565)
    ·
      refine ⟨28916628127179605415585587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77111008339145614441561565 28916628127179605415585587)
      ·
        refine ⟨43374942190769408123378381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28916628127179605415585587 43374942190769408123378381)
        ·
          refine ⟨16265603321538528046266893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43374942190769408123378381 16265603321538528046266893)
          ·
            refine ⟨6099601245576948017350085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16265603321538528046266893 6099601245576948017350085)
            ·
              refine ⟨1143675233545677753253141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6099601245576948017350085 1143675233545677753253141)
              ·
                refine ⟨53609776572453644683741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1143675233545677753253141 53609776572453644683741)
                ·
                  rfl

theorem cell22_1409463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 6].length) (baseStart_1409463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409463 prefixEnd_1409463 := by exact prefixLift 1409463
  have htrace : WordTrace (prefixWord ++ tailWord_1409463) baseStart_1409463 baseEnd_1409463 := by
    simpa [prefixWord, tailWord_1409463, baseEnd_1409463] using wordTrace_append hprefix tailTrace_1409463
  have hstable : (prefixWord ++ tailWord_1409463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409463).length < 2 ^ (prefixWord ++ tailWord_1409463).sum := by decide
  have hdescent : baseEnd_1409463 < baseStart_1409463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409666 : List Nat := [3, 4, 3, 1, 1, 1, 2, 7]
def baseStart_1409666 : Nat := 118140960795 + 1409666 * 2 ^ 59
def prefixEnd_1409666 : Nat := 4983230072969 + 3 ^ 40 * 1409666 * 2
def baseEnd_1409666 : Nat := 53617497800073104369783

theorem tailTrace_1409666 : CollatzResearch.WordTrace tailWord_1409666 prefixEnd_1409666 53617497800073104369783 := by
  unfold tailWord_1409666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12853685727757077157670213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34276495274018872420453901 12853685727757077157670213)
  ·
    refine ⟨2410066073954451967063165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12853685727757077157670213 2410066073954451967063165)
    ·
      refine ⟨903774777732919487648687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2410066073954451967063165 903774777732919487648687)
      ·
        refine ⟨1355662166599379231473031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903774777732919487648687 1355662166599379231473031)
        ·
          refine ⟨2033493249899068847209547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355662166599379231473031 2033493249899068847209547)
          ·
            refine ⟨3050239874848603270814321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033493249899068847209547 3050239874848603270814321)
            ·
              refine ⟨2287679906136452453110741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3050239874848603270814321 2287679906136452453110741)
              ·
                refine ⟨53617497800073104369783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2287679906136452453110741 53617497800073104369783)
                ·
                  rfl

theorem cell22_1409666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_1409666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409666 prefixEnd_1409666 := by exact prefixLift 1409666
  have htrace : WordTrace (prefixWord ++ tailWord_1409666) baseStart_1409666 baseEnd_1409666 := by
    simpa [prefixWord, tailWord_1409666, baseEnd_1409666] using wordTrace_append hprefix tailTrace_1409666
  have hstable : (prefixWord ++ tailWord_1409666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409666).length < 2 ^ (prefixWord ++ tailWord_1409666).sum := by decide
  have hdescent : baseEnd_1409666 < baseStart_1409666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409673 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_1409673 : Nat := 118140960795 + 1409673 * 2 ^ 59
def prefixEnd_1409673 : Nat := 4983230072969 + 3 ^ 40 * 1409673 * 2
def baseEnd_1409673 : Nat := 482559876443712254403025

theorem tailTrace_1409673 : CollatzResearch.WordTrace tailWord_1409673 prefixEnd_1409673 482559876443712254403025 := by
  unfold tailWord_1409673
  simp only [CollatzResearch.WordTrace]
  refine ⟨51414998222002948826185673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34276665481335299217457115 51414998222002948826185673)
  ·
    refine ⟨38561248666502211619639255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51414998222002948826185673 38561248666502211619639255)
    ·
      refine ⟨57841872999753317429458883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38561248666502211619639255 57841872999753317429458883)
      ·
        refine ⟨86762809499629976144188325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57841872999753317429458883 86762809499629976144188325)
        ·
          refine ⟨16268026781180620527035311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86762809499629976144188325 16268026781180620527035311)
          ·
            refine ⟨24402040171770930790552967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16268026781180620527035311 24402040171770930790552967)
            ·
              refine ⟨36603060257656396185829451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24402040171770930790552967 36603060257656396185829451)
              ·
                refine ⟨54904590386484594278744177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36603060257656396185829451 54904590386484594278744177)
                ·
                  refine ⟨41178442789863445709058133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54904590386484594278744177 41178442789863445709058133)
                  ·
                    refine ⟨482559876443712254403025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41178442789863445709058133 482559876443712254403025)
                    ·
                      rfl

theorem cell22_1409673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_1409673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409673 prefixEnd_1409673 := by exact prefixLift 1409673
  have htrace : WordTrace (prefixWord ++ tailWord_1409673) baseStart_1409673 baseEnd_1409673 := by
    simpa [prefixWord, tailWord_1409673, baseEnd_1409673] using wordTrace_append hprefix tailTrace_1409673
  have hstable : (prefixWord ++ tailWord_1409673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409673).length < 2 ^ (prefixWord ++ tailWord_1409673).sum := by decide
  have hdescent : baseEnd_1409673 < baseStart_1409673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409722 : List Nat := [3, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_1409722 : Nat := 118140960795 + 1409722 * 2 ^ 59
def prefixEnd_1409722 : Nat := 4983230072969 + 3 ^ 40 * 1409722 * 2
def baseEnd_1409722 : Nat := 160858883381697486642625

theorem tailTrace_1409722 : CollatzResearch.WordTrace tailWord_1409722 prefixEnd_1409722 160858883381697486642625 := by
  unfold tailWord_1409722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12854196349706357548679855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34277856932550286796479613 12854196349706357548679855)
  ·
    refine ⟨19281294524559536323019783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12854196349706357548679855 19281294524559536323019783)
    ·
      refine ⟨28921941786839304484529675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19281294524559536323019783 28921941786839304484529675)
      ·
        refine ⟨43382912680258956726794513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28921941786839304484529675 43382912680258956726794513)
        ·
          refine ⟨32537184510194217545095885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43382912680258956726794513 32537184510194217545095885)
          ·
            refine ⟨12201444191322831579410957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32537184510194217545095885 12201444191322831579410957)
            ·
              refine ⟨4575541571746061842279109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12201444191322831579410957 4575541571746061842279109)
              ·
                refine ⟨857914044702386595427333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4575541571746061842279109 857914044702386595427333)
                ·
                  refine ⟨160858883381697486642625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857914044702386595427333 160858883381697486642625)
                  ·
                    rfl

theorem cell22_1409722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_1409722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409722 prefixEnd_1409722 := by exact prefixLift 1409722
  have htrace : WordTrace (prefixWord ++ tailWord_1409722) baseStart_1409722 baseEnd_1409722 := by
    simpa [prefixWord, tailWord_1409722, baseEnd_1409722] using wordTrace_append hprefix tailTrace_1409722
  have hstable : (prefixWord ++ tailWord_1409722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409722).length < 2 ^ (prefixWord ++ tailWord_1409722).sum := by decide
  have hdescent : baseEnd_1409722 < baseStart_1409722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409752 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_1409752 : Nat := 118140960795 + 1409752 * 2 ^ 59
def prefixEnd_1409752 : Nat := 4983230072969 + 3 ^ 40 * 1409752 * 2
def baseEnd_1409752 : Nat := 482586919758182381677783

theorem tailTrace_1409752 : CollatzResearch.WordTrace tailWord_1409752 prefixEnd_1409752 482586919758182381677783 := by
  unfold tailWord_1409752
  simp only [CollatzResearch.WordTrace]
  refine ⟨25708939794358372659155755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34278586392477830212207673 25708939794358372659155755)
  ·
    refine ⟨38563409691537558988733633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25708939794358372659155755 38563409691537558988733633)
    ·
      refine ⟨28922557268653169241550225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38563409691537558988733633 28922557268653169241550225)
      ·
        refine ⟨21691917951489876931162669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28922557268653169241550225 21691917951489876931162669)
        ·
          refine ⟨8134469231808703849186001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21691917951489876931162669 8134469231808703849186001)
          ·
            refine ⟨6100851923856527886889501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8134469231808703849186001 6100851923856527886889501)
            ·
              refine ⟨2287819471446197957583563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6100851923856527886889501 2287819471446197957583563)
              ·
                refine ⟨3431729207169296936375345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287819471446197957583563 3431729207169296936375345)
                ·
                  refine ⟨2573796905376972702281509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431729207169296936375345 2573796905376972702281509)
                  ·
                    refine ⟨482586919758182381677783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2573796905376972702281509 482586919758182381677783)
                    ·
                      rfl

theorem cell22_1409752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_1409752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409752 prefixEnd_1409752 := by exact prefixLift 1409752
  have htrace : WordTrace (prefixWord ++ tailWord_1409752) baseStart_1409752 baseEnd_1409752 := by
    simpa [prefixWord, tailWord_1409752, baseEnd_1409752] using wordTrace_append hprefix tailTrace_1409752
  have hstable : (prefixWord ++ tailWord_1409752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409752).length < 2 ^ (prefixWord ++ tailWord_1409752).sum := by decide
  have hdescent : baseEnd_1409752 < baseStart_1409752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409756 : List Nat := [2, 2, 5, 1, 1, 2, 2, 3, 4]
def baseStart_1409756 : Nat := 118140960795 + 1409756 * 2 ^ 59
def prefixEnd_1409756 : Nat := 4983230072969 + 3 ^ 40 * 1409756 * 2
def baseEnd_1409756 : Nat := 160862763013309234859257

theorem tailTrace_1409756 : CollatzResearch.WordTrace tailWord_1409756 prefixEnd_1409756 160862763013309234859257 := by
  unfold tailWord_1409756
  simp only [CollatzResearch.WordTrace]
  refine ⟨25709012740351127000728561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34278683653801502667638081 25709012740351127000728561)
  ·
    refine ⟨19281759555263345250546421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25709012740351127000728561 19281759555263345250546421)
    ·
      refine ⟨1807664958305938617238727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19281759555263345250546421 1807664958305938617238727)
      ·
        refine ⟨2711497437458907925858091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1807664958305938617238727 2711497437458907925858091)
        ·
          refine ⟨4067246156188361888787137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2711497437458907925858091 4067246156188361888787137)
          ·
            refine ⟨3050434617141271416590353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4067246156188361888787137 3050434617141271416590353)
            ·
              refine ⟨2287825962855953562442765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3050434617141271416590353 2287825962855953562442765)
              ·
                refine ⟨857934736070982585916037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2287825962855953562442765 857934736070982585916037)
                ·
                  refine ⟨160862763013309234859257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857934736070982585916037 160862763013309234859257)
                  ·
                    rfl

theorem cell22_1409756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_1409756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409756 prefixEnd_1409756 := by exact prefixLift 1409756
  have htrace : WordTrace (prefixWord ++ tailWord_1409756) baseStart_1409756 baseEnd_1409756 := by
    simpa [prefixWord, tailWord_1409756, baseEnd_1409756] using wordTrace_append hprefix tailTrace_1409756
  have hstable : (prefixWord ++ tailWord_1409756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409756).length < 2 ^ (prefixWord ++ tailWord_1409756).sum := by decide
  have hdescent : baseEnd_1409756 < baseStart_1409756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409799 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 3, 3]
def baseStart_1409799 : Nat := 118140960795 + 1409799 * 2 ^ 59
def prefixEnd_1409799 : Nat := 4983230072969 + 3 ^ 40 * 1409799 * 2
def baseEnd_1409799 : Nat := 482603008818689925752639

theorem tailTrace_1409799 : CollatzResearch.WordTrace tailWord_1409799 prefixEnd_1409799 482603008818689925752639 := by
  unfold tailWord_1409799
  simp only [CollatzResearch.WordTrace]
  refine ⟨51419593819546472345272451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34279729213030981563514967 51419593819546472345272451)
  ·
    refine ⟨77129390729319708517908677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51419593819546472345272451 77129390729319708517908677)
    ·
      refine ⟨14461760761747445347107877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77129390729319708517908677 14461760761747445347107877)
      ·
        refine ⟨2711580142827646002582727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14461760761747445347107877 2711580142827646002582727)
        ·
          refine ⟨4067370214241469003874091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2711580142827646002582727 4067370214241469003874091)
          ·
            refine ⟨6101055321362203505811137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067370214241469003874091 6101055321362203505811137)
            ·
              refine ⟨4575791491021652629358353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6101055321362203505811137 4575791491021652629358353)
              ·
                refine ⟨3431843618266239472018765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4575791491021652629358353 3431843618266239472018765)
                ·
                  refine ⟨1286941356849839802007037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3431843618266239472018765 1286941356849839802007037)
                  ·
                    refine ⟨482603008818689925752639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1286941356849839802007037 482603008818689925752639)
                    ·
                      rfl

theorem cell22_1409799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_1409799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409799 prefixEnd_1409799 := by exact prefixLift 1409799
  have htrace : WordTrace (prefixWord ++ tailWord_1409799) baseStart_1409799 baseEnd_1409799 := by
    simpa [prefixWord, tailWord_1409799, baseEnd_1409799] using wordTrace_append hprefix tailTrace_1409799
  have hstable : (prefixWord ++ tailWord_1409799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409799).length < 2 ^ (prefixWord ++ tailWord_1409799).sum := by decide
  have hdescent : baseEnd_1409799 < baseStart_1409799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409842 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_1409842 : Nat := 118140960795 + 1409842 * 2 ^ 59
def prefixEnd_1409842 : Nat := 4983230072969 + 3 ^ 40 * 1409842 * 2
def baseEnd_1409842 : Nat := 482617728597452146927507

theorem tailTrace_1409842 : CollatzResearch.WordTrace tailWord_1409842 prefixEnd_1409842 482617728597452146927507 := by
  unfold tailWord_1409842
  simp only [CollatzResearch.WordTrace]
  refine ⟨12855290539597672672271945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34280774772260460459391853 12855290539597672672271945)
  ·
    refine ⟨9641467904698254504203959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12855290539597672672271945 9641467904698254504203959)
    ·
      refine ⟨14462201857047381756305939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9641467904698254504203959 14462201857047381756305939)
      ·
        refine ⟨21693302785571072634458909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14462201857047381756305939 21693302785571072634458909)
        ·
          refine ⟨8134988544589152237922091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21693302785571072634458909 8134988544589152237922091)
          ·
            refine ⟨12202482816883728356883137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8134988544589152237922091 12202482816883728356883137)
            ·
              refine ⟨9151862112662796267662353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12202482816883728356883137 9151862112662796267662353)
              ·
                refine ⟨6863896584497097200746765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9151862112662796267662353 6863896584497097200746765)
                ·
                  refine ⟨2573961219186411450280037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6863896584497097200746765 2573961219186411450280037)
                  ·
                    refine ⟨482617728597452146927507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2573961219186411450280037 482617728597452146927507)
                    ·
                      rfl

theorem cell22_1409842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_1409842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409842 prefixEnd_1409842 := by exact prefixLift 1409842
  have htrace : WordTrace (prefixWord ++ tailWord_1409842) baseStart_1409842 baseEnd_1409842 := by
    simpa [prefixWord, tailWord_1409842, baseEnd_1409842] using wordTrace_append hprefix tailTrace_1409842
  have hstable : (prefixWord ++ tailWord_1409842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409842).length < 2 ^ (prefixWord ++ tailWord_1409842).sum := by decide
  have hdescent : baseEnd_1409842 < baseStart_1409842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409846 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_1409846 : Nat := 118140960795 + 1409846 * 2 ^ 59
def prefixEnd_1409846 : Nat := 4983230072969 + 3 ^ 40 * 1409846 * 2
def baseEnd_1409846 : Nat := 160873032626399156609165

theorem tailTrace_1409846 : CollatzResearch.WordTrace tailWord_1409846 prefixEnd_1409846 160873032626399156609165 := by
  unfold tailWord_1409846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213831753148512460764587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34280872033584132914822261 3213831753148512460764587)
  ·
    refine ⟨4820747629722768691146881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3213831753148512460764587 4820747629722768691146881)
    ·
      refine ⟨3615560722292076518360161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4820747629722768691146881 3615560722292076518360161)
      ·
        refine ⟨2711670541719057388770121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3615560722292076518360161 2711670541719057388770121)
        ·
          refine ⟨2033752906289293041577591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2711670541719057388770121 2033752906289293041577591)
          ·
            refine ⟨3050629359433939562366387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033752906289293041577591 3050629359433939562366387)
            ·
              refine ⟨4575944039150909343549581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050629359433939562366387 4575944039150909343549581)
              ·
                refine ⟨1715979014681591003831093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4575944039150909343549581 1715979014681591003831093)
                ·
                  refine ⟨160873032626399156609165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1715979014681591003831093 160873032626399156609165)
                  ·
                    rfl

theorem cell22_1409846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_1409846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409846 prefixEnd_1409846 := by exact prefixLift 1409846
  have htrace : WordTrace (prefixWord ++ tailWord_1409846) baseStart_1409846 baseEnd_1409846 := by
    simpa [prefixWord, tailWord_1409846, baseEnd_1409846] using wordTrace_append hprefix tailTrace_1409846
  have hstable : (prefixWord ++ tailWord_1409846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409846).length < 2 ^ (prefixWord ++ tailWord_1409846).sum := by decide
  have hdescent : baseEnd_1409846 < baseStart_1409846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409872 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 6, 3]
def baseStart_1409872 : Nat := 118140960795 + 1409872 * 2 ^ 59
def prefixEnd_1409872 : Nat := 4983230072969 + 3 ^ 40 * 1409872 * 2
def baseEnd_1409872 : Nat := 482627998210542068677415

theorem tailTrace_1409872 : CollatzResearch.WordTrace tailWord_1409872 prefixEnd_1409872 482627998210542068677415 := by
  unfold tailWord_1409872
  simp only [CollatzResearch.WordTrace]
  refine ⟨25711128174141002906339935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34281504232188003875119913 25711128174141002906339935)
  ·
    refine ⟨38566692261211504359509903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25711128174141002906339935 38566692261211504359509903)
    ·
      refine ⟨57850038391817256539264855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38566692261211504359509903 57850038391817256539264855)
      ·
        refine ⟨86775057587725884808897283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57850038391817256539264855 86775057587725884808897283)
        ·
          refine ⟨130162586381588827213345925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86775057587725884808897283 130162586381588827213345925)
          ·
            refine ⟨24405484946547905102502361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130162586381588827213345925 24405484946547905102502361)
            ·
              refine ⟨18304113709910928826876771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24405484946547905102502361 18304113709910928826876771)
              ·
                refine ⟨27456170564866393240315157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18304113709910928826876771 27456170564866393240315157)
                ·
                  refine ⟨1287007995228112183139773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27456170564866393240315157 1287007995228112183139773)
                  ·
                    refine ⟨482627998210542068677415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1287007995228112183139773 482627998210542068677415)
                    ·
                      rfl

theorem cell22_1409872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_1409872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409872 prefixEnd_1409872 := by exact prefixLift 1409872
  have htrace : WordTrace (prefixWord ++ tailWord_1409872) baseStart_1409872 baseEnd_1409872 := by
    simpa [prefixWord, tailWord_1409872, baseEnd_1409872] using wordTrace_append hprefix tailTrace_1409872
  have hstable : (prefixWord ++ tailWord_1409872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409872).length < 2 ^ (prefixWord ++ tailWord_1409872).sum := by decide
  have hdescent : baseEnd_1409872 < baseStart_1409872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409874 : List Nat := [3, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_1409874 : Nat := 118140960795 + 1409874 * 2 ^ 59
def prefixEnd_1409874 : Nat := 4983230072969 + 3 ^ 40 * 1409874 * 2
def baseEnd_1409874 : Nat := 160876227617138243375803

theorem tailTrace_1409874 : CollatzResearch.WordTrace tailWord_1409874 prefixEnd_1409874 160876227617138243375803 := by
  unfold tailWord_1409874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12855582323568690038563169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34281552862849840102835117 12855582323568690038563169)
  ·
    refine ⟨9641686742676517528922377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12855582323568690038563169 9641686742676517528922377)
    ·
      refine ⟨7231265057007388146691783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9641686742676517528922377 7231265057007388146691783)
      ·
        refine ⟨10846897585511082220037675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7231265057007388146691783 10846897585511082220037675)
        ·
          refine ⟨16270346378266623330056513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10846897585511082220037675 16270346378266623330056513)
          ·
            refine ⟨12202759783699967497542385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16270346378266623330056513 12202759783699967497542385)
            ·
              refine ⟨9152069837774975623156789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12202759783699967497542385 9152069837774975623156789)
              ·
                refine ⟨858006547291403964670949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9152069837774975623156789 858006547291403964670949)
                ·
                  refine ⟨160876227617138243375803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858006547291403964670949 160876227617138243375803)
                  ·
                    rfl

theorem cell22_1409874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_1409874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409874 prefixEnd_1409874 := by exact prefixLift 1409874
  have htrace : WordTrace (prefixWord ++ tailWord_1409874) baseStart_1409874 baseEnd_1409874 := by
    simpa [prefixWord, tailWord_1409874, baseEnd_1409874] using wordTrace_append hprefix tailTrace_1409874
  have hstable : (prefixWord ++ tailWord_1409874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409874).length < 2 ^ (prefixWord ++ tailWord_1409874).sum := by decide
  have hdescent : baseEnd_1409874 < baseStart_1409874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409885 : List Nat := [1, 4, 17]
def baseStart_1409885 : Nat := 118140960795 + 1409885 * 2 ^ 59
def prefixEnd_1409885 : Nat := 4983230072969 + 3 ^ 40 * 1409885 * 2
def baseEnd_1409885 : Nat := 220682418096119967125

theorem tailTrace_1409885 : CollatzResearch.WordTrace tailWord_1409885 prefixEnd_1409885 220682418096119967125 := by
  unfold tailWord_1409885
  simp only [CollatzResearch.WordTrace]
  refine ⟨51422730497234909032903109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34281820331489939355268739 51422730497234909032903109)
  ·
    refine ⟨9641761968231545443669333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51422730497234909032903109 9641761968231545443669333)
    ·
      refine ⟨220682418096119967125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 9641761968231545443669333 220682418096119967125)
      ·
        rfl

theorem cell22_1409885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 17].length) (baseStart_1409885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409885 prefixEnd_1409885 := by exact prefixLift 1409885
  have htrace : WordTrace (prefixWord ++ tailWord_1409885) baseStart_1409885 baseEnd_1409885 := by
    simpa [prefixWord, tailWord_1409885, baseEnd_1409885] using wordTrace_append hprefix tailTrace_1409885
  have hstable : (prefixWord ++ tailWord_1409885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409885).length < 2 ^ (prefixWord ++ tailWord_1409885).sum := by decide
  have hdescent : baseEnd_1409885 < baseStart_1409885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409887 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 2, 4]
def baseStart_1409887 : Nat := 118140960795 + 1409887 * 2 ^ 59
def prefixEnd_1409887 : Nat := 4983230072969 + 3 ^ 40 * 1409887 * 2
def baseEnd_1409887 : Nat := 482633133017087029552369

theorem tailTrace_1409887 : CollatzResearch.WordTrace tailWord_1409887 prefixEnd_1409887 482633133017087029552369 := by
  unfold tailWord_1409887
  simp only [CollatzResearch.WordTrace]
  refine ⟨51422803443227663374475915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34281868962151775582983943 51422803443227663374475915)
  ·
    refine ⟨77134205164841495061713873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51422803443227663374475915 77134205164841495061713873)
    ·
      refine ⟨57850653873631121296285405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77134205164841495061713873 57850653873631121296285405)
      ·
        refine ⟨21693995202611670486107027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57850653873631121296285405 21693995202611670486107027)
        ·
          refine ⟨32540992803917505729160541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21693995202611670486107027 32540992803917505729160541)
          ·
            refine ⟨12202872301469064648435203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32540992803917505729160541 12202872301469064648435203)
            ·
              refine ⟨18304308452203596972652805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12202872301469064648435203 18304308452203596972652805)
              ·
                refine ⟨3432057834788174432372401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18304308452203596972652805 3432057834788174432372401)
                ·
                  refine ⟨2574043376091130824279301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3432057834788174432372401 2574043376091130824279301)
                  ·
                    refine ⟨482633133017087029552369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2574043376091130824279301 482633133017087029552369)
                    ·
                      rfl

theorem cell22_1409887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_1409887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409887 prefixEnd_1409887 := by exact prefixLift 1409887
  have htrace : WordTrace (prefixWord ++ tailWord_1409887) baseStart_1409887 baseEnd_1409887 := by
    simpa [prefixWord, tailWord_1409887, baseEnd_1409887] using wordTrace_append hprefix tailTrace_1409887
  have hstable : (prefixWord ++ tailWord_1409887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409887).length < 2 ^ (prefixWord ++ tailWord_1409887).sum := by decide
  have hdescent : baseEnd_1409887 < baseStart_1409887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409891 : List Nat := [1, 1, 1, 5, 3, 1, 4, 2, 4]
def baseStart_1409891 : Nat := 118140960795 + 1409891 * 2 ^ 59
def prefixEnd_1409891 : Nat := 4983230072969 + 3 ^ 40 * 1409891 * 2
def baseEnd_1409891 : Nat := 160878167432944117484119

theorem tailTrace_1409891 : CollatzResearch.WordTrace tailWord_1409891 prefixEnd_1409891 160878167432944117484119 := by
  unfold tailWord_1409891
  simp only [CollatzResearch.WordTrace]
  refine ⟨51422949335213172057621527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34281966223475448038414351 51422949335213172057621527)
  ·
    refine ⟨77134424002819758086432291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51422949335213172057621527 77134424002819758086432291)
    ·
      refine ⟨115701636004229637129648437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77134424002819758086432291 115701636004229637129648437)
      ·
        refine ⟨10847028375396528480904541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115701636004229637129648437 10847028375396528480904541)
        ·
          refine ⟨4067635640773698180339203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10847028375396528480904541 4067635640773698180339203)
          ·
            refine ⟨6101453461160547270508805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067635640773698180339203 6101453461160547270508805)
            ·
              refine ⟨1144022523967602613220401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6101453461160547270508805 1144022523967602613220401)
              ·
                refine ⟨858016892975701959915301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144022523967602613220401 858016892975701959915301)
                ·
                  refine ⟨160878167432944117484119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858016892975701959915301 160878167432944117484119)
                  ·
                    rfl

theorem cell22_1409891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 4].length) (baseStart_1409891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409891 prefixEnd_1409891 := by exact prefixLift 1409891
  have htrace : WordTrace (prefixWord ++ tailWord_1409891) baseStart_1409891 baseEnd_1409891 := by
    simpa [prefixWord, tailWord_1409891, baseEnd_1409891] using wordTrace_append hprefix tailTrace_1409891
  have hstable : (prefixWord ++ tailWord_1409891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409891).length < 2 ^ (prefixWord ++ tailWord_1409891).sum := by decide
  have hdescent : baseEnd_1409891 < baseStart_1409891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
