import V185TrunkScan21Chunk129

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1582652 : List Nat := [2, 2, 2, 2, 4, 1, 3, 2, 3]
def baseStart_1582652 : Nat := 118140960795 + 1582652 * 2 ^ 59
def prefixEnd_1582652 : Nat := 4983230072969 + 3 ^ 40 * 1582652 * 2
def baseEnd_1582652 : Nat := 361182748799843155765121

theorem tailTrace_1582652 : CollatzResearch.WordTrace tailWord_1582652 prefixEnd_1582652 361182748799843155765121 := by
  unfold tailWord_1582652
  simp only [CollatzResearch.WordTrace]
  refine ⟨28862030331164787143695105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38482707108219716191593473 28862030331164787143695105)
  ·
    refine ⟨21646522748373590357771329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28862030331164787143695105 21646522748373590357771329)
    ·
      refine ⟨16234892061280192768328497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21646522748373590357771329 16234892061280192768328497)
      ·
        refine ⟨12176169045960144576246373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16234892061280192768328497 12176169045960144576246373)
        ·
          refine ⟨2283031696117527108046195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12176169045960144576246373 2283031696117527108046195)
          ·
            refine ⟨3424547544176290662069293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283031696117527108046195 3424547544176290662069293)
            ·
              refine ⟨1284205329066108998275985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3424547544176290662069293 1284205329066108998275985)
              ·
                refine ⟨963153996799581748706989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284205329066108998275985 963153996799581748706989)
                ·
                  refine ⟨361182748799843155765121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963153996799581748706989 361182748799843155765121)
                  ·
                    rfl

theorem cell21_1582652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_1582652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582652 prefixEnd_1582652 := by exact prefixLift 1582652
  have htrace : WordTrace (prefixWord ++ tailWord_1582652) baseStart_1582652 baseEnd_1582652 := by
    simpa [prefixWord, tailWord_1582652, baseEnd_1582652] using wordTrace_append hprefix tailTrace_1582652
  have hstable : (prefixWord ++ tailWord_1582652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582652).length < 2 ^ (prefixWord ++ tailWord_1582652).sum := by decide
  have hdescent : baseEnd_1582652 < baseStart_1582652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582663 : List Nat := [1, 1, 4, 1, 5, 1, 2, 6]
def baseStart_1582663 : Nat := 118140960795 + 1582663 * 2 ^ 59
def prefixEnd_1582663 : Nat := 4983230072969 + 3 ^ 40 * 1582663 * 2
def baseEnd_1582663 : Nat := 120395086383236527027255

theorem tailTrace_1582663 : CollatzResearch.WordTrace tailWord_1582663 prefixEnd_1582663 120395086383236527027255 := by
  unfold tailWord_1582663
  simp only [CollatzResearch.WordTrace]
  refine ⟨57724461865289723166040643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38482974576859815444027095 57724461865289723166040643)
  ·
    refine ⟨86586692797934584749060965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57724461865289723166040643 86586692797934584749060965)
    ·
      refine ⟨16235004899612734640448931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86586692797934584749060965 16235004899612734640448931)
      ·
        refine ⟨24352507349419101960673397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16235004899612734640448931 24352507349419101960673397)
        ·
          refine ⟨2283047564008040808813131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24352507349419101960673397 2283047564008040808813131)
          ·
            refine ⟨3424571346012061213219697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283047564008040808813131 3424571346012061213219697)
            ·
              refine ⟨2568428509509045909914773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424571346012061213219697 2568428509509045909914773)
              ·
                refine ⟨120395086383236527027255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2568428509509045909914773 120395086383236527027255)
                ·
                  rfl

theorem cell21_1582663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 6].length) (baseStart_1582663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582663 prefixEnd_1582663 := by exact prefixLift 1582663
  have htrace : WordTrace (prefixWord ++ tailWord_1582663) baseStart_1582663 baseEnd_1582663 := by
    simpa [prefixWord, tailWord_1582663, baseEnd_1582663] using wordTrace_append hprefix tailTrace_1582663
  have hstable : (prefixWord ++ tailWord_1582663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582663).length < 2 ^ (prefixWord ++ tailWord_1582663).sum := by decide
  have hdescent : baseEnd_1582663 < baseStart_1582663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582767 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 6]
def baseStart_1582767 : Nat := 118140960795 + 1582767 * 2 ^ 59
def prefixEnd_1582767 : Nat := 4983230072969 + 3 ^ 40 * 1582767 * 2
def baseEnd_1582767 : Nat := 361208993366628511348219

theorem tailTrace_1582767 : CollatzResearch.WordTrace tailWord_1582767 prefixEnd_1582767 361208993366628511348219 := by
  unfold tailWord_1582767
  simp only [CollatzResearch.WordTrace]
  refine ⟨57728255056912948927826555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38485503371275299285217703 57728255056912948927826555)
  ·
    refine ⟨86592382585369423391739833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57728255056912948927826555 86592382585369423391739833)
    ·
      refine ⟨64944286939027067543804875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86592382585369423391739833 64944286939027067543804875)
      ·
        refine ⟨97416430408540601315707313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64944286939027067543804875 97416430408540601315707313)
        ·
          refine ⟨73062322806405450986780485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97416430408540601315707313 73062322806405450986780485)
          ·
            refine ⟨13699185526201022060021341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73062322806405450986780485 13699185526201022060021341)
            ·
              refine ⟨5137194572325383272508003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13699185526201022060021341 5137194572325383272508003)
              ·
                refine ⟨7705791858488074908762005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137194572325383272508003 7705791858488074908762005)
                ·
                  refine ⟨361208993366628511348219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7705791858488074908762005 361208993366628511348219)
                  ·
                    rfl

theorem cell21_1582767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_1582767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582767 prefixEnd_1582767 := by exact prefixLift 1582767
  have htrace : WordTrace (prefixWord ++ tailWord_1582767) baseStart_1582767 baseEnd_1582767 := by
    simpa [prefixWord, tailWord_1582767, baseEnd_1582767] using wordTrace_append hprefix tailTrace_1582767
  have hstable : (prefixWord ++ tailWord_1582767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582767).length < 2 ^ (prefixWord ++ tailWord_1582767).sum := by decide
  have hdescent : baseEnd_1582767 < baseStart_1582767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582770 : List Nat := [3, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_1582770 : Nat := 118140960795 + 1582770 * 2 ^ 59
def prefixEnd_1582770 : Nat := 4983230072969 + 3 ^ 40 * 1582770 * 2
def baseEnd_1582770 : Nat := 361209678007501172798213

theorem tailTrace_1582770 : CollatzResearch.WordTrace tailWord_1582770 prefixEnd_1582770 361209678007501172798213 := by
  unfold tailWord_1582770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14432091118975520110046441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38485576317268053626790509 14432091118975520110046441)
  ·
    refine ⟨10824068339231640082534831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14432091118975520110046441 10824068339231640082534831)
    ·
      refine ⟨16236102508847460123802247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10824068339231640082534831 16236102508847460123802247)
      ·
        refine ⟨24354153763271190185703371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16236102508847460123802247 24354153763271190185703371)
        ·
          refine ⟨36531230644906785278555057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24354153763271190185703371 36531230644906785278555057)
          ·
            refine ⟨27398422983680088958916293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36531230644906785278555057 27398422983680088958916293)
            ·
              refine ⟨5137204309440016679796805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27398422983680088958916293 5137204309440016679796805)
              ·
                refine ⟨963225808020003127461901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5137204309440016679796805 963225808020003127461901)
                ·
                  refine ⟨361209678007501172798213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963225808020003127461901 361209678007501172798213)
                  ·
                    rfl

theorem cell21_1582770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_1582770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582770 prefixEnd_1582770 := by exact prefixLift 1582770
  have htrace : WordTrace (prefixWord ++ tailWord_1582770) baseStart_1582770 baseEnd_1582770 := by
    simpa [prefixWord, tailWord_1582770, baseEnd_1582770] using wordTrace_append hprefix tailTrace_1582770
  have hstable : (prefixWord ++ tailWord_1582770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582770).length < 2 ^ (prefixWord ++ tailWord_1582770).sum := by decide
  have hdescent : baseEnd_1582770 < baseStart_1582770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582790 : List Nat := [6, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1582790 : Nat := 118140960795 + 1582790 * 2 ^ 59
def prefixEnd_1582790 : Nat := 4983230072969 + 3 ^ 40 * 1582790 * 2
def baseEnd_1582790 : Nat := 120404747426661860821613

theorem tailTrace_1582790 : CollatzResearch.WordTrace tailWord_1582790 prefixEnd_1582790 120404747426661860821613 := by
  unfold tailWord_1582790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1804034185494675745497307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38486062623886415903942549 1804034185494675745497307)
  ·
    refine ⟨2706051278242013618245961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1804034185494675745497307 2706051278242013618245961)
    ·
      refine ⟨2029538458681510213684471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2706051278242013618245961 2029538458681510213684471)
      ·
        refine ⟨3044307688022265320526707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029538458681510213684471 3044307688022265320526707)
        ·
          refine ⟨4566461532033397980790061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044307688022265320526707 4566461532033397980790061)
          ·
            refine ⟨1712423074512524242796273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4566461532033397980790061 1712423074512524242796273)
            ·
              refine ⟨1284317305884393182097205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712423074512524242796273 1284317305884393182097205)
              ·
                refine ⟨120404747426661860821613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1284317305884393182097205 120404747426661860821613)
                ·
                  rfl

theorem cell21_1582790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1582790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582790 prefixEnd_1582790 := by exact prefixLift 1582790
  have htrace : WordTrace (prefixWord ++ tailWord_1582790) baseStart_1582790 baseEnd_1582790 := by
    simpa [prefixWord, tailWord_1582790, baseEnd_1582790] using wordTrace_append hprefix tailTrace_1582790
  have hstable : (prefixWord ++ tailWord_1582790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582790).length < 2 ^ (prefixWord ++ tailWord_1582790).sum := by decide
  have hdescent : baseEnd_1582790 < baseStart_1582790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582798 : List Nat := [4, 1, 1, 1, 3, 1, 3, 7]
def baseStart_1582798 : Nat := 118140960795 + 1582798 * 2 ^ 59
def prefixEnd_1582798 : Nat := 4983230072969 + 3 ^ 40 * 1582798 * 2
def baseEnd_1582798 : Nat := 120405355996326448777163

theorem tailTrace_1582798 : CollatzResearch.WordTrace tailWord_1582798 prefixEnd_1582798 120405355996326448777163 := by
  unfold tailWord_1582798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7216173214975080152775631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38486257146533760814803365 7216173214975080152775631)
  ·
    refine ⟨10824259822462620229163447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7216173214975080152775631 10824259822462620229163447)
    ·
      refine ⟨16236389733693930343745171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10824259822462620229163447 16236389733693930343745171)
      ·
        refine ⟨24354584600540895515617757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16236389733693930343745171 24354584600540895515617757)
        ·
          refine ⟨9132969225202835818356659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24354584600540895515617757 9132969225202835818356659)
          ·
            refine ⟨13699453837804253727534989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9132969225202835818356659 13699453837804253727534989)
            ·
              refine ⟨5137295189176595147825621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13699453837804253727534989 5137295189176595147825621)
              ·
                refine ⟨120405355996326448777163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5137295189176595147825621 120405355996326448777163)
                ·
                  rfl

theorem cell21_1582798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_1582798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582798 prefixEnd_1582798 := by exact prefixLift 1582798
  have htrace : WordTrace (prefixWord ++ tailWord_1582798) baseStart_1582798 baseEnd_1582798 := by
    simpa [prefixWord, tailWord_1582798, baseEnd_1582798] using wordTrace_append hprefix tailTrace_1582798
  have hstable : (prefixWord ++ tailWord_1582798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582798).length < 2 ^ (prefixWord ++ tailWord_1582798).sum := by decide
  have hdescent : baseEnd_1582798 < baseStart_1582798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582804 : List Nat := [2, 4, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1582804 : Nat := 118140960795 + 1582804 * 2 ^ 59
def prefixEnd_1582804 : Nat := 4983230072969 + 3 ^ 40 * 1582804 * 2
def baseEnd_1582804 : Nat := 361217437270724669231477

theorem tailTrace_1582804 : CollatzResearch.WordTrace tailWord_1582804 prefixEnd_1582804 361217437270724669231477 := by
  unfold tailWord_1582804
  simp only [CollatzResearch.WordTrace]
  refine ⟨28864802278889452123461733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38486403038519269497948977 28864802278889452123461733)
  ·
    refine ⟨5412150427291772273149075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28864802278889452123461733 5412150427291772273149075)
    ·
      refine ⟨8118225640937658409723613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5412150427291772273149075 8118225640937658409723613)
      ·
        refine ⟨3044334615351621903646355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8118225640937658409723613 3044334615351621903646355)
        ·
          refine ⟨4566501923027432855469533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044334615351621903646355 4566501923027432855469533)
          ·
            refine ⟨1712438221135287320801075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4566501923027432855469533 1712438221135287320801075)
            ·
              refine ⟨2568657331702930981201613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712438221135287320801075 2568657331702930981201613)
              ·
                refine ⟨963246499388599117950605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2568657331702930981201613 963246499388599117950605)
                ·
                  refine ⟨361217437270724669231477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963246499388599117950605 361217437270724669231477)
                  ·
                    rfl

theorem cell21_1582804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1582804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582804 prefixEnd_1582804 := by exact prefixLift 1582804
  have htrace : WordTrace (prefixWord ++ tailWord_1582804) baseStart_1582804 baseEnd_1582804 := by
    simpa [prefixWord, tailWord_1582804, baseEnd_1582804] using wordTrace_append hprefix tailTrace_1582804
  have hstable : (prefixWord ++ tailWord_1582804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582804).length < 2 ^ (prefixWord ++ tailWord_1582804).sum := by decide
  have hdescent : baseEnd_1582804 < baseStart_1582804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582922 : List Nat := [3, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_1582922 : Nat := 118140960795 + 1582922 * 2 ^ 59
def prefixEnd_1582922 : Nat := 4983230072969 + 3 ^ 40 * 1582922 * 2
def baseEnd_1582922 : Nat := 361244366478382686264569

theorem tailTrace_1582922 : CollatzResearch.WordTrace tailWord_1582922 prefixEnd_1582922 361244366478382686264569 := by
  unfold tailWord_1582922
  simp only [CollatzResearch.WordTrace]
  refine ⟨14433477092837852599929755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38489272247567606933146013 14433477092837852599929755)
  ·
    refine ⟨21650215639256778899894633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14433477092837852599929755 21650215639256778899894633)
    ·
      refine ⟨16237661729442584174920975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21650215639256778899894633 16237661729442584174920975)
      ·
        refine ⟨24356492594163876262381463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16237661729442584174920975 24356492594163876262381463)
        ·
          refine ⟨36534738891245814393572195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24356492594163876262381463 36534738891245814393572195)
          ·
            refine ⟨54802108336868721590358293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36534738891245814393572195 54802108336868721590358293)
            ·
              refine ⟨2568848828290721324548045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54802108336868721590358293 2568848828290721324548045)
              ·
                refine ⟨963318310609020496705517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2568848828290721324548045 963318310609020496705517)
                ·
                  refine ⟨361244366478382686264569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963318310609020496705517 361244366478382686264569)
                  ·
                    rfl

theorem cell21_1582922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_1582922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582922 prefixEnd_1582922 := by exact prefixLift 1582922
  have htrace : WordTrace (prefixWord ++ tailWord_1582922) baseStart_1582922 baseEnd_1582922 := by
    simpa [prefixWord, tailWord_1582922, baseEnd_1582922] using wordTrace_append hprefix tailTrace_1582922
  have hstable : (prefixWord ++ tailWord_1582922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582922).length < 2 ^ (prefixWord ++ tailWord_1582922).sum := by decide
  have hdescent : baseEnd_1582922 < baseStart_1582922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583012 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_1583012 : Nat := 118140960795 + 1583012 * 2 ^ 59
def prefixEnd_1583012 : Nat := 4983230072969 + 3 ^ 40 * 1583012 * 2
def baseEnd_1583012 : Nat := 361264905704562529764385

theorem tailTrace_1583012 : CollatzResearch.WordTrace tailWord_1583012 prefixEnd_1583012 361264905704562529764385 := by
  unfold tailWord_1583012
  simp only [CollatzResearch.WordTrace]
  refine ⟨28868595470512677885247645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38491460627350237180330193 28868595470512677885247645)
  ·
    refine ⟨10825723301442254206967867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28868595470512677885247645 10825723301442254206967867)
    ·
      refine ⟨16238584952163381310451801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10825723301442254206967867 16238584952163381310451801)
      ·
        refine ⟨12178938714122535982838851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16238584952163381310451801 12178938714122535982838851)
        ·
          refine ⟨18268408071183803974258277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12178938714122535982838851 18268408071183803974258277)
          ·
            refine ⟨3425326513346963245173427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18268408071183803974258277 3425326513346963245173427)
            ·
              refine ⟨5137989770020444867760141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425326513346963245173427 5137989770020444867760141)
              ·
                refine ⟨1926746163757666825410053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5137989770020444867760141 1926746163757666825410053)
                ·
                  refine ⟨361264905704562529764385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1926746163757666825410053 361264905704562529764385)
                  ·
                    rfl

theorem cell21_1583012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_1583012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583012 prefixEnd_1583012 := by exact prefixLift 1583012
  have htrace : WordTrace (prefixWord ++ tailWord_1583012) baseStart_1583012 baseEnd_1583012 := by
    simpa [prefixWord, tailWord_1583012, baseEnd_1583012] using wordTrace_append hprefix tailTrace_1583012
  have hstable : (prefixWord ++ tailWord_1583012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583012).length < 2 ^ (prefixWord ++ tailWord_1583012).sum := by decide
  have hdescent : baseEnd_1583012 < baseStart_1583012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583133 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1583133 : Nat := 118140960795 + 1583133 * 2 ^ 59
def prefixEnd_1583133 : Nat := 4983230072969 + 3 ^ 40 * 1583133 * 2
def baseEnd_1583133 : Nat := 361292519553093208247471

theorem tailTrace_1583133 : CollatzResearch.WordTrace tailWord_1583133 prefixEnd_1583133 361292519553093208247471 := by
  unfold tailWord_1583133
  simp only [CollatzResearch.WordTrace]
  refine ⟨57741604173586993435650053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38494402782391328957100035 57741604173586993435650053)
  ·
    refine ⟨10826550782547561269184385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57741604173586993435650053 10826550782547561269184385)
    ·
      refine ⟨8119913086910670951888289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10826550782547561269184385 8119913086910670951888289)
      ·
        refine ⟨6089934815183003213916217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8119913086910670951888289 6089934815183003213916217)
        ·
          refine ⟨4567451111387252410437163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6089934815183003213916217 4567451111387252410437163)
          ·
            refine ⟨6851176667080878615655745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567451111387252410437163 6851176667080878615655745)
            ·
              refine ⟨5138382500310658961741809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6851176667080878615655745 5138382500310658961741809)
              ·
                refine ⟨3853786875232994221306357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5138382500310658961741809 3853786875232994221306357)
                ·
                  refine ⟨361292519553093208247471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3853786875232994221306357 361292519553093208247471)
                  ·
                    rfl

theorem cell21_1583133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1583133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583133 prefixEnd_1583133 := by exact prefixLift 1583133
  have htrace : WordTrace (prefixWord ++ tailWord_1583133) baseStart_1583133 baseEnd_1583133 := by
    simpa [prefixWord, tailWord_1583133, baseEnd_1583133] using wordTrace_append hprefix tailTrace_1583133
  have hstable : (prefixWord ++ tailWord_1583133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583133).length < 2 ^ (prefixWord ++ tailWord_1583133).sum := by decide
  have hdescent : baseEnd_1583133 < baseStart_1583133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583209 : List Nat := [1, 2, 1, 1, 1, 5, 2, 5, 3]
def baseStart_1583209 : Nat := 118140960795 + 1583209 * 2 ^ 59
def prefixEnd_1583209 : Nat := 4983230072969 + 3 ^ 40 * 1583209 * 2
def baseEnd_1583209 : Nat := 361309863788533964980649

theorem tailTrace_1583209 : CollatzResearch.WordTrace tailWord_1583209 prefixEnd_1583209 361309863788533964980649 := by
  unfold tailWord_1583209
  simp only [CollatzResearch.WordTrace]
  refine ⟨57744376121311658415416681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38496250747541105610277787 57744376121311658415416681)
  ·
    refine ⟨43308282090983743811562511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57744376121311658415416681 43308282090983743811562511)
    ·
      refine ⟨64962423136475615717343767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43308282090983743811562511 64962423136475615717343767)
      ·
        refine ⟨97443634704713423576015651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64962423136475615717343767 97443634704713423576015651)
        ·
          refine ⟨146165452057070135364023477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97443634704713423576015651 146165452057070135364023477)
          ·
            refine ⟨13703011130350325190377201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146165452057070135364023477 13703011130350325190377201)
            ·
              refine ⟨10277258347762743892782901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13703011130350325190377201 10277258347762743892782901)
              ·
                refine ⟨963492970102757239948397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10277258347762743892782901 963492970102757239948397)
                ·
                  refine ⟨361309863788533964980649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963492970102757239948397 361309863788533964980649)
                  ·
                    rfl

theorem cell21_1583209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_1583209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583209 prefixEnd_1583209 := by exact prefixLift 1583209
  have htrace : WordTrace (prefixWord ++ tailWord_1583209) baseStart_1583209 baseEnd_1583209 := by
    simpa [prefixWord, tailWord_1583209, baseEnd_1583209] using wordTrace_append hprefix tailTrace_1583209
  have hstable : (prefixWord ++ tailWord_1583209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583209).length < 2 ^ (prefixWord ++ tailWord_1583209).sum := by decide
  have hdescent : baseEnd_1583209 < baseStart_1583209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583223 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 4]
def baseStart_1583223 : Nat := 118140960795 + 1583223 * 2 ^ 59
def prefixEnd_1583223 : Nat := 4983230072969 + 3 ^ 40 * 1583223 * 2
def baseEnd_1583223 : Nat := 361313058779273051747287

theorem tailTrace_1583223 : CollatzResearch.WordTrace tailWord_1583223 prefixEnd_1583223 361313058779273051747287 := by
  unfold tailWord_1583223
  simp only [CollatzResearch.WordTrace]
  refine ⟨57744886743260938806426323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38496591162173959204284215 57744886743260938806426323)
  ·
    refine ⟨86617330114891408209639485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57744886743260938806426323 86617330114891408209639485)
    ·
      refine ⟨32481498793084278078614807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86617330114891408209639485 32481498793084278078614807)
      ·
        refine ⟨48722248189626417117922211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32481498793084278078614807 48722248189626417117922211)
        ·
          refine ⟨73083372284439625676883317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48722248189626417117922211 73083372284439625676883317)
          ·
            refine ⟨6851566151666214907207811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73083372284439625676883317 6851566151666214907207811)
            ·
              refine ⟨10277349227499322360811717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6851566151666214907207811 10277349227499322360811717)
              ·
                refine ⟨1927002980156122942652197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10277349227499322360811717 1927002980156122942652197)
                ·
                  refine ⟨361313058779273051747287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927002980156122942652197 361313058779273051747287)
                  ·
                    rfl

theorem cell21_1583223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 4].length) (baseStart_1583223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583223 prefixEnd_1583223 := by exact prefixLift 1583223
  have htrace : WordTrace (prefixWord ++ tailWord_1583223) baseStart_1583223 baseEnd_1583223 := by
    simpa [prefixWord, tailWord_1583223, baseEnd_1583223] using wordTrace_append hprefix tailTrace_1583223
  have hstable : (prefixWord ++ tailWord_1583223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583223).length < 2 ^ (prefixWord ++ tailWord_1583223).sum := by decide
  have hdescent : baseEnd_1583223 < baseStart_1583223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583240 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_1583240 : Nat := 118140960795 + 1583240 * 2 ^ 59
def prefixEnd_1583240 : Nat := 4983230072969 + 3 ^ 40 * 1583240 * 2
def baseEnd_1583240 : Nat := 361316938410884799963919

theorem tailTrace_1583240 : CollatzResearch.WordTrace tailWord_1583240 prefixEnd_1583240 361316938410884799963919 := by
  unfold tailWord_1583240
  simp only [CollatzResearch.WordTrace]
  refine ⟨28872753392099675354897587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38497004522799567139863449 28872753392099675354897587)
  ·
    refine ⟨43309130088149513032346381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28872753392099675354897587 43309130088149513032346381)
    ·
      refine ⟨16240923783056067387129893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43309130088149513032346381 16240923783056067387129893)
      ·
        refine ⟨3045173209323012635086855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16240923783056067387129893 3045173209323012635086855)
        ·
          refine ⟨4567759813984518952630283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045173209323012635086855 4567759813984518952630283)
          ·
            refine ⟨6851639720976778428945425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567759813984518952630283 6851639720976778428945425)
            ·
              refine ⟨5138729790732583821709069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6851639720976778428945425 5138729790732583821709069)
              ·
                refine ⟨1927023671524718933140901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5138729790732583821709069 1927023671524718933140901)
                ·
                  refine ⟨361316938410884799963919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927023671524718933140901 361316938410884799963919)
                  ·
                    rfl

theorem cell21_1583240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_1583240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583240 prefixEnd_1583240 := by exact prefixLift 1583240
  have htrace : WordTrace (prefixWord ++ tailWord_1583240) baseStart_1583240 baseEnd_1583240 := by
    simpa [prefixWord, tailWord_1583240, baseEnd_1583240] using wordTrace_append hprefix tailTrace_1583240
  have hstable : (prefixWord ++ tailWord_1583240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583240).length < 2 ^ (prefixWord ++ tailWord_1583240).sum := by decide
  have hdescent : baseEnd_1583240 < baseStart_1583240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583274 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_1583274 : Nat := 118140960795 + 1583274 * 2 ^ 59
def prefixEnd_1583274 : Nat := 4983230072969 + 3 ^ 40 * 1583274 * 2
def baseEnd_1583274 : Nat := 361324697674108296397183

theorem tailTrace_1583274 : CollatzResearch.WordTrace tailWord_1583274 prefixEnd_1583274 361324697674108296397183 := by
  unfold tailWord_1583274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14436686716519043629133219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38497831244050783011021917 14436686716519043629133219)
  ·
    refine ⟨21655030074778565443699829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14436686716519043629133219 21655030074778565443699829)
    ·
      refine ⟨2030159069510490510346859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21655030074778565443699829 2030159069510490510346859)
      ·
        refine ⟨3045238604265735765520289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030159069510490510346859 3045238604265735765520289)
        ·
          refine ⟨2283928953199301824140217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3045238604265735765520289 2283928953199301824140217)
          ·
            refine ⟨1712946714899476368105163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283928953199301824140217 1712946714899476368105163)
            ·
              refine ⟨2569420072349214552157745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712946714899476368105163 2569420072349214552157745)
              ·
                refine ⟨1927065054261910914118309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2569420072349214552157745 1927065054261910914118309)
                ·
                  refine ⟨361324697674108296397183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927065054261910914118309 361324697674108296397183)
                  ·
                    rfl

theorem cell21_1583274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_1583274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583274 prefixEnd_1583274 := by exact prefixLift 1583274
  have htrace : WordTrace (prefixWord ++ tailWord_1583274) baseStart_1583274 baseEnd_1583274 := by
    simpa [prefixWord, tailWord_1583274, baseEnd_1583274] using wordTrace_append hprefix tailTrace_1583274
  have hstable : (prefixWord ++ tailWord_1583274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583274).length < 2 ^ (prefixWord ++ tailWord_1583274).sum := by decide
  have hdescent : baseEnd_1583274 < baseStart_1583274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583389 : List Nat := [1, 4, 2, 3, 11]
def baseStart_1583389 : Nat := 118140960795 + 1583389 * 2 ^ 59
def prefixEnd_1583389 : Nat := 4983230072969 + 3 ^ 40 * 1583389 * 2
def baseEnd_1583389 : Nat := 4461122743714736444201

theorem tailTrace_1583389 : CollatzResearch.WordTrace tailWord_1583389 prefixEnd_1583389 4461122743714736444201 := by
  unfold tailWord_1583389
  simp only [CollatzResearch.WordTrace]
  refine ⟨57750941260659549156969221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38500627507106366104646147 57750941260659549156969221)
  ·
    refine ⟨10828301486373665466931729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57750941260659549156969221 10828301486373665466931729)
    ·
      refine ⟨8121226114780249100198797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10828301486373665466931729 8121226114780249100198797)
      ·
        refine ⟨3045459793042593412574549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8121226114780249100198797 3045459793042593412574549)
        ·
          refine ⟨4461122743714736444201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3045459793042593412574549 4461122743714736444201)
          ·
            rfl

theorem cell21_1583389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 11].length) (baseStart_1583389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583389 prefixEnd_1583389 := by exact prefixLift 1583389
  have htrace : WordTrace (prefixWord ++ tailWord_1583389) baseStart_1583389 baseEnd_1583389 := by
    simpa [prefixWord, tailWord_1583389, baseEnd_1583389] using wordTrace_append hprefix tailTrace_1583389
  have hstable : (prefixWord ++ tailWord_1583389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583389).length < 2 ^ (prefixWord ++ tailWord_1583389).sum := by decide
  have hdescent : baseEnd_1583389 < baseStart_1583389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583392 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_1583392 : Nat := 118140960795 + 1583392 * 2 ^ 59
def prefixEnd_1583392 : Nat := 4983230072969 + 3 ^ 40 * 1583392 * 2
def baseEnd_1583392 : Nat := 361351626881766313430275

theorem tailTrace_1583392 : CollatzResearch.WordTrace tailWord_1583392 prefixEnd_1583392 361351626881766313430275 := by
  unfold tailWord_1583392
  simp only [CollatzResearch.WordTrace]
  refine ⟨28875525339824340334664215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38500700453099120446218953 28875525339824340334664215)
  ·
    refine ⟨43313288009736510501996323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28875525339824340334664215 43313288009736510501996323)
    ·
      refine ⟨64969932014604765752994485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43313288009736510501996323 64969932014604765752994485)
      ·
        refine ⟨6090931126369196789343233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64969932014604765752994485 6090931126369196789343233)
        ·
          refine ⟨4568198344776897592007425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6090931126369196789343233 4568198344776897592007425)
          ·
            refine ⟨3426148758582673194005569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4568198344776897592007425 3426148758582673194005569)
            ·
              refine ⟨2569611568937004895504177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3426148758582673194005569 2569611568937004895504177)
              ·
                refine ⟨1927208676702753671628133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2569611568937004895504177 1927208676702753671628133)
                ·
                  refine ⟨361351626881766313430275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927208676702753671628133 361351626881766313430275)
                  ·
                    rfl

theorem cell21_1583392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_1583392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583392 prefixEnd_1583392 := by exact prefixLift 1583392
  have htrace : WordTrace (prefixWord ++ tailWord_1583392) baseStart_1583392 baseEnd_1583392 := by
    simpa [prefixWord, tailWord_1583392, baseEnd_1583392] using wordTrace_append hprefix tailTrace_1583392
  have hstable : (prefixWord ++ tailWord_1583392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583392).length < 2 ^ (prefixWord ++ tailWord_1583392).sum := by decide
  have hdescent : baseEnd_1583392 < baseStart_1583392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583420 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_1583420 : Nat := 118140960795 + 1583420 * 2 ^ 59
def prefixEnd_1583420 : Nat := 4983230072969 + 3 ^ 40 * 1583420 * 2
def baseEnd_1583420 : Nat := 361358016863244486963551

theorem tailTrace_1583420 : CollatzResearch.WordTrace tailWord_1583420 prefixEnd_1583420 361358016863244486963551 := by
  unfold tailWord_1583420
  simp only [CollatzResearch.WordTrace]
  refine ⟨28876035961773620725673857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38501381282364827634231809 28876035961773620725673857)
  ·
    refine ⟨21657026971330215544255393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28876035961773620725673857 21657026971330215544255393)
    ·
      refine ⟨16242770228497661658191545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21657026971330215544255393 16242770228497661658191545)
      ·
        refine ⟨12182077671373246243643659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16242770228497661658191545 12182077671373246243643659)
        ·
          refine ⟨18273116507059869365465489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12182077671373246243643659 18273116507059869365465489)
          ·
            refine ⟨13704837380294902024099117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18273116507059869365465489 13704837380294902024099117)
            ·
              refine ⟨5139314017610588259037169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13704837380294902024099117 5139314017610588259037169)
              ·
                refine ⟨3854485513207941194277877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5139314017610588259037169 3854485513207941194277877)
                ·
                  refine ⟨361358016863244486963551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3854485513207941194277877 361358016863244486963551)
                  ·
                    rfl

theorem cell21_1583420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_1583420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583420 prefixEnd_1583420 := by exact prefixLift 1583420
  have htrace : WordTrace (prefixWord ++ tailWord_1583420) baseStart_1583420 baseEnd_1583420 := by
    simpa [prefixWord, tailWord_1583420, baseEnd_1583420] using wordTrace_append hprefix tailTrace_1583420
  have hstable : (prefixWord ++ tailWord_1583420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583420).length < 2 ^ (prefixWord ++ tailWord_1583420).sum := by decide
  have hdescent : baseEnd_1583420 < baseStart_1583420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583479 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 7]
def baseStart_1583479 : Nat := 118140960795 + 1583479 * 2 ^ 59
def prefixEnd_1583479 : Nat := 4983230072969 + 3 ^ 40 * 1583479 * 2
def baseEnd_1583479 : Nat := 361371481467073495480097

theorem tailTrace_1583479 : CollatzResearch.WordTrace tailWord_1583479 prefixEnd_1583479 361371481467073495480097 := by
  unfold tailWord_1583479
  simp only [CollatzResearch.WordTrace]
  refine ⟨57754223830333494527745491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38502815886888996351830327 57754223830333494527745491)
  ·
    refine ⟨86631335745500241791618237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57754223830333494527745491 86631335745500241791618237)
    ·
      refine ⟨32486750904562590671856839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86631335745500241791618237 32486750904562590671856839)
      ·
        refine ⟨48730126356843886007785259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32486750904562590671856839 48730126356843886007785259)
        ·
          refine ⟨73095189535265829011677889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48730126356843886007785259 73095189535265829011677889)
          ·
            refine ⟨54821392151449371758758417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73095189535265829011677889 54821392151449371758758417)
            ·
              refine ⟨41116044113587028819068813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54821392151449371758758417 41116044113587028819068813)
              ·
                refine ⟨15418516542595135807150805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41116044113587028819068813 15418516542595135807150805)
                ·
                  refine ⟨361371481467073495480097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15418516542595135807150805 361371481467073495480097)
                  ·
                    rfl

theorem cell21_1583479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_1583479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583479 prefixEnd_1583479 := by exact prefixLift 1583479
  have htrace : WordTrace (prefixWord ++ tailWord_1583479) baseStart_1583479 baseEnd_1583479 := by
    simpa [prefixWord, tailWord_1583479, baseEnd_1583479] using wordTrace_append hprefix tailTrace_1583479
  have hstable : (prefixWord ++ tailWord_1583479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583479).length < 2 ^ (prefixWord ++ tailWord_1583479).sum := by decide
  have hdescent : baseEnd_1583479 < baseStart_1583479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583564 : List Nat := [2, 2, 1, 4, 4, 1, 2, 2, 3]
def baseStart_1583564 : Nat := 118140960795 + 1583564 * 2 ^ 59
def prefixEnd_1583564 : Nat := 4983230072969 + 3 ^ 40 * 1583564 * 2
def baseEnd_1583564 : Nat := 361390879625132236563257

theorem tailTrace_1583564 : CollatzResearch.WordTrace tailWord_1583564 prefixEnd_1583564 361390879625132236563257 := by
  unfold tailWord_1583564
  simp only [CollatzResearch.WordTrace]
  refine ⟨28878662017512777022294873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38504882690017036029726497 28878662017512777022294873)
  ·
    refine ⟨21658996513134582766721155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28878662017512777022294873 21658996513134582766721155)
    ·
      refine ⟨32488494769701874150081733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21658996513134582766721155 32488494769701874150081733)
      ·
        refine ⟨6091592769319101403140325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32488494769701874150081733 6091592769319101403140325)
        ·
          refine ⟨1142173644247331513088811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6091592769319101403140325 1142173644247331513088811)
          ·
            refine ⟨1713260466370997269633217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142173644247331513088811 1713260466370997269633217)
            ·
              refine ⟨1284945349778247952224913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1713260466370997269633217 1284945349778247952224913)
              ·
                refine ⟨963709012333685964168685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284945349778247952224913 963709012333685964168685)
                ·
                  refine ⟨361390879625132236563257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963709012333685964168685 361390879625132236563257)
                  ·
                    rfl

theorem cell21_1583564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_1583564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583564 prefixEnd_1583564 := by exact prefixLift 1583564
  have htrace : WordTrace (prefixWord ++ tailWord_1583564) baseStart_1583564 baseEnd_1583564 := by
    simpa [prefixWord, tailWord_1583564, baseEnd_1583564] using wordTrace_append hprefix tailTrace_1583564
  have hstable : (prefixWord ++ tailWord_1583564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583564).length < 2 ^ (prefixWord ++ tailWord_1583564).sum := by decide
  have hdescent : baseEnd_1583564 < baseStart_1583564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583589 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 5]
def baseStart_1583589 : Nat := 118140960795 + 1583589 * 2 ^ 59
def prefixEnd_1583589 : Nat := 4983230072969 + 3 ^ 40 * 1583589 * 2
def baseEnd_1583589 : Nat := 361396584965737748646539

theorem tailTrace_1583589 : CollatzResearch.WordTrace tailWord_1583589 prefixEnd_1583589 361396584965737748646539 := by
  unfold tailWord_1583589
  simp only [CollatzResearch.WordTrace]
  refine ⟨57758235859934983314249821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38505490573289988876166547 57758235859934983314249821)
  ·
    refine ⟨21659338447475618742843683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57758235859934983314249821 21659338447475618742843683)
    ·
      refine ⟨32489007671213428114265525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21659338447475618742843683 32489007671213428114265525)
      ·
        refine ⟨3045844469176258885712393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32489007671213428114265525 3045844469176258885712393)
        ·
          refine ⟨2284383351882194164284295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3045844469176258885712393 2284383351882194164284295)
          ·
            refine ⟨3426575027823291246426443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284383351882194164284295 3426575027823291246426443)
            ·
              refine ⟨5139862541734936869639665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426575027823291246426443 5139862541734936869639665)
              ·
                refine ⟨3854896906301202652229749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5139862541734936869639665 3854896906301202652229749)
                ·
                  refine ⟨361396584965737748646539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3854896906301202652229749 361396584965737748646539)
                  ·
                    rfl

theorem cell21_1583589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_1583589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583589 prefixEnd_1583589 := by exact prefixLift 1583589
  have htrace : WordTrace (prefixWord ++ tailWord_1583589) baseStart_1583589 baseEnd_1583589 := by
    simpa [prefixWord, tailWord_1583589, baseEnd_1583589] using wordTrace_append hprefix tailTrace_1583589
  have hstable : (prefixWord ++ tailWord_1583589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583589).length < 2 ^ (prefixWord ++ tailWord_1583589).sum := by decide
  have hdescent : baseEnd_1583589 < baseStart_1583589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583606 : List Nat := [5, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_1583606 : Nat := 118140960795 + 1583606 * 2 ^ 59
def prefixEnd_1583606 : Nat := 4983230072969 + 3 ^ 40 * 1583606 * 2
def baseEnd_1583606 : Nat := 361400464597349496863171

theorem tailTrace_1583606 : CollatzResearch.WordTrace tailWord_1583606 prefixEnd_1583606 361400464597349496863171 := by
  unfold tailWord_1583606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609928493804587201101167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38505903933915596811745781 3609928493804587201101167)
  ·
    refine ⟨5414892740706880801651751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3609928493804587201101167 5414892740706880801651751)
    ·
      refine ⟨8122339111060321202477627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5414892740706880801651751 8122339111060321202477627)
      ·
        refine ⟨12183508666590481803716441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8122339111060321202477627 12183508666590481803716441)
        ·
          refine ⟨9137631499942861352787331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12183508666590481803716441 9137631499942861352787331)
          ·
            refine ⟨13706447249914292029180997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9137631499942861352787331 13706447249914292029180997)
            ·
              refine ⟨2569958859358929755471437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13706447249914292029180997 2569958859358929755471437)
              ·
                refine ⟨963734572259598658301789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2569958859358929755471437 963734572259598658301789)
                ·
                  refine ⟨361400464597349496863171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963734572259598658301789 361400464597349496863171)
                  ·
                    rfl

theorem cell21_1583606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_1583606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583606 prefixEnd_1583606 := by exact prefixLift 1583606
  have htrace : WordTrace (prefixWord ++ tailWord_1583606) baseStart_1583606 baseEnd_1583606 := by
    simpa [prefixWord, tailWord_1583606, baseEnd_1583606] using wordTrace_append hprefix tailTrace_1583606
  have hstable : (prefixWord ++ tailWord_1583606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583606).length < 2 ^ (prefixWord ++ tailWord_1583606).sum := by decide
  have hdescent : baseEnd_1583606 < baseStart_1583606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583617 : List Nat := [1, 2, 4, 1, 3, 2, 8]
def baseStart_1583617 : Nat := 118140960795 + 1583617 * 2 ^ 59
def prefixEnd_1583617 : Nat := 4983230072969 + 3 ^ 40 * 1583617 * 2
def baseEnd_1583617 : Nat := 40155886105246213575535

theorem tailTrace_1583617 : CollatzResearch.WordTrace tailWord_1583617 prefixEnd_1583617 40155886105246213575535 := by
  unfold tailWord_1583617
  simp only [CollatzResearch.WordTrace]
  refine ⟨57759257103833544096269105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38506171402555696064179403 57759257103833544096269105)
  ·
    refine ⟨43319442827875158072201829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57759257103833544096269105 43319442827875158072201829)
    ·
      refine ⟨8122395530226592138537843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43319442827875158072201829 8122395530226592138537843)
      ·
        refine ⟨12183593295339888207806765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8122395530226592138537843 12183593295339888207806765)
        ·
          refine ⟨4568847485752458077927537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12183593295339888207806765 4568847485752458077927537)
          ·
            refine ⟨3426635614314343558445653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4568847485752458077927537 3426635614314343558445653)
            ·
              refine ⟨40155886105246213575535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3426635614314343558445653 40155886105246213575535)
              ·
                rfl

theorem cell21_1583617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 8].length) (baseStart_1583617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583617 prefixEnd_1583617 := by exact prefixLift 1583617
  have htrace : WordTrace (prefixWord ++ tailWord_1583617) baseStart_1583617 baseEnd_1583617 := by
    simpa [prefixWord, tailWord_1583617, baseEnd_1583617] using wordTrace_append hprefix tailTrace_1583617
  have hstable : (prefixWord ++ tailWord_1583617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583617).length < 2 ^ (prefixWord ++ tailWord_1583617).sum := by decide
  have hdescent : baseEnd_1583617 < baseStart_1583617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583620 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_1583620 : Nat := 118140960795 + 1583620 * 2 ^ 59
def prefixEnd_1583620 : Nat := 4983230072969 + 3 ^ 40 * 1583620 * 2
def baseEnd_1583620 : Nat := 361403659588088583629809

theorem tailTrace_1583620 : CollatzResearch.WordTrace tailWord_1583620 prefixEnd_1583620 361403659588088583629809 := by
  unfold tailWord_1583620
  simp only [CollatzResearch.WordTrace]
  refine ⟨28879683261411337804314157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38506244348548450405752209 28879683261411337804314157)
  ·
    refine ⟨10829881223029251676617809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28879683261411337804314157 10829881223029251676617809)
    ·
      refine ⟨8122410917271938757463357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10829881223029251676617809 8122410917271938757463357)
      ·
        refine ⟨3045904093976977034048759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8122410917271938757463357 3045904093976977034048759)
        ·
          refine ⟨4568856140965465551073139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045904093976977034048759 4568856140965465551073139)
          ·
            refine ⟨6853284211448198326609709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568856140965465551073139 6853284211448198326609709)
            ·
              refine ⟨2569981579293074372478641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6853284211448198326609709 2569981579293074372478641)
              ·
                refine ⟨1927486184469805779358981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2569981579293074372478641 1927486184469805779358981)
                ·
                  refine ⟨361403659588088583629809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927486184469805779358981 361403659588088583629809)
                  ·
                    rfl

theorem cell21_1583620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_1583620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583620 prefixEnd_1583620 := by exact prefixLift 1583620
  have htrace : WordTrace (prefixWord ++ tailWord_1583620) baseStart_1583620 baseEnd_1583620 := by
    simpa [prefixWord, tailWord_1583620, baseEnd_1583620] using wordTrace_append hprefix tailTrace_1583620
  have hstable : (prefixWord ++ tailWord_1583620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583620).length < 2 ^ (prefixWord ++ tailWord_1583620).sum := by decide
  have hdescent : baseEnd_1583620 < baseStart_1583620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583631 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 5]
def baseStart_1583631 : Nat := 118140960795 + 1583631 * 2 ^ 59
def prefixEnd_1583631 : Nat := 4983230072969 + 3 ^ 40 * 1583631 * 2
def baseEnd_1583631 : Nat := 361406169937955008946453

theorem tailTrace_1583631 : CollatzResearch.WordTrace tailWord_1583631 prefixEnd_1583631 361406169937955008946453 := by
  unfold tailWord_1583631
  simp only [CollatzResearch.WordTrace]
  refine ⟨57759767725782824487278747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38506511817188549658185831 57759767725782824487278747)
  ·
    refine ⟨86639651588674236730918121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57759767725782824487278747 86639651588674236730918121)
    ·
      refine ⟨64979738691505677548188591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86639651588674236730918121 64979738691505677548188591)
      ·
        refine ⟨97469608037258516322282887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64979738691505677548188591 97469608037258516322282887)
        ·
          refine ⟨146204412055887774483424331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97469608037258516322282887 146204412055887774483424331)
          ·
            refine ⟨219306618083831661725136497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146204412055887774483424331 219306618083831661725136497)
            ·
              refine ⟨164479963562873746293852373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219306618083831661725136497 164479963562873746293852373)
              ·
                refine ⟨3854999146004853428762165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 164479963562873746293852373 3854999146004853428762165)
                ·
                  refine ⟨361406169937955008946453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3854999146004853428762165 361406169937955008946453)
                  ·
                    rfl

theorem cell21_1583631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_1583631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583631 prefixEnd_1583631 := by exact prefixLift 1583631
  have htrace : WordTrace (prefixWord ++ tailWord_1583631) baseStart_1583631 baseEnd_1583631 := by
    simpa [prefixWord, tailWord_1583631, baseEnd_1583631] using wordTrace_append hprefix tailTrace_1583631
  have hstable : (prefixWord ++ tailWord_1583631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583631).length < 2 ^ (prefixWord ++ tailWord_1583631).sum := by decide
  have hdescent : baseEnd_1583631 < baseStart_1583631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583665 : List Nat := [1, 2, 2, 3, 1, 1, 5, 3, 3]
def baseStart_1583665 : Nat := 118140960795 + 1583665 * 2 ^ 59
def prefixEnd_1583665 : Nat := 4983230072969 + 3 ^ 40 * 1583665 * 2
def baseEnd_1583665 : Nat := 361413929201178505379717

theorem tailTrace_1583665 : CollatzResearch.WordTrace tailWord_1583665 prefixEnd_1583665 361413929201178505379717 := by
  unfold tailWord_1583665
  simp only [CollatzResearch.WordTrace]
  refine ⟨57761007807659648294016449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38507338538439765529344299 57761007807659648294016449)
  ·
    refine ⟨43320755855744736220512337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57761007807659648294016449 43320755855744736220512337)
    ·
      refine ⟨32490566891808552165384253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43320755855744736220512337 32490566891808552165384253)
      ·
        refine ⟨12183962584428207062019095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32490566891808552165384253 12183962584428207062019095)
        ·
          refine ⟨18275943876642310593028643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12183962584428207062019095 18275943876642310593028643)
          ·
            refine ⟨27413915814963465889542965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18275943876642310593028643 27413915814963465889542965)
            ·
              refine ⟨2570054607652824927144653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27413915814963465889542965 2570054607652824927144653)
              ·
                refine ⟨963770477869809347679245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2570054607652824927144653 963770477869809347679245)
                ·
                  refine ⟨361413929201178505379717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963770477869809347679245 361413929201178505379717)
                  ·
                    rfl

theorem cell21_1583665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_1583665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583665 prefixEnd_1583665 := by exact prefixLift 1583665
  have htrace : WordTrace (prefixWord ++ tailWord_1583665) baseStart_1583665 baseEnd_1583665 := by
    simpa [prefixWord, tailWord_1583665, baseEnd_1583665] using wordTrace_append hprefix tailTrace_1583665
  have hstable : (prefixWord ++ tailWord_1583665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583665).length < 2 ^ (prefixWord ++ tailWord_1583665).sum := by decide
  have hdescent : baseEnd_1583665 < baseStart_1583665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583668 : List Nat := [2, 5, 1, 3, 2, 1, 7]
def baseStart_1583668 : Nat := 118140960795 + 1583668 * 2 ^ 59
def prefixEnd_1583668 : Nat := 4983230072969 + 3 ^ 40 * 1583668 * 2
def baseEnd_1583668 : Nat := 40157179315783462981079

theorem tailTrace_1583668 : CollatzResearch.WordTrace tailWord_1583668 prefixEnd_1583668 40157179315783462981079 := by
  unfold tailWord_1583668
  simp only [CollatzResearch.WordTrace]
  refine ⟨28880558613324389903187829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38507411484432519870917105 28880558613324389903187829)
  ·
    refine ⟨2707552369999161553423859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28880558613324389903187829 2707552369999161553423859)
    ·
      refine ⟨4061328554998742330135789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707552369999161553423859 4061328554998742330135789)
      ·
        refine ⟨1522998208124528373800921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4061328554998742330135789 1522998208124528373800921)
        ·
          refine ⟨1142248656093396280350691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1522998208124528373800921 1142248656093396280350691)
          ·
            refine ⟨1713372984140094420526037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142248656093396280350691 1713372984140094420526037)
            ·
              refine ⟨40157179315783462981079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1713372984140094420526037 40157179315783462981079)
              ·
                rfl

theorem cell21_1583668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 7].length) (baseStart_1583668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583668 prefixEnd_1583668 := by exact prefixLift 1583668
  have htrace : WordTrace (prefixWord ++ tailWord_1583668) baseStart_1583668 baseEnd_1583668 := by
    simpa [prefixWord, tailWord_1583668, baseEnd_1583668] using wordTrace_append hprefix tailTrace_1583668
  have hstable : (prefixWord ++ tailWord_1583668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583668).length < 2 ^ (prefixWord ++ tailWord_1583668).sum := by decide
  have hdescent : baseEnd_1583668 < baseStart_1583668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583769 : List Nat := [1, 2, 1, 2, 1, 2, 7, 5]
def baseStart_1583769 : Nat := 118140960795 + 1583769 * 2 ^ 59
def prefixEnd_1583769 : Nat := 4983230072969 + 3 ^ 40 * 1583769 * 2
def baseEnd_1583769 : Nat := 120479221139365811882057

theorem tailTrace_1583769 : CollatzResearch.WordTrace tailWord_1583769 prefixEnd_1583769 120479221139365811882057 := by
  unfold tailWord_1583769
  simp only [CollatzResearch.WordTrace]
  refine ⟨57764800999282874055802361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38509867332855249370534907 57764800999282874055802361)
  ·
    refine ⟨43323600749462155541851771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57764800999282874055802361 43323600749462155541851771)
    ·
      refine ⟨64985401124193233312777657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43323600749462155541851771 64985401124193233312777657)
      ·
        refine ⟨48739050843144924984583243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64985401124193233312777657 48739050843144924984583243)
        ·
          refine ⟨73108576264717387476874865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48739050843144924984583243 73108576264717387476874865)
          ·
            refine ⟨54831432198538040607656149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73108576264717387476874865 54831432198538040607656149)
            ·
              refine ⟨1285111692153235326741941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54831432198538040607656149 1285111692153235326741941)
              ·
                refine ⟨120479221139365811882057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1285111692153235326741941 120479221139365811882057)
                ·
                  rfl

theorem cell21_1583769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 5].length) (baseStart_1583769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583769 prefixEnd_1583769 := by exact prefixLift 1583769
  have htrace : WordTrace (prefixWord ++ tailWord_1583769) baseStart_1583769 baseEnd_1583769 := by
    simpa [prefixWord, tailWord_1583769, baseEnd_1583769] using wordTrace_append hprefix tailTrace_1583769
  have hstable : (prefixWord ++ tailWord_1583769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583769).length < 2 ^ (prefixWord ++ tailWord_1583769).sum := by decide
  have hdescent : baseEnd_1583769 < baseStart_1583769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583845 : List Nat := [1, 3, 1, 4, 1, 4, 7]
def baseStart_1583845 : Nat := 118140960795 + 1583845 * 2 ^ 59
def prefixEnd_1583845 : Nat := 4983230072969 + 3 ^ 40 * 1583845 * 2
def baseEnd_1583845 : Nat := 40161667517059799153261

theorem tailTrace_1583845 : CollatzResearch.WordTrace tailWord_1583845 prefixEnd_1583845 40161667517059799153261 := by
  unfold tailWord_1583845
  simp only [CollatzResearch.WordTrace]
  refine ⟨57767572947007539035568989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38511715298005026023712659 57767572947007539035568989)
  ·
    refine ⟨21662839855127827138338371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57767572947007539035568989 21662839855127827138338371)
    ·
      refine ⟨32494259782691740707507557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21662839855127827138338371 32494259782691740707507557)
      ·
        refine ⟨6092673709254701382657667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32494259782691740707507557 6092673709254701382657667)
        ·
          refine ⟨9139010563882052073986501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6092673709254701382657667 9139010563882052073986501)
          ·
            refine ⟨1713564480727884763872469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9139010563882052073986501 1713564480727884763872469)
            ·
              refine ⟨40161667517059799153261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1713564480727884763872469 40161667517059799153261)
              ·
                rfl

theorem cell21_1583845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 7].length) (baseStart_1583845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583845 prefixEnd_1583845 := by exact prefixLift 1583845
  have htrace : WordTrace (prefixWord ++ tailWord_1583845) baseStart_1583845 baseEnd_1583845 := by
    simpa [prefixWord, tailWord_1583845, baseEnd_1583845] using wordTrace_append hprefix tailTrace_1583845
  have hstable : (prefixWord ++ tailWord_1583845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583845).length < 2 ^ (prefixWord ++ tailWord_1583845).sum := by decide
  have hdescent : baseEnd_1583845 < baseStart_1583845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583904 : List Nat := [2, 1, 1, 5, 1, 11]
def baseStart_1583904 : Nat := 118140960795 + 1583904 * 2 ^ 59
def prefixEnd_1583904 : Nat := 4983230072969 + 3 ^ 40 * 1583904 * 2
def baseEnd_1583904 : Nat := 13387721194717303736885

theorem tailTrace_1583904 : CollatzResearch.WordTrace tailWord_1583904 prefixEnd_1583904 13387721194717303736885 := by
  unfold tailWord_1583904
  simp only [CollatzResearch.WordTrace]
  refine ⟨28884862426896896055983383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38513149902529194741311177 28884862426896896055983383)
  ·
    refine ⟨43327293640345344083975075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28884862426896896055983383 43327293640345344083975075)
    ·
      refine ⟨64990940460518016125962613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43327293640345344083975075 64990940460518016125962613)
      ·
        refine ⟨6092900668173564011808995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64990940460518016125962613 6092900668173564011808995)
        ·
          refine ⟨9139351002260346017713493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6092900668173564011808995 9139351002260346017713493)
          ·
            refine ⟨13387721194717303736885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9139351002260346017713493 13387721194717303736885)
            ·
              rfl

theorem cell21_1583904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 11].length) (baseStart_1583904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583904 prefixEnd_1583904 := by exact prefixLift 1583904
  have htrace : WordTrace (prefixWord ++ tailWord_1583904) baseStart_1583904 baseEnd_1583904 := by
    simpa [prefixWord, tailWord_1583904, baseEnd_1583904] using wordTrace_append hprefix tailTrace_1583904
  have hstable : (prefixWord ++ tailWord_1583904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583904).length < 2 ^ (prefixWord ++ tailWord_1583904).sum := by decide
  have hdescent : baseEnd_1583904 < baseStart_1583904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583935 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 7]
def baseStart_1583935 : Nat := 118140960795 + 1583935 * 2 ^ 59
def prefixEnd_1583935 : Nat := 4983230072969 + 3 ^ 40 * 1583935 * 2
def baseEnd_1583935 : Nat := 361475546879718035879165

theorem tailTrace_1583935 : CollatzResearch.WordTrace tailWord_1583935 prefixEnd_1583935 361475546879718035879165 := by
  unfold tailWord_1583935
  simp only [CollatzResearch.WordTrace]
  refine ⟨57770855516681484406345259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38513903677787656270896839 57770855516681484406345259)
  ·
    refine ⟨86656283275022226609517889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57770855516681484406345259 86656283275022226609517889)
    ·
      refine ⟨64992212456266669957138417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86656283275022226609517889 64992212456266669957138417)
      ·
        refine ⟨48744159342200002467853813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64992212456266669957138417 48744159342200002467853813)
        ·
          refine ⟨4569764938331250231361295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48744159342200002467853813 4569764938331250231361295)
          ·
            refine ⟨6854647407496875347041943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569764938331250231361295 6854647407496875347041943)
            ·
              refine ⟨10281971111245313020562915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854647407496875347041943 10281971111245313020562915)
              ·
                refine ⟨15422956666867969530844373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10281971111245313020562915 15422956666867969530844373)
                ·
                  refine ⟨361475546879718035879165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15422956666867969530844373 361475546879718035879165)
                  ·
                    rfl

theorem cell21_1583935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_1583935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583935 prefixEnd_1583935 := by exact prefixLift 1583935
  have htrace : WordTrace (prefixWord ++ tailWord_1583935) baseStart_1583935 baseEnd_1583935 := by
    simpa [prefixWord, tailWord_1583935, baseEnd_1583935] using wordTrace_append hprefix tailTrace_1583935
  have hstable : (prefixWord ++ tailWord_1583935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583935).length < 2 ^ (prefixWord ++ tailWord_1583935).sum := by decide
  have hdescent : baseEnd_1583935 < baseStart_1583935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583952 : List Nat := [2, 1, 1, 1, 1, 4, 3, 5, 3]
def baseStart_1583952 : Nat := 118140960795 + 1583952 * 2 ^ 59
def prefixEnd_1583952 : Nat := 4983230072969 + 3 ^ 40 * 1583952 * 2
def baseEnd_1583952 : Nat := 361479426511329784095797

theorem tailTrace_1583952 : CollatzResearch.WordTrace tailWord_1583952 prefixEnd_1583952 361479426511329784095797 := by
  unfold tailWord_1583952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28885737778809948154857055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38514317038413264206476073 28885737778809948154857055)
  ·
    refine ⟨43328606668214922232285583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28885737778809948154857055 43328606668214922232285583)
    ·
      refine ⟨64992910002322383348428375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43328606668214922232285583 64992910002322383348428375)
      ·
        refine ⟨97489365003483575022642563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64992910002322383348428375 97489365003483575022642563)
        ·
          refine ⟨146234047505225362533963845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97489365003483575022642563 146234047505225362533963845)
          ·
            refine ⟨27418883907229755475118221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146234047505225362533963845 27418883907229755475118221)
            ·
              refine ⟨10282081465211158303169333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27418883907229755475118221 10282081465211158303169333)
              ·
                refine ⟨963945137363546090922125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10282081465211158303169333 963945137363546090922125)
                ·
                  refine ⟨361479426511329784095797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963945137363546090922125 361479426511329784095797)
                  ·
                    rfl

theorem cell21_1583952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_1583952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583952 prefixEnd_1583952 := by exact prefixLift 1583952
  have htrace : WordTrace (prefixWord ++ tailWord_1583952) baseStart_1583952 baseEnd_1583952 := by
    simpa [prefixWord, tailWord_1583952, baseEnd_1583952] using wordTrace_append hprefix tailTrace_1583952
  have hstable : (prefixWord ++ tailWord_1583952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583952).length < 2 ^ (prefixWord ++ tailWord_1583952).sum := by decide
  have hdescent : baseEnd_1583952 < baseStart_1583952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583980 : List Nat := [2, 2, 1, 1, 4, 1, 2, 8]
def baseStart_1583980 : Nat := 118140960795 + 1583980 * 2 ^ 59
def prefixEnd_1583980 : Nat := 4983230072969 + 3 ^ 40 * 1583980 * 2
def baseEnd_1583980 : Nat := 120495272164269319209691

theorem tailTrace_1583980 : CollatzResearch.WordTrace tailWord_1583980 prefixEnd_1583980 120495272164269319209691 := by
  unfold tailWord_1583980
  simp only [CollatzResearch.WordTrace]
  refine ⟨28886248400759228545866697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38514997867678971394488929 28886248400759228545866697)
  ·
    refine ⟨21664686300569421409400023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28886248400759228545866697 21664686300569421409400023)
    ·
      refine ⟨32497029450854132114100035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21664686300569421409400023 32497029450854132114100035)
      ·
        refine ⟨48745544176281198171150053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32497029450854132114100035 48745544176281198171150053)
        ·
          refine ⟨9139789533052724657090635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48745544176281198171150053 9139789533052724657090635)
          ·
            refine ⟨13709684299579086985635953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9139789533052724657090635 13709684299579086985635953)
            ·
              refine ⟨10282263224684315239226965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13709684299579086985635953 10282263224684315239226965)
              ·
                refine ⟨120495272164269319209691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10282263224684315239226965 120495272164269319209691)
                ·
                  rfl

theorem cell21_1583980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_1583980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583980 prefixEnd_1583980 := by exact prefixLift 1583980
  have htrace : WordTrace (prefixWord ++ tailWord_1583980) baseStart_1583980 baseEnd_1583980 := by
    simpa [prefixWord, tailWord_1583980, baseEnd_1583980] using wordTrace_append hprefix tailTrace_1583980
  have hstable : (prefixWord ++ tailWord_1583980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583980).length < 2 ^ (prefixWord ++ tailWord_1583980).sum := by decide
  have hdescent : baseEnd_1583980 < baseStart_1583980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583997 : List Nat := [1, 4, 1, 1, 2, 1, 6, 5]
def baseStart_1583997 : Nat := 118140960795 + 1583997 * 2 ^ 59
def prefixEnd_1583997 : Nat := 4983230072969 + 3 ^ 40 * 1583997 * 2
def baseEnd_1583997 : Nat := 120496565374806568615235

theorem tailTrace_1583997 : CollatzResearch.WordTrace tailWord_1583997 prefixEnd_1583997 120496565374806568615235 := by
  unfold tailWord_1583997
  simp only [CollatzResearch.WordTrace]
  refine ⟨57773116842456868995102245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38515411228304579330068163 57773116842456868995102245)
  ·
    refine ⟨10832459407960662936581671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57773116842456868995102245 10832459407960662936581671)
    ·
      refine ⟨16248689111940994404872507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10832459407960662936581671 16248689111940994404872507)
      ·
        refine ⟨24373033667911491607308761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16248689111940994404872507 24373033667911491607308761)
        ·
          refine ⟨18279775250933618705481571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24373033667911491607308761 18279775250933618705481571)
          ·
            refine ⟨27419662876400428058222357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18279775250933618705481571 27419662876400428058222357)
            ·
              refine ⟨1285296697331270065229173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27419662876400428058222357 1285296697331270065229173)
              ·
                refine ⟨120496565374806568615235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1285296697331270065229173 120496565374806568615235)
                ·
                  rfl

theorem cell21_1583997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 5].length) (baseStart_1583997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1583997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1583997 prefixEnd_1583997 := by exact prefixLift 1583997
  have htrace : WordTrace (prefixWord ++ tailWord_1583997) baseStart_1583997 baseEnd_1583997 := by
    simpa [prefixWord, tailWord_1583997, baseEnd_1583997] using wordTrace_append hprefix tailTrace_1583997
  have hstable : (prefixWord ++ tailWord_1583997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583997).length < 2 ^ (prefixWord ++ tailWord_1583997).sum := by decide
  have hdescent : baseEnd_1583997 < baseStart_1583997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584056 : List Nat := [2, 1, 2, 1, 2, 4, 2, 7]
def baseStart_1584056 : Nat := 118140960795 + 1584056 * 2 ^ 59
def prefixEnd_1584056 : Nat := 4983230072969 + 3 ^ 40 * 1584056 * 2
def baseEnd_1584056 : Nat := 120501053576082904787417

theorem tailTrace_1584056 : CollatzResearch.WordTrace tailWord_1584056 prefixEnd_1584056 120501053576082904787417 := by
  unfold tailWord_1584056
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887634374621561035750011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38516845832828748047666681 28887634374621561035750011)
  ·
    refine ⟨43331451561932341553625017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28887634374621561035750011 43331451561932341553625017)
    ·
      refine ⟨32498588671449256165218763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43331451561932341553625017 32498588671449256165218763)
      ·
        refine ⟨48747883007173884247828145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32498588671449256165218763 48747883007173884247828145)
        ·
          refine ⟨36560912255380413185871109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48747883007173884247828145 36560912255380413185871109)
          ·
            refine ⟨6855171047883827472350833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36560912255380413185871109 6855171047883827472350833)
            ·
              refine ⟨5141378285912870604263125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6855171047883827472350833 5141378285912870604263125)
              ·
                refine ⟨120501053576082904787417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5141378285912870604263125 120501053576082904787417)
                ·
                  rfl

theorem cell21_1584056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_1584056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584056 prefixEnd_1584056 := by exact prefixLift 1584056
  have htrace : WordTrace (prefixWord ++ tailWord_1584056) baseStart_1584056 baseEnd_1584056 := by
    simpa [prefixWord, tailWord_1584056, baseEnd_1584056] using wordTrace_append hprefix tailTrace_1584056
  have hstable : (prefixWord ++ tailWord_1584056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584056).length < 2 ^ (prefixWord ++ tailWord_1584056).sum := by decide
  have hdescent : baseEnd_1584056 < baseStart_1584056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584163 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 5]
def baseStart_1584163 : Nat := 118140960795 + 1584163 * 2 ^ 59
def prefixEnd_1584163 : Nat := 4983230072969 + 3 ^ 40 * 1584163 * 2
def baseEnd_1584163 : Nat := 361527579586040306078699

theorem tailTrace_1584163 : CollatzResearch.WordTrace tailWord_1584163 prefixEnd_1584163 361527579586040306078699 := by
  unfold tailWord_1584163
  simp only [CollatzResearch.WordTrace]
  refine ⟨57779171359855479345645143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38519447573236986230430095 57779171359855479345645143)
  ·
    refine ⟨86668757039783219018467715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57779171359855479345645143 86668757039783219018467715)
    ·
      refine ⟨130003135559674828527701573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86668757039783219018467715 130003135559674828527701573)
      ·
        refine ⟨24375587917439030348944045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130003135559674828527701573 24375587917439030348944045)
        ·
          refine ⟨9140845469039636380854017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24375587917439030348944045 9140845469039636380854017)
          ·
            refine ⟨6855634101779727285640513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9140845469039636380854017 6855634101779727285640513)
            ·
              refine ⟨5141725576334795464230385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6855634101779727285640513 5141725576334795464230385)
              ·
                refine ⟨3856294182251096598172789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5141725576334795464230385 3856294182251096598172789)
                ·
                  refine ⟨361527579586040306078699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3856294182251096598172789 361527579586040306078699)
                  ·
                    rfl

theorem cell21_1584163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_1584163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584163 prefixEnd_1584163 := by exact prefixLift 1584163
  have htrace : WordTrace (prefixWord ++ tailWord_1584163) baseStart_1584163 baseEnd_1584163 := by
    simpa [prefixWord, tailWord_1584163, baseEnd_1584163] using wordTrace_append hprefix tailTrace_1584163
  have hstable : (prefixWord ++ tailWord_1584163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584163).length < 2 ^ (prefixWord ++ tailWord_1584163).sum := by decide
  have hdescent : baseEnd_1584163 < baseStart_1584163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584177 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 8]
def baseStart_1584177 : Nat := 118140960795 + 1584177 * 2 ^ 59
def prefixEnd_1584177 : Nat := 4983230072969 + 3 ^ 40 * 1584177 * 2
def baseEnd_1584177 : Nat := 361530774576779392845337

theorem tailTrace_1584177 : CollatzResearch.WordTrace tailWord_1584177 prefixEnd_1584177 361530774576779392845337 := by
  unfold tailWord_1584177
  simp only [CollatzResearch.WordTrace]
  refine ⟨57779681981804759736654785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38519787987869839824436523 57779681981804759736654785)
  ·
    refine ⟨43334761486353569802491089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57779681981804759736654785 43334761486353569802491089)
    ·
      refine ⟨32501071114765177351868317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43334761486353569802491089 32501071114765177351868317)
      ·
        refine ⟨12187901668036941506950619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32501071114765177351868317 12187901668036941506950619)
        ·
          refine ⟨18281852502055412260425929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12187901668036941506950619 18281852502055412260425929)
          ·
            refine ⟨13711389376541559195319447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18281852502055412260425929 13711389376541559195319447)
            ·
              refine ⟨20567084064812338792979171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13711389376541559195319447 20567084064812338792979171)
              ·
                refine ⟨30850626097218508189468757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20567084064812338792979171 30850626097218508189468757)
                ·
                  refine ⟨361530774576779392845337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30850626097218508189468757 361530774576779392845337)
                  ·
                    rfl

theorem cell21_1584177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_1584177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584177 prefixEnd_1584177 := by exact prefixLift 1584177
  have htrace : WordTrace (prefixWord ++ tailWord_1584177) baseStart_1584177 baseEnd_1584177 := by
    simpa [prefixWord, tailWord_1584177, baseEnd_1584177] using wordTrace_append hprefix tailTrace_1584177
  have hstable : (prefixWord ++ tailWord_1584177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584177).length < 2 ^ (prefixWord ++ tailWord_1584177).sum := by decide
  have hdescent : baseEnd_1584177 < baseStart_1584177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584290 : List Nat := [3, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_1584290 : Nat := 118140960795 + 1584290 * 2 ^ 59
def prefixEnd_1584290 : Nat := 4983230072969 + 3 ^ 40 * 1584290 * 2
def baseEnd_1584290 : Nat := 361556562716316307461773

theorem tailTrace_1584290 : CollatzResearch.WordTrace tailWord_1584290 prefixEnd_1584290 361556562716316307461773 := by
  unfold tailWord_1584290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14445950857598845008879581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38522535620263586690345549 14445950857598845008879581)
  ·
    refine ⟨5417231571599566878329843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14445950857598845008879581 5417231571599566878329843)
    ·
      refine ⟨8125847357399350317494765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5417231571599566878329843 8125847357399350317494765)
      ·
        refine ⟨3047192759024756369060537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8125847357399350317494765 3047192759024756369060537)
        ·
          refine ⟨2285394569268567276795403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3047192759024756369060537 2285394569268567276795403)
          ·
            refine ⟨3428091853902850915193105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285394569268567276795403 3428091853902850915193105)
            ·
              refine ⟨2571068890427138186394829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3428091853902850915193105 2571068890427138186394829)
              ·
                refine ⟨964150833910176819898061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2571068890427138186394829 964150833910176819898061)
                ·
                  refine ⟨361556562716316307461773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964150833910176819898061 361556562716316307461773)
                  ·
                    rfl

theorem cell21_1584290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_1584290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584290 prefixEnd_1584290 := by exact prefixLift 1584290
  have htrace : WordTrace (prefixWord ++ tailWord_1584290) baseStart_1584290 baseEnd_1584290 := by
    simpa [prefixWord, tailWord_1584290, baseEnd_1584290] using wordTrace_append hprefix tailTrace_1584290
  have hstable : (prefixWord ++ tailWord_1584290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584290).length < 2 ^ (prefixWord ++ tailWord_1584290).sum := by decide
  have hdescent : baseEnd_1584290 < baseStart_1584290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584301 : List Nat := [1, 5, 2, 1, 3, 1, 8]
def baseStart_1584301 : Nat := 118140960795 + 1584301 * 2 ^ 59
def prefixEnd_1584301 : Nat := 4983230072969 + 3 ^ 40 * 1584301 * 2
def baseEnd_1584301 : Nat := 40173230340686970308713

theorem tailTrace_1584301 : CollatzResearch.WordTrace tailWord_1584301 prefixEnd_1584301 40173230340686970308713 := by
  unfold tailWord_1584301
  simp only [CollatzResearch.WordTrace]
  refine ⟨57784204633355528914168757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38522803088903685942779171 57784204633355528914168757)
  ·
    refine ⟨5417269184377080835703321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57784204633355528914168757 5417269184377080835703321)
    ·
      refine ⟨4062951888282810626777491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5417269184377080835703321 4062951888282810626777491)
      ·
        refine ⟨6094427832424215940166237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4062951888282810626777491 6094427832424215940166237)
        ·
          refine ⟨2285410437159080977562339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6094427832424215940166237 2285410437159080977562339)
          ·
            refine ⟨3428115655738621466343509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285410437159080977562339 3428115655738621466343509)
            ·
              refine ⟨40173230340686970308713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3428115655738621466343509 40173230340686970308713)
              ·
                rfl

theorem cell21_1584301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 8].length) (baseStart_1584301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584301 prefixEnd_1584301 := by exact prefixLift 1584301
  have htrace : WordTrace (prefixWord ++ tailWord_1584301) baseStart_1584301 baseEnd_1584301 := by
    simpa [prefixWord, tailWord_1584301, baseEnd_1584301] using wordTrace_append hprefix tailTrace_1584301
  have hstable : (prefixWord ++ tailWord_1584301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584301).length < 2 ^ (prefixWord ++ tailWord_1584301).sum := by decide
  have hdescent : baseEnd_1584301 < baseStart_1584301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584380 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_1584380 : Nat := 118140960795 + 1584380 * 2 ^ 59
def prefixEnd_1584380 : Nat := 4983230072969 + 3 ^ 40 * 1584380 * 2
def baseEnd_1584380 : Nat := 361577101942496150961589

theorem tailTrace_1584380 : CollatzResearch.WordTrace tailWord_1584380 prefixEnd_1584380 361577101942496150961589 := by
  unfold tailWord_1584380
  simp only [CollatzResearch.WordTrace]
  refine ⟨28893543000034662703147297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38524724000046216937529729 28893543000034662703147297)
  ·
    refine ⟨21670157250025997027360473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28893543000034662703147297 21670157250025997027360473)
    ·
      refine ⟨16252617937519497770520355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21670157250025997027360473 16252617937519497770520355)
      ·
        refine ⟨24378926906279246655780533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16252617937519497770520355 24378926906279246655780533)
        ·
          refine ⟨2285524397463679373979425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24378926906279246655780533 2285524397463679373979425)
          ·
            refine ⟨1714143298097759530484569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2285524397463679373979425 1714143298097759530484569)
            ·
              refine ⟨1285607473573319647863427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714143298097759530484569 1285607473573319647863427)
              ·
                refine ⟨1928411210359979471795141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285607473573319647863427 1928411210359979471795141)
                ·
                  refine ⟨361577101942496150961589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1928411210359979471795141 361577101942496150961589)
                  ·
                    rfl

theorem cell21_1584380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_1584380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584380 prefixEnd_1584380 := by exact prefixLift 1584380
  have htrace : WordTrace (prefixWord ++ tailWord_1584380) baseStart_1584380 baseEnd_1584380 := by
    simpa [prefixWord, tailWord_1584380, baseEnd_1584380] using wordTrace_append hprefix tailTrace_1584380
  have hstable : (prefixWord ++ tailWord_1584380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584380).length < 2 ^ (prefixWord ++ tailWord_1584380).sum := by decide
  have hdescent : baseEnd_1584380 < baseStart_1584380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584419 : List Nat := [1, 1, 1, 4, 2, 12]
def baseStart_1584419 : Nat := 118140960795 + 1584419 * 2 ^ 59
def prefixEnd_1584419 : Nat := 4983230072969 + 3 ^ 40 * 1584419 * 2
def baseEnd_1584419 : Nat := 13392074158290398141167

theorem tailTrace_1584419 : CollatzResearch.WordTrace tailWord_1584419 prefixEnd_1584419 13392074158290398141167 := by
  unfold tailWord_1584419
  simp only [CollatzResearch.WordTrace]
  refine ⟨57788508446928035066964311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38525672297952023377976207 57788508446928035066964311)
  ·
    refine ⟨86682762670392052600446467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57788508446928035066964311 86682762670392052600446467)
    ·
      refine ⟨130024144005588078900669701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86682762670392052600446467 130024144005588078900669701)
      ·
        refine ⟨24379527001047764793875569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130024144005588078900669701 24379527001047764793875569)
        ·
          refine ⟨18284645250785823595406677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24379527001047764793875569 18284645250785823595406677)
          ·
            refine ⟨13392074158290398141167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18284645250785823595406677 13392074158290398141167)
            ·
              rfl

theorem cell21_1584419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 12].length) (baseStart_1584419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584419 prefixEnd_1584419 := by exact prefixLift 1584419
  have htrace : WordTrace (prefixWord ++ tailWord_1584419) baseStart_1584419 baseEnd_1584419 := by
    simpa [prefixWord, tailWord_1584419, baseEnd_1584419] using wordTrace_append hprefix tailTrace_1584419
  have hstable : (prefixWord ++ tailWord_1584419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584419).length < 2 ^ (prefixWord ++ tailWord_1584419).sum := by decide
  have hdescent : baseEnd_1584419 < baseStart_1584419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584484 : List Nat := [2, 3, 1, 1, 3, 2, 2, 4, 3]
def baseStart_1584484 : Nat := 118140960795 + 1584484 * 2 ^ 59
def prefixEnd_1584484 : Nat := 4983230072969 + 3 ^ 40 * 1584484 * 2
def baseEnd_1584484 : Nat := 361600836159415081228043

theorem tailTrace_1584484 : CollatzResearch.WordTrace tailWord_1584484 prefixEnd_1584484 361600836159415081228043 := by
  unfold tailWord_1584484
  simp only [CollatzResearch.WordTrace]
  refine ⟨28895439595846275584040253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38527252794461700778720337 28895439595846275584040253)
  ·
    refine ⟨10835789848442353344015095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28895439595846275584040253 10835789848442353344015095)
    ·
      refine ⟨16253684772663530016022643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10835789848442353344015095 16253684772663530016022643)
      ·
        refine ⟨24380527158995295024033965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16253684772663530016022643 24380527158995295024033965)
        ·
          refine ⟨9142697684623235634012737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24380527158995295024033965 9142697684623235634012737)
          ·
            refine ⟨6857023263467426725509553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9142697684623235634012737 6857023263467426725509553)
            ·
              refine ⟨5142767447600570044132165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6857023263467426725509553 5142767447600570044132165)
              ·
                refine ⟨964268896425106883274781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5142767447600570044132165 964268896425106883274781)
                ·
                  refine ⟨361600836159415081228043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964268896425106883274781 361600836159415081228043)
                  ·
                    rfl

theorem cell21_1584484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_1584484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584484 prefixEnd_1584484 := by exact prefixLift 1584484
  have htrace : WordTrace (prefixWord ++ tailWord_1584484) baseStart_1584484 baseEnd_1584484 := by
    simpa [prefixWord, tailWord_1584484, baseEnd_1584484] using wordTrace_append hprefix tailTrace_1584484
  have hstable : (prefixWord ++ tailWord_1584484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584484).length < 2 ^ (prefixWord ++ tailWord_1584484).sum := by decide
  have hdescent : baseEnd_1584484 < baseStart_1584484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584495 : List Nat := [1, 1, 2, 1, 3, 1, 4, 8]
def baseStart_1584495 : Nat := 118140960795 + 1584495 * 2 ^ 59
def prefixEnd_1584495 : Nat := 4983230072969 + 3 ^ 40 * 1584495 * 2
def baseEnd_1584495 : Nat := 120534448836427168848229

theorem tailTrace_1584495 : CollatzResearch.WordTrace tailWord_1584495 prefixEnd_1584495 120534448836427168848229 := by
  unfold tailWord_1584495
  simp only [CollatzResearch.WordTrace]
  refine ⟨57791280394652700046730939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38527520263101800031153959 57791280394652700046730939)
  ·
    refine ⟨86686920591979050070096409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57791280394652700046730939 86686920591979050070096409)
    ·
      refine ⟨65015190443984287552572307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86686920591979050070096409 65015190443984287552572307)
      ·
        refine ⟨97522785665976431328858461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65015190443984287552572307 97522785665976431328858461)
        ·
          refine ⟨36571044624741161748321923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97522785665976431328858461 36571044624741161748321923)
          ·
            refine ⟨54856566937111742622482885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36571044624741161748321923 54856566937111742622482885)
            ·
              refine ⟨10285606300708451741715541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54856566937111742622482885 10285606300708451741715541)
              ·
                refine ⟨120534448836427168848229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10285606300708451741715541 120534448836427168848229)
                ·
                  rfl

theorem cell21_1584495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 8].length) (baseStart_1584495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584495 prefixEnd_1584495 := by exact prefixLift 1584495
  have htrace : WordTrace (prefixWord ++ tailWord_1584495) baseStart_1584495 baseEnd_1584495 := by
    simpa [prefixWord, tailWord_1584495, baseEnd_1584495] using wordTrace_append hprefix tailTrace_1584495
  have hstable : (prefixWord ++ tailWord_1584495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584495).length < 2 ^ (prefixWord ++ tailWord_1584495).sum := by decide
  have hdescent : baseEnd_1584495 < baseStart_1584495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584543 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 5]
def baseStart_1584543 : Nat := 118140960795 + 1584543 * 2 ^ 59
def prefixEnd_1584543 : Nat := 4983230072969 + 3 ^ 40 * 1584543 * 2
def baseEnd_1584543 : Nat := 361614300763244089744589

theorem tailTrace_1584543 : CollatzResearch.WordTrace tailWord_1584543 prefixEnd_1584543 361614300763244089744589 := by
  unfold tailWord_1584543
  simp only [CollatzResearch.WordTrace]
  refine ⟨57793031098478804244478283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38528687398985869496318855 57793031098478804244478283)
  ·
    refine ⟨86689546647718206366717425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57793031098478804244478283 86689546647718206366717425)
    ·
      refine ⟨65017159985788654775038069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86689546647718206366717425 65017159985788654775038069)
      ·
        refine ⟨6095358748667686385159819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65017159985788654775038069 6095358748667686385159819)
        ·
          refine ⟨9143038123001529577739729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6095358748667686385159819 9143038123001529577739729)
          ·
            refine ⟨6857278592251147183304797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9143038123001529577739729 6857278592251147183304797)
            ·
              refine ⟨2571479472094180193739299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6857278592251147183304797 2571479472094180193739299)
              ·
                refine ⟨3857219208141270290608949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571479472094180193739299 3857219208141270290608949)
                ·
                  refine ⟨361614300763244089744589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3857219208141270290608949 361614300763244089744589)
                  ·
                    rfl

theorem cell21_1584543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 5].length) (baseStart_1584543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584543 prefixEnd_1584543 := by exact prefixLift 1584543
  have htrace : WordTrace (prefixWord ++ tailWord_1584543) baseStart_1584543 baseEnd_1584543 := by
    simpa [prefixWord, tailWord_1584543, baseEnd_1584543] using wordTrace_append hprefix tailTrace_1584543
  have hstable : (prefixWord ++ tailWord_1584543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584543).length < 2 ^ (prefixWord ++ tailWord_1584543).sum := by decide
  have hdescent : baseEnd_1584543 < baseStart_1584543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584605 : List Nat := [1, 4, 3, 1, 1, 4, 1, 6]
def baseStart_1584605 : Nat := 118140960795 + 1584605 * 2 ^ 59
def prefixEnd_1584605 : Nat := 4983230072969 + 3 ^ 40 * 1584605 * 2
def baseEnd_1584605 : Nat := 120542816669315253237043

theorem tailTrace_1584605 : CollatzResearch.WordTrace tailWord_1584605 prefixEnd_1584605 120542816669315253237043 := by
  unfold tailWord_1584605
  simp only [CollatzResearch.WordTrace]
  refine ⟨57795292424254188833235269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38530194949502792555490179 57795292424254188833235269)
  ·
    refine ⟨10836617329547660406231613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57795292424254188833235269 10836617329547660406231613)
    ·
      refine ⟨4063731498580372652336855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10836617329547660406231613 4063731498580372652336855)
      ·
        refine ⟨6095597247870558978505283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063731498580372652336855 6095597247870558978505283)
        ·
          refine ⟨9143395871805838467757925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6095597247870558978505283 9143395871805838467757925)
          ·
            refine ⟨1714386725963594712704611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9143395871805838467757925 1714386725963594712704611)
            ·
              refine ⟨2571580088945392069056917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714386725963594712704611 2571580088945392069056917)
              ·
                refine ⟨120542816669315253237043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2571580088945392069056917 120542816669315253237043)
                ·
                  rfl

theorem cell21_1584605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 6].length) (baseStart_1584605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584605 prefixEnd_1584605 := by exact prefixLift 1584605
  have htrace : WordTrace (prefixWord ++ tailWord_1584605) baseStart_1584605 baseEnd_1584605 := by
    simpa [prefixWord, tailWord_1584605, baseEnd_1584605] using wordTrace_append hprefix tailTrace_1584605
  have hstable : (prefixWord ++ tailWord_1584605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584605).length < 2 ^ (prefixWord ++ tailWord_1584605).sum := by decide
  have hdescent : baseEnd_1584605 < baseStart_1584605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584650 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_1584650 : Nat := 118140960795 + 1584650 * 2 ^ 59
def prefixEnd_1584650 : Nat := 4983230072969 + 3 ^ 40 * 1584650 * 2
def baseEnd_1584650 : Nat := 361638719621035681461037

theorem tailTrace_1584650 : CollatzResearch.WordTrace tailWord_1584650 prefixEnd_1584650 361638719621035681461037 := by
  unfold tailWord_1584650
  simp only [CollatzResearch.WordTrace]
  refine ⟨14449233427272790379655851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38531289139394107679082269 14449233427272790379655851)
  ·
    refine ⟨21673850140909185569483777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14449233427272790379655851 21673850140909185569483777)
    ·
      refine ⟨16255387605681889177112833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21673850140909185569483777 16255387605681889177112833)
      ·
        refine ⟨12191540704261416882834625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16255387605681889177112833 12191540704261416882834625)
        ·
          refine ⟨9143655528196062662125969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12191540704261416882834625 9143655528196062662125969)
          ·
            refine ⟨6857741646147046996594477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9143655528196062662125969 6857741646147046996594477)
            ·
              refine ⟨2571653117305142623722929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6857741646147046996594477 2571653117305142623722929)
              ·
                refine ⟨1928739837978856967792197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2571653117305142623722929 1928739837978856967792197)
                ·
                  refine ⟨361638719621035681461037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1928739837978856967792197 361638719621035681461037)
                  ·
                    rfl

theorem cell21_1584650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_1584650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584650 prefixEnd_1584650 := by exact prefixLift 1584650
  have htrace : WordTrace (prefixWord ++ tailWord_1584650) baseStart_1584650 baseEnd_1584650 := by
    simpa [prefixWord, tailWord_1584650, baseEnd_1584650] using wordTrace_append hprefix tailTrace_1584650
  have hstable : (prefixWord ++ tailWord_1584650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584650).length < 2 ^ (prefixWord ++ tailWord_1584650).sum := by decide
  have hdescent : baseEnd_1584650 < baseStart_1584650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584709 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 4]
def baseStart_1584709 : Nat := 118140960795 + 1584709 * 2 ^ 59
def prefixEnd_1584709 : Nat := 4983230072969 + 3 ^ 40 * 1584709 * 2
def baseEnd_1584709 : Nat := 361652184224864689977583

theorem tailTrace_1584709 : CollatzResearch.WordTrace tailWord_1584709 prefixEnd_1584709 361652184224864689977583 := by
  unfold tailWord_1584709
  simp only [CollatzResearch.WordTrace]
  refine ⟨57799085615877414595021181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38532723743918276396680787 57799085615877414595021181)
  ·
    refine ⟨21674657105954030473132943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57799085615877414595021181 21674657105954030473132943)
    ·
      refine ⟨32511985658931045709699415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21674657105954030473132943 32511985658931045709699415)
      ·
        refine ⟨48767978488396568564549123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32511985658931045709699415 48767978488396568564549123)
        ·
          refine ⟨73151967732594852846823685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48767978488396568564549123 73151967732594852846823685)
          ·
            refine ⟨13715993949861534908779441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73151967732594852846823685 13715993949861534908779441)
            ·
              refine ⟨10286995462396151181584581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13715993949861534908779441 10286995462396151181584581)
              ·
                refine ⟨1928811649199278346547109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10286995462396151181584581 1928811649199278346547109)
                ·
                  refine ⟨361652184224864689977583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1928811649199278346547109 361652184224864689977583)
                  ·
                    rfl

theorem cell21_1584709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_1584709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584709 prefixEnd_1584709 := by exact prefixLift 1584709
  have htrace : WordTrace (prefixWord ++ tailWord_1584709) baseStart_1584709 baseEnd_1584709 := by
    simpa [prefixWord, tailWord_1584709, baseEnd_1584709] using wordTrace_append hprefix tailTrace_1584709
  have hstable : (prefixWord ++ tailWord_1584709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584709).length < 2 ^ (prefixWord ++ tailWord_1584709).sum := by decide
  have hdescent : baseEnd_1584709 < baseStart_1584709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584788 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1584788 : Nat := 118140960795 + 1584788 * 2 ^ 59
def prefixEnd_1584788 : Nat := 4983230072969 + 3 ^ 40 * 1584788 * 2
def baseEnd_1584788 : Nat := 361670213101178108160755

theorem tailTrace_1584788 : CollatzResearch.WordTrace tailWord_1584788 prefixEnd_1584788 361670213101178108160755 := by
  unfold tailWord_1584788
  simp only [CollatzResearch.WordTrace]
  refine ⟨28900983491295605543573509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38534644655060807391431345 28900983491295605543573509)
  ·
    refine ⟨5418934404617926039420033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28900983491295605543573509 5418934404617926039420033)
    ·
      refine ⟨4064200803463444529565025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5418934404617926039420033 4064200803463444529565025)
      ·
        refine ⟨3048150602597583397173769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4064200803463444529565025 3048150602597583397173769)
        ·
          refine ⟨2286112951948187547880327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048150602597583397173769 2286112951948187547880327)
          ·
            refine ⟨3429169427922281321820491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286112951948187547880327 3429169427922281321820491)
            ·
              refine ⟨5143754141883421982730737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429169427922281321820491 5143754141883421982730737)
              ·
                refine ⟨3857815606412566487048053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143754141883421982730737 3857815606412566487048053)
                ·
                  refine ⟨361670213101178108160755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3857815606412566487048053 361670213101178108160755)
                  ·
                    rfl

theorem cell21_1584788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1584788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584788 prefixEnd_1584788 := by exact prefixLift 1584788
  have htrace : WordTrace (prefixWord ++ tailWord_1584788) baseStart_1584788 baseEnd_1584788 := by
    simpa [prefixWord, tailWord_1584788, baseEnd_1584788] using wordTrace_append hprefix tailTrace_1584788
  have hstable : (prefixWord ++ tailWord_1584788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584788).length < 2 ^ (prefixWord ++ tailWord_1584788).sum := by decide
  have hdescent : baseEnd_1584788 < baseStart_1584788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584920 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_1584920 : Nat := 118140960795 + 1584920 * 2 ^ 59
def prefixEnd_1584920 : Nat := 4983230072969 + 3 ^ 40 * 1584920 * 2
def baseEnd_1584920 : Nat := 361700337299575211960485

theorem tailTrace_1584920 : CollatzResearch.WordTrace tailWord_1584920 prefixEnd_1584920 361700337299575211960485 := by
  unfold tailWord_1584920
  simp only [CollatzResearch.WordTrace]
  refine ⟨28903390709056498815476107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38537854278741998420634809 28903390709056498815476107)
  ·
    refine ⟨43355086063584748223214161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28903390709056498815476107 43355086063584748223214161)
    ·
      refine ⟨32516314547688561167410621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43355086063584748223214161 32516314547688561167410621)
      ·
        refine ⟨12193617955383210437778983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32516314547688561167410621 12193617955383210437778983)
        ·
          refine ⟨18290426933074815656668475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12193617955383210437778983 18290426933074815656668475)
          ·
            refine ⟨27435640399612223485002713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18290426933074815656668475 27435640399612223485002713)
            ·
              refine ⟨20576730299709167613752035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27435640399612223485002713 20576730299709167613752035)
              ·
                refine ⟨30865095449563751420628053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20576730299709167613752035 30865095449563751420628053)
                ·
                  refine ⟨361700337299575211960485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30865095449563751420628053 361700337299575211960485)
                  ·
                    rfl

theorem cell21_1584920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_1584920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584920 prefixEnd_1584920 := by exact prefixLift 1584920
  have htrace : WordTrace (prefixWord ++ tailWord_1584920) baseStart_1584920 baseEnd_1584920 := by
    simpa [prefixWord, tailWord_1584920, baseEnd_1584920] using wordTrace_append hprefix tailTrace_1584920
  have hstable : (prefixWord ++ tailWord_1584920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584920).length < 2 ^ (prefixWord ++ tailWord_1584920).sum := by decide
  have hdescent : baseEnd_1584920 < baseStart_1584920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584926 : List Nat := [4, 3, 2, 2, 2, 8]
def baseStart_1584926 : Nat := 118140960795 + 1584926 * 2 ^ 59
def prefixEnd_1584926 : Nat := 4983230072969 + 3 ^ 40 * 1584926 * 2
def baseEnd_1584926 : Nat := 13396359503011871661499

theorem tailTrace_1584926 : CollatzResearch.WordTrace tailWord_1584926 prefixEnd_1584926 13396359503011871661499 := by
  unfold tailWord_1584926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225875032011407581958829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38538000170727507103780421 7225875032011407581958829)
  ·
    refine ⟨2709703137004277843234561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7225875032011407581958829 2709703137004277843234561)
    ·
      refine ⟨2032277352753208382425921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2709703137004277843234561 2032277352753208382425921)
      ·
        refine ⟨1524208014564906286819441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2032277352753208382425921 1524208014564906286819441)
        ·
          refine ⟨1143156010923679715114581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1524208014564906286819441 1143156010923679715114581)
          ·
            refine ⟨13396359503011871661499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1143156010923679715114581 13396359503011871661499)
            ·
              rfl

theorem cell21_1584926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 8].length) (baseStart_1584926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584926 prefixEnd_1584926 := by exact prefixLift 1584926
  have htrace : WordTrace (prefixWord ++ tailWord_1584926) baseStart_1584926 baseEnd_1584926 := by
    simpa [prefixWord, tailWord_1584926, baseEnd_1584926] using wordTrace_append hprefix tailTrace_1584926
  have hstable : (prefixWord ++ tailWord_1584926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584926).length < 2 ^ (prefixWord ++ tailWord_1584926).sum := by decide
  have hdescent : baseEnd_1584926 < baseStart_1584926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584940 : List Nat := [2, 2, 1, 1, 1, 5, 4, 2, 3]
def baseStart_1584940 : Nat := 118140960795 + 1584940 * 2 ^ 59
def prefixEnd_1584940 : Nat := 4983230072969 + 3 ^ 40 * 1584940 * 2
def baseEnd_1584940 : Nat := 361704901572059621627111

theorem tailTrace_1584940 : CollatzResearch.WordTrace tailWord_1584940 prefixEnd_1584940 361704901572059621627111 := by
  unfold tailWord_1584940
  simp only [CollatzResearch.WordTrace]
  refine ⟨28903755439020270523340137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38538340585360360697786849 28903755439020270523340137)
  ·
    refine ⟨21677816579265202892505103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28903755439020270523340137 21677816579265202892505103)
    ·
      refine ⟨32516724868897804338757655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21677816579265202892505103 32516724868897804338757655)
      ·
        refine ⟨48775087303346706508136483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32516724868897804338757655 48775087303346706508136483)
        ·
          refine ⟨73162630955020059762204725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48775087303346706508136483 73162630955020059762204725)
          ·
            refine ⟨6858996652033130602706693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73162630955020059762204725 6858996652033130602706693)
            ·
              refine ⟨1286061872256211988007505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6858996652033130602706693 1286061872256211988007505)
              ·
                refine ⟨964546404192158991005629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286061872256211988007505 964546404192158991005629)
                ·
                  refine ⟨361704901572059621627111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964546404192158991005629 361704901572059621627111)
                  ·
                    rfl

theorem cell21_1584940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_1584940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584940 prefixEnd_1584940 := by exact prefixLift 1584940
  have htrace : WordTrace (prefixWord ++ tailWord_1584940) baseStart_1584940 baseEnd_1584940 := by
    simpa [prefixWord, tailWord_1584940, baseEnd_1584940] using wordTrace_append hprefix tailTrace_1584940
  have hstable : (prefixWord ++ tailWord_1584940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584940).length < 2 ^ (prefixWord ++ tailWord_1584940).sum := by decide
  have hdescent : baseEnd_1584940 < baseStart_1584940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584968 : List Nat := [2, 1, 3, 1, 1, 5, 3, 5]
def baseStart_1584968 : Nat := 118140960795 + 1584968 * 2 ^ 59
def prefixEnd_1584968 : Nat := 4983230072969 + 3 ^ 40 * 1584968 * 2
def baseEnd_1584968 : Nat := 120570430517845931720129

theorem tailTrace_1584968 : CollatzResearch.WordTrace tailWord_1584968 prefixEnd_1584968 120570430517845931720129 := by
  unfold tailWord_1584968
  simp only [CollatzResearch.WordTrace]
  refine ⟨28904266060969550914349779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38539021414626067885799705 28904266060969550914349779)
  ·
    refine ⟨43356399091454326371524669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28904266060969550914349779 43356399091454326371524669)
    ·
      refine ⟨16258649659295372389321751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43356399091454326371524669 16258649659295372389321751)
      ·
        refine ⟨24387974488943058583982627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16258649659295372389321751 24387974488943058583982627)
        ·
          refine ⟨36581961733414587875973941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24387974488943058583982627 36581961733414587875973941)
          ·
            refine ⟨3429558912507617613372557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36581961733414587875973941 3429558912507617613372557)
            ·
              refine ⟨1286084592190356605014709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3429558912507617613372557 1286084592190356605014709)
              ·
                refine ⟨120570430517845931720129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1286084592190356605014709 120570430517845931720129)
                ·
                  rfl

theorem cell21_1584968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_1584968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584968 prefixEnd_1584968 := by exact prefixLift 1584968
  have htrace : WordTrace (prefixWord ++ tailWord_1584968) baseStart_1584968 baseEnd_1584968 := by
    simpa [prefixWord, tailWord_1584968, baseEnd_1584968] using wordTrace_append hprefix tailTrace_1584968
  have hstable : (prefixWord ++ tailWord_1584968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584968).length < 2 ^ (prefixWord ++ tailWord_1584968).sum := by decide
  have hdescent : baseEnd_1584968 < baseStart_1584968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584988 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 4]
def baseStart_1584988 : Nat := 118140960795 + 1584988 * 2 ^ 59
def prefixEnd_1584988 : Nat := 4983230072969 + 3 ^ 40 * 1584988 * 2
def baseEnd_1584988 : Nat := 361715855826022204827013

theorem tailTrace_1584988 : CollatzResearch.WordTrace tailWord_1584988 prefixEnd_1584988 361715855826022204827013 := by
  unfold tailWord_1584988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28904630790933322622213809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38539507721244430162951745 28904630790933322622213809)
  ·
    refine ⟨21678473093199991966660357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28904630790933322622213809 21678473093199991966660357)
    ·
      refine ⟨4064713704974998493748817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21678473093199991966660357 4064713704974998493748817)
      ·
        refine ⟨3048535278731248870311613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4064713704974998493748817 3048535278731248870311613)
        ·
          refine ⟨1143200729524218326366855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3048535278731248870311613 1143200729524218326366855)
          ·
            refine ⟨1714801094286327489550283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143200729524218326366855 1714801094286327489550283)
            ·
              refine ⟨2572201641429491234325425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714801094286327489550283 2572201641429491234325425)
              ·
                refine ⟨1929151231072118425744069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2572201641429491234325425 1929151231072118425744069)
                ·
                  refine ⟨361715855826022204827013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1929151231072118425744069 361715855826022204827013)
                  ·
                    rfl

theorem cell21_1584988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_1584988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584988 prefixEnd_1584988 := by exact prefixLift 1584988
  have htrace : WordTrace (prefixWord ++ tailWord_1584988) baseStart_1584988 baseEnd_1584988 := by
    simpa [prefixWord, tailWord_1584988, baseEnd_1584988] using wordTrace_append hprefix tailTrace_1584988
  have hstable : (prefixWord ++ tailWord_1584988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584988).length < 2 ^ (prefixWord ++ tailWord_1584988).sum := by decide
  have hdescent : baseEnd_1584988 < baseStart_1584988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584999 : List Nat := [1, 1, 5, 1, 2, 1, 1, 6, 3]
def baseStart_1584999 : Nat := 118140960795 + 1584999 * 2 ^ 59
def prefixEnd_1584999 : Nat := 4983230072969 + 3 ^ 40 * 1584999 * 2
def baseEnd_1584999 : Nat := 361718366175888630143657

theorem tailTrace_1584999 : CollatzResearch.WordTrace tailWord_1584999 prefixEnd_1584999 361718366175888630143657 := by
  unfold tailWord_1584999
  simp only [CollatzResearch.WordTrace]
  refine ⟨57809662784826794123078051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38539775189884529415385367 57809662784826794123078051)
  ·
    refine ⟨86714494177240191184617077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57809662784826794123078051 86714494177240191184617077)
    ·
      refine ⟨8129483829116267923557851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86714494177240191184617077 8129483829116267923557851)
      ·
        refine ⟨12194225743674401885336777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8129483829116267923557851 12194225743674401885336777)
        ·
          refine ⟨9145669307755801414002583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12194225743674401885336777 9145669307755801414002583)
          ·
            refine ⟨13718503961633702121003875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9145669307755801414002583 13718503961633702121003875)
            ·
              refine ⟨20577755942450553181505813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13718503961633702121003875 20577755942450553181505813)
              ·
                refine ⟨964582309802369680383085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20577755942450553181505813 964582309802369680383085)
                ·
                  refine ⟨361718366175888630143657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964582309802369680383085 361718366175888630143657)
                  ·
                    rfl

theorem cell21_1584999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 3].length) (baseStart_1584999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1584999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1584999 prefixEnd_1584999 := by exact prefixLift 1584999
  have htrace : WordTrace (prefixWord ++ tailWord_1584999) baseStart_1584999 baseEnd_1584999 := by
    simpa [prefixWord, tailWord_1584999, baseEnd_1584999] using wordTrace_append hprefix tailTrace_1584999
  have hstable : (prefixWord ++ tailWord_1584999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584999).length < 2 ^ (prefixWord ++ tailWord_1584999).sum := by decide
  have hdescent : baseEnd_1584999 < baseStart_1584999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585027 : List Nat := [1, 1, 1, 3, 4, 3, 1, 7]
def baseStart_1585027 : Nat := 118140960795 + 1585027 * 2 ^ 59
def prefixEnd_1585027 : Nat := 4983230072969 + 3 ^ 40 * 1585027 * 2
def baseEnd_1585027 : Nat := 120574918719122267892311

theorem tailTrace_1585027 : CollatzResearch.WordTrace tailWord_1585027 prefixEnd_1585027 120574918719122267892311 := by
  unfold tailWord_1585027
  simp only [CollatzResearch.WordTrace]
  refine ⟨57810684028725354905097335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38540456019150236603398223 57810684028725354905097335)
  ·
    refine ⟨86716026043088032357646003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57810684028725354905097335 86716026043088032357646003)
    ·
      refine ⟨130074039064632048536469005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86716026043088032357646003 130074039064632048536469005)
      ·
        refine ⟨48777764649237018201175877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130074039064632048536469005 48777764649237018201175877)
        ·
          refine ⟨9145830871731940912720477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48777764649237018201175877 9145830871731940912720477)
          ·
            refine ⟨3429686576899477842270179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9145830871731940912720477 3429686576899477842270179)
            ·
              refine ⟨5144529865349216763405269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429686576899477842270179 5144529865349216763405269)
              ·
                refine ⟨120574918719122267892311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5144529865349216763405269 120574918719122267892311)
                ·
                  rfl

theorem cell21_1585027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 7].length) (baseStart_1585027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585027 prefixEnd_1585027 := by exact prefixLift 1585027
  have htrace : WordTrace (prefixWord ++ tailWord_1585027) baseStart_1585027 baseEnd_1585027 := by
    simpa [prefixWord, tailWord_1585027, baseEnd_1585027] using wordTrace_append hprefix tailTrace_1585027
  have hstable : (prefixWord ++ tailWord_1585027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585027).length < 2 ^ (prefixWord ++ tailWord_1585027).sum := by decide
  have hdescent : baseEnd_1585027 < baseStart_1585027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585041 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 7]
def baseStart_1585041 : Nat := 118140960795 + 1585041 * 2 ^ 59
def prefixEnd_1585041 : Nat := 4983230072969 + 3 ^ 40 * 1585041 * 2
def baseEnd_1585041 : Nat := 361727951148105890443571

theorem tailTrace_1585041 : CollatzResearch.WordTrace tailWord_1585041 prefixEnd_1585041 361727951148105890443571 := by
  unfold tailWord_1585041
  simp only [CollatzResearch.WordTrace]
  refine ⟨57811194650674635296106977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38540796433783090197404651 57811194650674635296106977)
  ·
    refine ⟨43358395988005976472080233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57811194650674635296106977 43358395988005976472080233)
    ·
      refine ⟨32518796991004482354060175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43358395988005976472080233 32518796991004482354060175)
      ·
        refine ⟨48778195486506723531090263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32518796991004482354060175 48778195486506723531090263)
        ·
          refine ⟨73167293229760085296635395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48778195486506723531090263 73167293229760085296635395)
          ·
            refine ⟨109750939844640127944953093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73167293229760085296635395 109750939844640127944953093)
            ·
              refine ⟨20578301220870023989678705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109750939844640127944953093 20578301220870023989678705)
              ·
                refine ⟨15433725915652517992259029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20578301220870023989678705 15433725915652517992259029)
                ·
                  refine ⟨361727951148105890443571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15433725915652517992259029 361727951148105890443571)
                  ·
                    rfl

theorem cell21_1585041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_1585041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585041 prefixEnd_1585041 := by exact prefixLift 1585041
  have htrace : WordTrace (prefixWord ++ tailWord_1585041) baseStart_1585041 baseEnd_1585041 := by
    simpa [prefixWord, tailWord_1585041, baseEnd_1585041] using wordTrace_append hprefix tailTrace_1585041
  have hstable : (prefixWord ++ tailWord_1585041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585041).length < 2 ^ (prefixWord ++ tailWord_1585041).sum := by decide
  have hdescent : baseEnd_1585041 < baseStart_1585041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585044 : List Nat := [2, 4, 2, 1, 1, 4, 7]
def baseStart_1585044 : Nat := 118140960795 + 1585044 * 2 ^ 59
def prefixEnd_1585044 : Nat := 4983230072969 + 3 ^ 40 * 1585044 * 2
def baseEnd_1585044 : Nat := 40192070643219839099285

theorem tailTrace_1585044 : CollatzResearch.WordTrace tailWord_1585044 prefixEnd_1585044 40192070643219839099285 := by
  unfold tailWord_1585044
  simp only [CollatzResearch.WordTrace]
  refine ⟨28905652034831883404233093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38540869379775844538977457 28905652034831883404233093)
  ·
    refine ⟨5419809756530978138293705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28905652034831883404233093 5419809756530978138293705)
    ·
      refine ⟨4064857317398233603720279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5419809756530978138293705 4064857317398233603720279)
      ·
        refine ⟨6097285976097350405580419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064857317398233603720279 6097285976097350405580419)
        ·
          refine ⟨9145928964146025608370629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6097285976097350405580419 9145928964146025608370629)
          ·
            refine ⟨1714861680777379801569493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9145928964146025608370629 1714861680777379801569493)
            ·
              refine ⟨40192070643219839099285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1714861680777379801569493 40192070643219839099285)
              ·
                rfl

theorem cell21_1585044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 7].length) (baseStart_1585044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585044 prefixEnd_1585044 := by exact prefixLift 1585044
  have htrace : WordTrace (prefixWord ++ tailWord_1585044) baseStart_1585044 baseEnd_1585044 := by
    simpa [prefixWord, tailWord_1585044, baseEnd_1585044] using wordTrace_append hprefix tailTrace_1585044
  have hstable : (prefixWord ++ tailWord_1585044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585044).length < 2 ^ (prefixWord ++ tailWord_1585044).sum := by decide
  have hdescent : baseEnd_1585044 < baseStart_1585044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585109 : List Nat := [1, 3, 2, 3, 2, 3, 2, 2, 3]
def baseStart_1585109 : Nat := 118140960795 + 1585109 * 2 ^ 59
def prefixEnd_1585109 : Nat := 4983230072969 + 3 ^ 40 * 1585109 * 2
def baseEnd_1585109 : Nat := 361743469674552883310099

theorem tailTrace_1585109 : CollatzResearch.WordTrace tailWord_1585109 prefixEnd_1585109 361743469674552883310099 := by
  unfold tailWord_1585109
  simp only [CollatzResearch.WordTrace]
  refine ⟨57813674814428282909582381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38542449876285521939721587 57813674814428282909582381)
  ·
    refine ⟨21680128055410606091093393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57813674814428282909582381 21680128055410606091093393)
    ·
      refine ⟨16260096041557954568320045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21680128055410606091093393 16260096041557954568320045)
      ·
        refine ⟨6097536015584232963120017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16260096041557954568320045 6097536015584232963120017)
        ·
          refine ⟨4573152011688174722340013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6097536015584232963120017 4573152011688174722340013)
          ·
            refine ⟨1714932004383065520877505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4573152011688174722340013 1714932004383065520877505)
            ·
              refine ⟨1286199003287299140658129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714932004383065520877505 1286199003287299140658129)
              ·
                refine ⟨964649252465474355493597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286199003287299140658129 964649252465474355493597)
                ·
                  refine ⟨361743469674552883310099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964649252465474355493597 361743469674552883310099)
                  ·
                    rfl

theorem cell21_1585109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_1585109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585109 prefixEnd_1585109 := by exact prefixLift 1585109
  have htrace : WordTrace (prefixWord ++ tailWord_1585109) baseStart_1585109 baseEnd_1585109 := by
    simpa [prefixWord, tailWord_1585109, baseEnd_1585109] using wordTrace_append hprefix tailTrace_1585109
  have hstable : (prefixWord ++ tailWord_1585109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585109).length < 2 ^ (prefixWord ++ tailWord_1585109).sum := by decide
  have hdescent : baseEnd_1585109 < baseStart_1585109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585134 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1585134 : Nat := 118140960795 + 1585134 * 2 ^ 59
def prefixEnd_1585134 : Nat := 4983230072969 + 3 ^ 40 * 1585134 * 2
def baseEnd_1585134 : Nat := 361749175015158395393381

theorem tailTrace_1585134 : CollatzResearch.WordTrace tailWord_1585134 prefixEnd_1585134 361749175015158395393381 := by
  unfold tailWord_1585134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226823329917214022405307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38543057759558474786161637 7226823329917214022405307)
  ·
    refine ⟨10840234994875821033607961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7226823329917214022405307 10840234994875821033607961)
    ·
      refine ⟨8130176246156865775205971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10840234994875821033607961 8130176246156865775205971)
      ·
        refine ⟨12195264369235298662808957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130176246156865775205971 12195264369235298662808957)
        ·
          refine ⟨4573224138463236998553359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12195264369235298662808957 4573224138463236998553359)
          ·
            refine ⟨6859836207694855497830039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573224138463236998553359 6859836207694855497830039)
            ·
              refine ⟨10289754311542283246745059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859836207694855497830039 10289754311542283246745059)
              ·
                refine ⟨15434631467313424870117589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10289754311542283246745059 15434631467313424870117589)
                ·
                  refine ⟨361749175015158395393381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15434631467313424870117589 361749175015158395393381)
                  ·
                    rfl

theorem cell21_1585134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1585134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585134 prefixEnd_1585134 := by exact prefixLift 1585134
  have htrace : WordTrace (prefixWord ++ tailWord_1585134) baseStart_1585134 baseEnd_1585134 := by
    simpa [prefixWord, tailWord_1585134, baseEnd_1585134] using wordTrace_append hprefix tailTrace_1585134
  have hstable : (prefixWord ++ tailWord_1585134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585134).length < 2 ^ (prefixWord ++ tailWord_1585134).sum := by decide
  have hdescent : baseEnd_1585134 < baseStart_1585134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585148 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_1585148 : Nat := 118140960795 + 1585148 * 2 ^ 59
def prefixEnd_1585148 : Nat := 4983230072969 + 3 ^ 40 * 1585148 * 2
def baseEnd_1585148 : Nat := 361752370005897482160019

theorem tailTrace_1585148 : CollatzResearch.WordTrace tailWord_1585148 prefixEnd_1585148 361752370005897482160019 := by
  unfold tailWord_1585148
  simp only [CollatzResearch.WordTrace]
  refine ⟨28907548630643496285126049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38543398174191328380168065 28907548630643496285126049)
  ·
    refine ⟨21680661472982622213844537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28907548630643496285126049 21680661472982622213844537)
    ·
      refine ⟨16260496104736966660383403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21680661472982622213844537 16260496104736966660383403)
      ·
        refine ⟨24390744157105449990575105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16260496104736966660383403 24390744157105449990575105)
        ·
          refine ⟨18293058117829087492931329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24390744157105449990575105 18293058117829087492931329)
          ·
            refine ⟨13719793588371815619698497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18293058117829087492931329 13719793588371815619698497)
            ·
              refine ⟨10289845191278861714773873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13719793588371815619698497 10289845191278861714773873)
              ·
                refine ⟨7717383893459146286080405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10289845191278861714773873 7717383893459146286080405)
                ·
                  refine ⟨361752370005897482160019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7717383893459146286080405 361752370005897482160019)
                  ·
                    rfl

theorem cell21_1585148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_1585148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585148 prefixEnd_1585148 := by exact prefixLift 1585148
  have htrace : WordTrace (prefixWord ++ tailWord_1585148) baseStart_1585148 baseEnd_1585148 := by
    simpa [prefixWord, tailWord_1585148, baseEnd_1585148] using wordTrace_append hprefix tailTrace_1585148
  have hstable : (prefixWord ++ tailWord_1585148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585148).length < 2 ^ (prefixWord ++ tailWord_1585148).sum := by decide
  have hdescent : baseEnd_1585148 < baseStart_1585148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585362 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1585362 : Nat := 118140960795 + 1585362 * 2 ^ 59
def prefixEnd_1585362 : Nat := 4983230072969 + 3 ^ 40 * 1585362 * 2
def baseEnd_1585362 : Nat := 361801207721480665592915

theorem tailTrace_1585362 : CollatzResearch.WordTrace tailWord_1585362 prefixEnd_1585362 361801207721480665592915 := by
  unfold tailWord_1585362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455725620627926779635585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38548601655007804745694893 14455725620627926779635585)
  ·
    refine ⟨10841794215470945084726689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14455725620627926779635585 10841794215470945084726689)
    ·
      refine ⟨8131345661603208813545017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10841794215470945084726689 8131345661603208813545017)
      ·
        refine ⟨6098509246202406610158763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8131345661603208813545017 6098509246202406610158763)
        ·
          refine ⟨9147763869303609915238145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6098509246202406610158763 9147763869303609915238145)
          ·
            refine ⟨6860822901977707436428609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9147763869303609915238145 6860822901977707436428609)
            ·
              refine ⟨5145617176483280577321457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6860822901977707436428609 5145617176483280577321457)
              ·
                refine ⟨3859212882362460432991093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5145617176483280577321457 3859212882362460432991093)
                ·
                  refine ⟨361801207721480665592915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3859212882362460432991093 361801207721480665592915)
                  ·
                    rfl

theorem cell21_1585362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1585362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585362 prefixEnd_1585362 := by exact prefixLift 1585362
  have htrace : WordTrace (prefixWord ++ tailWord_1585362) baseStart_1585362 baseEnd_1585362 := by
    simpa [prefixWord, tailWord_1585362, baseEnd_1585362] using wordTrace_append hprefix tailTrace_1585362
  have hstable : (prefixWord ++ tailWord_1585362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585362).length < 2 ^ (prefixWord ++ tailWord_1585362).sum := by decide
  have hdescent : baseEnd_1585362 < baseStart_1585362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585365 : List Nat := [1, 3, 2, 4, 2, 2, 2, 5]
def baseStart_1585365 : Nat := 118140960795 + 1585365 * 2 ^ 59
def prefixEnd_1585365 : Nat := 4983230072969 + 3 ^ 40 * 1585365 * 2
def baseEnd_1585365 : Nat := 120600630787451109014303

theorem tailTrace_1585365 : CollatzResearch.WordTrace tailWord_1585365 prefixEnd_1585365 120600630787451109014303 := by
  unfold tailWord_1585365
  simp only [CollatzResearch.WordTrace]
  refine ⟨57823011901500838630901549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38548674601000559087267699 57823011901500838630901549)
  ·
    refine ⟨21683629463062814486588081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57823011901500838630901549 21683629463062814486588081)
    ·
      refine ⟨16262722097297110864941061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21683629463062814486588081 16262722097297110864941061)
      ·
        refine ⟨3049260393243208287176449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16262722097297110864941061 3049260393243208287176449)
        ·
          refine ⟨2286945294932406215382337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3049260393243208287176449 2286945294932406215382337)
          ·
            refine ⟨1715208971199304661536753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2286945294932406215382337 1715208971199304661536753)
            ·
              refine ⟨1286406728399478496152565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715208971199304661536753 1286406728399478496152565)
              ·
                refine ⟨120600630787451109014303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1286406728399478496152565 120600630787451109014303)
                ·
                  rfl

theorem cell21_1585365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 5].length) (baseStart_1585365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585365 prefixEnd_1585365 := by exact prefixLift 1585365
  have htrace : WordTrace (prefixWord ++ tailWord_1585365) baseStart_1585365 baseEnd_1585365 := by
    simpa [prefixWord, tailWord_1585365, baseEnd_1585365] using wordTrace_append hprefix tailTrace_1585365
  have hstable : (prefixWord ++ tailWord_1585365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585365).length < 2 ^ (prefixWord ++ tailWord_1585365).sum := by decide
  have hdescent : baseEnd_1585365 < baseStart_1585365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585410 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1585410 : Nat := 118140960795 + 1585410 * 2 ^ 59
def prefixEnd_1585410 : Nat := 4983230072969 + 3 ^ 40 * 1585410 * 2
def baseEnd_1585410 : Nat := 361812161975443248792817

theorem tailTrace_1585410 : CollatzResearch.WordTrace tailWord_1585410 prefixEnd_1585410 361812161975443248792817 := by
  unfold tailWord_1585410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14456163296584452829072421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38549768790891874210859789 14456163296584452829072421)
  ·
    refine ⟨2710530618109584905451079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14456163296584452829072421 2710530618109584905451079)
    ·
      refine ⟨4065795927164377358176619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710530618109584905451079 4065795927164377358176619)
      ·
        refine ⟨6098693890746566037264929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065795927164377358176619 6098693890746566037264929)
        ·
          refine ⟨4574020418059924527948697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6098693890746566037264929 4574020418059924527948697)
          ·
            refine ⟨3430515313544943395961523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4574020418059924527948697 3430515313544943395961523)
            ·
              refine ⟨5145772970317415093942285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3430515313544943395961523 5145772970317415093942285)
              ·
                refine ⟨1929664863869030660228357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5145772970317415093942285 1929664863869030660228357)
                ·
                  refine ⟨361812161975443248792817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1929664863869030660228357 361812161975443248792817)
                  ·
                    rfl

theorem cell21_1585410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1585410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585410 prefixEnd_1585410 := by exact prefixLift 1585410
  have htrace : WordTrace (prefixWord ++ tailWord_1585410) baseStart_1585410 baseEnd_1585410 := by
    simpa [prefixWord, tailWord_1585410, baseEnd_1585410] using wordTrace_append hprefix tailTrace_1585410
  have hstable : (prefixWord ++ tailWord_1585410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585410).length < 2 ^ (prefixWord ++ tailWord_1585410).sum := by decide
  have hdescent : baseEnd_1585410 < baseStart_1585410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585435 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 8]
def baseStart_1585435 : Nat := 118140960795 + 1585435 * 2 ^ 59
def prefixEnd_1585435 : Nat := 4983230072969 + 3 ^ 40 * 1585435 * 2
def baseEnd_1585435 : Nat := 361817867316048760876099

theorem tailTrace_1585435 : CollatzResearch.WordTrace tailWord_1585435 prefixEnd_1585435 361817867316048760876099 := by
  unfold tailWord_1585435
  simp only [CollatzResearch.WordTrace]
  refine ⟨57825565011247240585949759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38550376674164827057299839 57825565011247240585949759)
  ·
    refine ⟨86738347516870860878924639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57825565011247240585949759 86738347516870860878924639)
    ·
      refine ⟨130107521275306291318386959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86738347516870860878924639 130107521275306291318386959)
      ·
        refine ⟨195161281912959436977580439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130107521275306291318386959 195161281912959436977580439)
        ·
          refine ⟨292741922869439155466370659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195161281912959436977580439 292741922869439155466370659)
          ·
            refine ⟨439112884304158733199555989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292741922869439155466370659 439112884304158733199555989)
            ·
              refine ⟨20583416451757440618729187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 439112884304158733199555989 20583416451757440618729187)
              ·
                refine ⟨30875124677636160928093781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20583416451757440618729187 30875124677636160928093781)
                ·
                  refine ⟨361817867316048760876099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30875124677636160928093781 361817867316048760876099)
                  ·
                    rfl

theorem cell21_1585435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_1585435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585435 prefixEnd_1585435 := by exact prefixLift 1585435
  have htrace : WordTrace (prefixWord ++ tailWord_1585435) baseStart_1585435 baseEnd_1585435 := by
    simpa [prefixWord, tailWord_1585435, baseEnd_1585435] using wordTrace_append hprefix tailTrace_1585435
  have hstable : (prefixWord ++ tailWord_1585435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585435).length < 2 ^ (prefixWord ++ tailWord_1585435).sum := by decide
  have hdescent : baseEnd_1585435 < baseStart_1585435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585447 : List Nat := [1, 1, 8, 1, 1, 2, 2, 2, 3]
def baseStart_1585447 : Nat := 118140960795 + 1585447 * 2 ^ 59
def prefixEnd_1585447 : Nat := 4983230072969 + 3 ^ 40 * 1585447 * 2
def baseEnd_1585447 : Nat := 361820605879539406676075

theorem tailTrace_1585447 : CollatzResearch.WordTrace tailWord_1585447 prefixEnd_1585447 361820605879539406676075 := by
  unfold tailWord_1585447
  simp only [CollatzResearch.WordTrace]
  refine ⟨57826002687203766635386595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38550668458135844423591063 57826002687203766635386595)
  ·
    refine ⟨86739004030805649953079893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57826002687203766635386595 86739004030805649953079893)
    ·
      refine ⟨1016472703486003710387655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 86739004030805649953079893 1016472703486003710387655)
      ·
        refine ⟨1524709055229005565581483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016472703486003710387655 1524709055229005565581483)
        ·
          refine ⟨2287063582843508348372225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524709055229005565581483 2287063582843508348372225)
          ·
            refine ⟨1715297687132631261279169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2287063582843508348372225 1715297687132631261279169)
            ·
              refine ⟨1286473265349473445959377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715297687132631261279169 1286473265349473445959377)
              ·
                refine ⟨964854949012105084469533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286473265349473445959377 964854949012105084469533)
                ·
                  refine ⟨361820605879539406676075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964854949012105084469533 361820605879539406676075)
                  ·
                    rfl

theorem cell21_1585447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 3].length) (baseStart_1585447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585447 prefixEnd_1585447 := by exact prefixLift 1585447
  have htrace : WordTrace (prefixWord ++ tailWord_1585447) baseStart_1585447 baseEnd_1585447 := by
    simpa [prefixWord, tailWord_1585447, baseEnd_1585447] using wordTrace_append hprefix tailTrace_1585447
  have hstable : (prefixWord ++ tailWord_1585447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585447).length < 2 ^ (prefixWord ++ tailWord_1585447).sum := by decide
  have hdescent : baseEnd_1585447 < baseStart_1585447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585452 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_1585452 : Nat := 118140960795 + 1585452 * 2 ^ 59
def prefixEnd_1585452 : Nat := 4983230072969 + 3 ^ 40 * 1585452 * 2
def baseEnd_1585452 : Nat := 361821746947660509092731

theorem tailTrace_1585452 : CollatzResearch.WordTrace tailWord_1585452 prefixEnd_1585452 361821746947660509092731 := by
  unfold tailWord_1585452
  simp only [CollatzResearch.WordTrace]
  refine ⟨28913092526092826244659305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38550790034790434992879073 28913092526092826244659305)
  ·
    refine ⟨21684819394569619683494479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28913092526092826244659305 21684819394569619683494479)
    ·
      refine ⟨32527229091854429525241719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21684819394569619683494479 32527229091854429525241719)
      ·
        refine ⟨48790843637781644287862579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32527229091854429525241719 48790843637781644287862579)
        ·
          refine ⟨73186265456672466431793869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48790843637781644287862579 73186265456672466431793869)
          ·
            refine ⟨27444849546252174911922701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73186265456672466431793869 27444849546252174911922701)
            ·
              refine ⟨10291818579844565591971013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27444849546252174911922701 10291818579844565591971013)
              ·
                refine ⟨1929715983720856048494565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10291818579844565591971013 1929715983720856048494565)
                ·
                  refine ⟨361821746947660509092731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1929715983720856048494565 361821746947660509092731)
                  ·
                    rfl

theorem cell21_1585452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_1585452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585452 prefixEnd_1585452 := by exact prefixLift 1585452
  have htrace : WordTrace (prefixWord ++ tailWord_1585452) baseStart_1585452 baseEnd_1585452 := by
    simpa [prefixWord, tailWord_1585452, baseEnd_1585452] using wordTrace_append hprefix tailTrace_1585452
  have hstable : (prefixWord ++ tailWord_1585452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585452).length < 2 ^ (prefixWord ++ tailWord_1585452).sum := by decide
  have hdescent : baseEnd_1585452 < baseStart_1585452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585455 : List Nat := [1, 1, 2, 1, 2, 1, 8, 2, 3]
def baseStart_1585455 : Nat := 118140960795 + 1585455 * 2 ^ 59
def prefixEnd_1585455 : Nat := 4983230072969 + 3 ^ 40 * 1585455 * 2
def baseEnd_1585455 : Nat := 361822431588533170542725

theorem tailTrace_1585455 : CollatzResearch.WordTrace tailWord_1585455 prefixEnd_1585455 361822431588533170542725 := by
  unfold tailWord_1585455
  simp only [CollatzResearch.WordTrace]
  refine ⟨57826294471174784001677819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38550862980783189334451879 57826294471174784001677819)
  ·
    refine ⟨86739441706762176002516729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57826294471174784001677819 86739441706762176002516729)
    ·
      refine ⟨65054581280071632001887547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86739441706762176002516729 65054581280071632001887547)
      ·
        refine ⟨97581871920107448002831321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65054581280071632001887547 97581871920107448002831321)
        ·
          refine ⟨73186403940080586002123491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97581871920107448002831321 73186403940080586002123491)
          ·
            refine ⟨109779605910120879003185237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73186403940080586002123491 109779605910120879003185237)
            ·
              refine ⟨1286479756759229050818577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 109779605910120879003185237 1286479756759229050818577)
              ·
                refine ⟨964859817569421788113933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286479756759229050818577 964859817569421788113933)
                ·
                  refine ⟨361822431588533170542725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964859817569421788113933 361822431588533170542725)
                  ·
                    rfl

theorem cell21_1585455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 3].length) (baseStart_1585455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585455 prefixEnd_1585455 := by exact prefixLift 1585455
  have htrace : WordTrace (prefixWord ++ tailWord_1585455) baseStart_1585455 baseEnd_1585455 := by
    simpa [prefixWord, tailWord_1585455, baseEnd_1585455] using wordTrace_append hprefix tailTrace_1585455
  have hstable : (prefixWord ++ tailWord_1585455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585455).length < 2 ^ (prefixWord ++ tailWord_1585455).sum := by decide
  have hdescent : baseEnd_1585455 < baseStart_1585455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585500 : List Nat := [2, 2, 4, 3, 1, 1, 8]
def baseStart_1585500 : Nat := 118140960795 + 1585500 * 2 ^ 59
def prefixEnd_1585500 : Nat := 4983230072969 + 3 ^ 40 * 1585500 * 2
def baseEnd_1585500 : Nat := 40203633466847010254737

theorem tailTrace_1585500 : CollatzResearch.WordTrace tailWord_1585500 prefixEnd_1585500 40203633466847010254737 := by
  unfold tailWord_1585500
  simp only [CollatzResearch.WordTrace]
  refine ⟨28913967878005878343532977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38551957170674504458043969 28913967878005878343532977)
  ·
    refine ⟨21685475908504408757649733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28913967878005878343532977 21685475908504408757649733)
    ·
      refine ⟨4066026732844576642059325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21685475908504408757649733 4066026732844576642059325)
      ·
        refine ⟨1524760024816716240772247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4066026732844576642059325 1524760024816716240772247)
        ·
          refine ⟨2287140037225074361158371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524760024816716240772247 2287140037225074361158371)
          ·
            refine ⟨3430710055837611541737557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287140037225074361158371 3430710055837611541737557)
            ·
              refine ⟨40203633466847010254737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3430710055837611541737557 40203633466847010254737)
              ·
                rfl

theorem cell21_1585500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 8].length) (baseStart_1585500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585500 prefixEnd_1585500 := by exact prefixLift 1585500
  have htrace : WordTrace (prefixWord ++ tailWord_1585500) baseStart_1585500 baseEnd_1585500 := by
    simpa [prefixWord, tailWord_1585500, baseEnd_1585500] using wordTrace_append hprefix tailTrace_1585500
  have hstable : (prefixWord ++ tailWord_1585500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585500).length < 2 ^ (prefixWord ++ tailWord_1585500).sum := by decide
  have hdescent : baseEnd_1585500 < baseStart_1585500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585514 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_1585514 : Nat := 118140960795 + 1585514 * 2 ^ 59
def prefixEnd_1585514 : Nat := 4983230072969 + 3 ^ 40 * 1585514 * 2
def baseEnd_1585514 : Nat := 361835896192362179059271

theorem tailTrace_1585514 : CollatzResearch.WordTrace tailWord_1585514 prefixEnd_1585514 361835896192362179059271 := by
  unfold tailWord_1585514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14457111594490259269518899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38552297585307358052050397 14457111594490259269518899)
  ·
    refine ⟨21685667391735388904278349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14457111594490259269518899 21685667391735388904278349)
    ·
      refine ⟨8132125271900770839104381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21685667391735388904278349 8132125271900770839104381)
      ·
        refine ⟨3049546976962789064664143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8132125271900770839104381 3049546976962789064664143)
        ·
          refine ⟨4574320465444183596996215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049546976962789064664143 4574320465444183596996215)
          ·
            refine ⟨6861480698166275395494323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4574320465444183596996215 6861480698166275395494323)
            ·
              refine ⟨10292221047249413093241485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6861480698166275395494323 10292221047249413093241485)
              ·
                refine ⟨3859582892718529909965557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10292221047249413093241485 3859582892718529909965557)
                ·
                  refine ⟨361835896192362179059271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3859582892718529909965557 361835896192362179059271)
                  ·
                    rfl

theorem cell21_1585514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_1585514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585514 prefixEnd_1585514 := by exact prefixLift 1585514
  have htrace : WordTrace (prefixWord ++ tailWord_1585514) baseStart_1585514 baseEnd_1585514 := by
    simpa [prefixWord, tailWord_1585514, baseEnd_1585514] using wordTrace_append hprefix tailTrace_1585514
  have hstable : (prefixWord ++ tailWord_1585514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585514).length < 2 ^ (prefixWord ++ tailWord_1585514).sum := by decide
  have hdescent : baseEnd_1585514 < baseStart_1585514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585576 : List Nat := [2, 1, 6, 1, 1, 2, 2, 6]
def baseStart_1585576 : Nat := 118140960795 + 1585576 * 2 ^ 59
def prefixEnd_1585576 : Nat := 4983230072969 + 3 ^ 40 * 1585576 * 2
def baseEnd_1585576 : Nat := 120616681812354616341937

theorem tailTrace_1585576 : CollatzResearch.WordTrace tailWord_1585576 prefixEnd_1585576 120616681812354616341937 := by
  unfold tailWord_1585576
  simp only [CollatzResearch.WordTrace]
  refine ⟨28915353851868210833416291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38553805135824281111221721 28915353851868210833416291)
  ·
    refine ⟨43373030777802316250124437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28915353851868210833416291 43373030777802316250124437)
    ·
      refine ⟨2033110817709483574224583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43373030777802316250124437 2033110817709483574224583)
      ·
        refine ⟨3049666226564225361336875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033110817709483574224583 3049666226564225361336875)
        ·
          refine ⟨4574499339846338042005313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049666226564225361336875 4574499339846338042005313)
          ·
            refine ⟨3430874504884753531503985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4574499339846338042005313 3430874504884753531503985)
            ·
              refine ⟨2573155878663565148627989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3430874504884753531503985 2573155878663565148627989)
              ·
                refine ⟨120616681812354616341937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2573155878663565148627989 120616681812354616341937)
                ·
                  rfl

theorem cell21_1585576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_1585576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585576 prefixEnd_1585576 := by exact prefixLift 1585576
  have htrace : WordTrace (prefixWord ++ tailWord_1585576) baseStart_1585576 baseEnd_1585576 := by
    simpa [prefixWord, tailWord_1585576, baseEnd_1585576] using wordTrace_append hprefix tailTrace_1585576
  have hstable : (prefixWord ++ tailWord_1585576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585576).length < 2 ^ (prefixWord ++ tailWord_1585576).sum := by decide
  have hdescent : baseEnd_1585576 < baseStart_1585576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585621 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 4]
def baseStart_1585621 : Nat := 118140960795 + 1585621 * 2 ^ 59
def prefixEnd_1585621 : Nat := 4983230072969 + 3 ^ 40 * 1585621 * 2
def baseEnd_1585621 : Nat := 361860315050153770775719

theorem tailTrace_1585621 : CollatzResearch.WordTrace tailWord_1585621 prefixEnd_1585621 361860315050153770775719 := by
  unfold tailWord_1585621
  simp only [CollatzResearch.WordTrace]
  refine ⟨57832348988573394352220717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38554899325715596234813811 57832348988573394352220717)
  ·
    refine ⟨21687130870715022882082769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57832348988573394352220717 21687130870715022882082769)
    ·
      refine ⟨16265348153036267161562077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21687130870715022882082769 16265348153036267161562077)
      ·
        refine ⟨6099505557388600185585779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16265348153036267161562077 6099505557388600185585779)
        ·
          refine ⟨9149258336082900278378669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099505557388600185585779 9149258336082900278378669)
          ·
            refine ⟨3430971876031087604392001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9149258336082900278378669 3430971876031087604392001)
            ·
              refine ⟨2573228907023315703294001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3430971876031087604392001 2573228907023315703294001)
              ·
                refine ⟨1929921680267486777470501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573228907023315703294001 1929921680267486777470501)
                ·
                  refine ⟨361860315050153770775719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1929921680267486777470501 361860315050153770775719)
                  ·
                    rfl

theorem cell21_1585621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_1585621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585621 prefixEnd_1585621 := by exact prefixLift 1585621
  have htrace : WordTrace (prefixWord ++ tailWord_1585621) baseStart_1585621 baseEnd_1585621 := by
    simpa [prefixWord, tailWord_1585621, baseEnd_1585621] using wordTrace_append hprefix tailTrace_1585621
  have hstable : (prefixWord ++ tailWord_1585621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585621).length < 2 ^ (prefixWord ++ tailWord_1585621).sum := by decide
  have hdescent : baseEnd_1585621 < baseStart_1585621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585649 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 5]
def baseStart_1585649 : Nat := 118140960795 + 1585649 * 2 ^ 59
def prefixEnd_1585649 : Nat := 4983230072969 + 3 ^ 40 * 1585649 * 2
def baseEnd_1585649 : Nat := 361866705031631944308995

theorem tailTrace_1585649 : CollatzResearch.WordTrace tailWord_1585649 prefixEnd_1585649 361866705031631944308995 := by
  unfold tailWord_1585649
  simp only [CollatzResearch.WordTrace]
  refine ⟨57833370232471955134240001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38555580154981303422826667 57833370232471955134240001)
  ·
    refine ⟨43375027674353966350680001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57833370232471955134240001 43375027674353966350680001)
    ·
      refine ⟨32531270755765474763010001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43375027674353966350680001 32531270755765474763010001)
      ·
        refine ⟨24398453066824106072257501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32531270755765474763010001 24398453066824106072257501)
        ·
          refine ⟨9149419900059039777096563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24398453066824106072257501 9149419900059039777096563)
          ·
            refine ⟨13724129850088559665644845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149419900059039777096563 13724129850088559665644845)
            ·
              refine ⟨5146548693783209874616817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13724129850088559665644845 5146548693783209874616817)
              ·
                refine ⟨3859911520337407405962613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5146548693783209874616817 3859911520337407405962613)
                ·
                  refine ⟨361866705031631944308995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3859911520337407405962613 361866705031631944308995)
                  ·
                    rfl

theorem cell21_1585649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_1585649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585649 prefixEnd_1585649 := by exact prefixLift 1585649
  have htrace : WordTrace (prefixWord ++ tailWord_1585649) baseStart_1585649 baseEnd_1585649 := by
    simpa [prefixWord, tailWord_1585649, baseEnd_1585649] using wordTrace_append hprefix tailTrace_1585649
  have hstable : (prefixWord ++ tailWord_1585649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585649).length < 2 ^ (prefixWord ++ tailWord_1585649).sum := by decide
  have hdescent : baseEnd_1585649 < baseStart_1585649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585663 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 6]
def baseStart_1585663 : Nat := 118140960795 + 1585663 * 2 ^ 59
def prefixEnd_1585663 : Nat := 4983230072969 + 3 ^ 40 * 1585663 * 2
def baseEnd_1585663 : Nat := 361869900022371031075633

theorem tailTrace_1585663 : CollatzResearch.WordTrace tailWord_1585663 prefixEnd_1585663 361869900022371031075633 := by
  unfold tailWord_1585663
  simp only [CollatzResearch.WordTrace]
  refine ⟨57833880854421235525249643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38555920569614157016833095 57833880854421235525249643)
  ·
    refine ⟨86750821281631853287874465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57833880854421235525249643 86750821281631853287874465)
    ·
      refine ⟨65063115961223889965905849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86750821281631853287874465 65063115961223889965905849)
      ·
        refine ⟨48797336970917917474429387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65063115961223889965905849 48797336970917917474429387)
        ·
          refine ⟨73196005456376876211644081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48797336970917917474429387 73196005456376876211644081)
          ·
            refine ⟨54897004092282657158733061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73196005456376876211644081 54897004092282657158733061)
            ·
              refine ⟨10293188267302998217262449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54897004092282657158733061 10293188267302998217262449)
              ·
                refine ⟨7719891200477248662946837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10293188267302998217262449 7719891200477248662946837)
                ·
                  refine ⟨361869900022371031075633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7719891200477248662946837 361869900022371031075633)
                  ·
                    rfl

theorem cell21_1585663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_1585663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585663 prefixEnd_1585663 := by exact prefixLift 1585663
  have htrace : WordTrace (prefixWord ++ tailWord_1585663) baseStart_1585663 baseEnd_1585663 := by
    simpa [prefixWord, tailWord_1585663, baseEnd_1585663] using wordTrace_append hprefix tailTrace_1585663
  have hstable : (prefixWord ++ tailWord_1585663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585663).length < 2 ^ (prefixWord ++ tailWord_1585663).sum := by decide
  have hdescent : baseEnd_1585663 < baseStart_1585663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585697 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 4]
def baseStart_1585697 : Nat := 118140960795 + 1585697 * 2 ^ 59
def prefixEnd_1585697 : Nat := 4983230072969 + 3 ^ 40 * 1585697 * 2
def baseEnd_1585697 : Nat := 361877659285594527508897

theorem tailTrace_1585697 : CollatzResearch.WordTrace tailWord_1585697 prefixEnd_1585697 361877659285594527508897 := by
  unfold tailWord_1585697
  simp only [CollatzResearch.WordTrace]
  refine ⟨57835120936298059331987345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38556747290865372887991563 57835120936298059331987345)
  ·
    refine ⟨43376340702223544498990509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57835120936298059331987345 43376340702223544498990509)
    ·
      refine ⟨16266127763333829187121441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43376340702223544498990509 16266127763333829187121441)
      ·
        refine ⟨12199595822500371890341081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16266127763333829187121441 12199595822500371890341081)
        ·
          refine ⟨9149696866875278917755811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12199595822500371890341081 9149696866875278917755811)
          ·
            refine ⟨13724545300312918376633717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149696866875278917755811 13724545300312918376633717)
            ·
              refine ⟨1286676121904336097809411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13724545300312918376633717 1286676121904336097809411)
              ·
                refine ⟨1930014182856504146714117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286676121904336097809411 1930014182856504146714117)
                ·
                  refine ⟨361877659285594527508897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930014182856504146714117 361877659285594527508897)
                  ·
                    rfl

theorem cell21_1585697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_1585697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585697 prefixEnd_1585697 := by exact prefixLift 1585697
  have htrace : WordTrace (prefixWord ++ tailWord_1585697) baseStart_1585697 baseEnd_1585697 := by
    simpa [prefixWord, tailWord_1585697, baseEnd_1585697] using wordTrace_append hprefix tailTrace_1585697
  have hstable : (prefixWord ++ tailWord_1585697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585697).length < 2 ^ (prefixWord ++ tailWord_1585697).sum := by decide
  have hdescent : baseEnd_1585697 < baseStart_1585697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585739 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 6]
def baseStart_1585739 : Nat := 118140960795 + 1585739 * 2 ^ 59
def prefixEnd_1585739 : Nat := 4983230072969 + 3 ^ 40 * 1585739 * 2
def baseEnd_1585739 : Nat := 361887244257811787808811

theorem tailTrace_1585739 : CollatzResearch.WordTrace tailWord_1585739 prefixEnd_1585739 361887244257811787808811 := by
  unfold tailWord_1585739
  simp only [CollatzResearch.WordTrace]
  refine ⟨57836652802145900505016271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38557768534763933670010847 57836652802145900505016271)
  ·
    refine ⟨86754979203218850757524407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57836652802145900505016271 86754979203218850757524407)
    ·
      refine ⟨130132468804828276136286611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86754979203218850757524407 130132468804828276136286611)
      ·
        refine ⟨195198703207242414204429917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130132468804828276136286611 195198703207242414204429917)
        ·
          refine ⟨73199513702715905326661219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195198703207242414204429917 73199513702715905326661219)
          ·
            refine ⟨109799270554073857989991829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73199513702715905326661219 109799270554073857989991829)
            ·
              refine ⟨5146840807222212093280867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109799270554073857989991829 5146840807222212093280867)
              ·
                refine ⟨7720261210833318139921301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5146840807222212093280867 7720261210833318139921301)
                ·
                  refine ⟨361887244257811787808811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7720261210833318139921301 361887244257811787808811)
                  ·
                    rfl

theorem cell21_1585739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_1585739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585739 prefixEnd_1585739 := by exact prefixLift 1585739
  have htrace : WordTrace (prefixWord ++ tailWord_1585739) baseStart_1585739 baseEnd_1585739 := by
    simpa [prefixWord, tailWord_1585739, baseEnd_1585739] using wordTrace_append hprefix tailTrace_1585739
  have hstable : (prefixWord ++ tailWord_1585739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585739).length < 2 ^ (prefixWord ++ tailWord_1585739).sum := by decide
  have hdescent : baseEnd_1585739 < baseStart_1585739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585742 : List Nat := [4, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_1585742 : Nat := 118140960795 + 1585742 * 2 ^ 59
def prefixEnd_1585742 : Nat := 4983230072969 + 3 ^ 40 * 1585742 * 2
def baseEnd_1585742 : Nat := 361887928898684449258805

theorem tailTrace_1585742 : CollatzResearch.WordTrace tailWord_1585742 prefixEnd_1585742 361887928898684449258805 := by
  unfold tailWord_1585742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7229595277641879002171935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38557841480756688011583653 7229595277641879002171935)
  ·
    refine ⟨10844392916462818503257903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7229595277641879002171935 10844392916462818503257903)
    ·
      refine ⟨16266589374694227754886855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10844392916462818503257903 16266589374694227754886855)
      ·
        refine ⟨24399884062041341632330283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16266589374694227754886855 24399884062041341632330283)
        ·
          refine ⟨36599826093062012448495425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24399884062041341632330283 36599826093062012448495425)
          ·
            refine ⟨27449869569796509336371569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36599826093062012448495425 27449869569796509336371569)
            ·
              refine ⟨20587402177347382002278677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27449869569796509336371569 20587402177347382002278677)
              ·
                refine ⟨965034477063158531356813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20587402177347382002278677 965034477063158531356813)
                ·
                  refine ⟨361887928898684449258805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965034477063158531356813 361887928898684449258805)
                  ·
                    rfl

theorem cell21_1585742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_1585742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585742 prefixEnd_1585742 := by exact prefixLift 1585742
  have htrace : WordTrace (prefixWord ++ tailWord_1585742) baseStart_1585742 baseEnd_1585742 := by
    simpa [prefixWord, tailWord_1585742, baseEnd_1585742] using wordTrace_append hprefix tailTrace_1585742
  have hstable : (prefixWord ++ tailWord_1585742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585742).length < 2 ^ (prefixWord ++ tailWord_1585742).sum := by decide
  have hdescent : baseEnd_1585742 < baseStart_1585742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585770 : List Nat := [3, 1, 3, 2, 1, 1, 1, 9]
def baseStart_1585770 : Nat := 118140960795 + 1585770 * 2 ^ 59
def prefixEnd_1585770 : Nat := 4983230072969 + 3 ^ 40 * 1585770 * 2
def baseEnd_1585770 : Nat := 120631439626720874264027

theorem tailTrace_1585770 : CollatzResearch.WordTrace tailWord_1585770 prefixEnd_1585770 120631439626720874264027 := by
  unfold tailWord_1585770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14459445866258398199848691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38558522310022395199596509 14459445866258398199848691)
  ·
    refine ⟨21689168799387597299773037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14459445866258398199848691 21689168799387597299773037)
    ·
      refine ⟨8133438299770348987414889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21689168799387597299773037 8133438299770348987414889)
      ·
        refine ⟨6100078724827761740561167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8133438299770348987414889 6100078724827761740561167)
        ·
          refine ⟨9150118087241642610841751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6100078724827761740561167 9150118087241642610841751)
          ·
            refine ⟨13725177130862463916262627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9150118087241642610841751 13725177130862463916262627)
            ·
              refine ⟨20587765696293695874393941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13725177130862463916262627 20587765696293695874393941)
              ·
                refine ⟨120631439626720874264027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20587765696293695874393941 120631439626720874264027)
                ·
                  rfl

theorem cell21_1585770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_1585770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585770 prefixEnd_1585770 := by exact prefixLift 1585770
  have htrace : WordTrace (prefixWord ++ tailWord_1585770) baseStart_1585770 baseEnd_1585770 := by
    simpa [prefixWord, tailWord_1585770, baseEnd_1585770] using wordTrace_append hprefix tailTrace_1585770
  have hstable : (prefixWord ++ tailWord_1585770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585770).length < 2 ^ (prefixWord ++ tailWord_1585770).sum := by decide
  have hdescent : baseEnd_1585770 < baseStart_1585770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585784 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_1585784 : Nat := 118140960795 + 1585784 * 2 ^ 59
def prefixEnd_1585784 : Nat := 4983230072969 + 3 ^ 40 * 1585784 * 2
def baseEnd_1585784 : Nat := 361897513870901709558719

theorem tailTrace_1585784 : CollatzResearch.WordTrace tailWord_1585784 prefixEnd_1585784 361897513870901709558719 := by
  unfold tailWord_1585784
  simp only [CollatzResearch.WordTrace]
  refine ⟨28919147043491436595202203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38558862724655248793602937 28919147043491436595202203)
  ·
    refine ⟨43378720565237154892803305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28919147043491436595202203 43378720565237154892803305)
    ·
      refine ⟨32534040423927866169602479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43378720565237154892803305 32534040423927866169602479)
      ·
        refine ⟨48801060635891799254403719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32534040423927866169602479 48801060635891799254403719)
        ·
          refine ⟨73201590953837698881605579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48801060635891799254403719 73201590953837698881605579)
          ·
            refine ⟨109802386430756548322408369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73201590953837698881605579 109802386430756548322408369)
            ·
              refine ⟨82351789823067411241806277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109802386430756548322408369 82351789823067411241806277)
              ·
                refine ⟨15440960591825139607838677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82351789823067411241806277 15440960591825139607838677)
                ·
                  refine ⟨361897513870901709558719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15440960591825139607838677 361897513870901709558719)
                  ·
                    rfl

theorem cell21_1585784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_1585784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585784 prefixEnd_1585784 := by exact prefixLift 1585784
  have htrace : WordTrace (prefixWord ++ tailWord_1585784) baseStart_1585784 baseEnd_1585784 := by
    simpa [prefixWord, tailWord_1585784, baseEnd_1585784] using wordTrace_append hprefix tailTrace_1585784
  have hstable : (prefixWord ++ tailWord_1585784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585784).length < 2 ^ (prefixWord ++ tailWord_1585784).sum := by decide
  have hdescent : baseEnd_1585784 < baseStart_1585784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585962 : List Nat := [3, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_1585962 : Nat := 118140960795 + 1585962 * 2 ^ 59
def prefixEnd_1585962 : Nat := 4983230072969 + 3 ^ 40 * 1585962 * 2
def baseEnd_1585962 : Nat := 361938135896012955591689

theorem tailTrace_1585962 : CollatzResearch.WordTrace tailWord_1585962 prefixEnd_1585962 361938135896012955591689 := by
  unfold tailWord_1585962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14461196570084502397596035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38563190853558673060256093 14461196570084502397596035)
  ·
    refine ⟨21691794855126753596394053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14461196570084502397596035 21691794855126753596394053)
    ·
      refine ⟨4067211535336266299323885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21691794855126753596394053 4067211535336266299323885)
      ·
        refine ⟨1525204325751099862246457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4067211535336266299323885 1525204325751099862246457)
        ·
          refine ⟨1143903244313324896684843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525204325751099862246457 1143903244313324896684843)
          ·
            refine ⟨1715854866469987345027265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143903244313324896684843 1715854866469987345027265)
            ·
              refine ⟨1286891149852490508770449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715854866469987345027265 1286891149852490508770449)
              ·
                refine ⟨965168362389367881577837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286891149852490508770449 965168362389367881577837)
                ·
                  refine ⟨361938135896012955591689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965168362389367881577837 361938135896012955591689)
                  ·
                    rfl

theorem cell21_1585962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_1585962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585962 prefixEnd_1585962 := by exact prefixLift 1585962
  have htrace : WordTrace (prefixWord ++ tailWord_1585962) baseStart_1585962 baseEnd_1585962 := by
    simpa [prefixWord, tailWord_1585962, baseEnd_1585962] using wordTrace_append hprefix tailTrace_1585962
  have hstable : (prefixWord ++ tailWord_1585962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585962).length < 2 ^ (prefixWord ++ tailWord_1585962).sum := by decide
  have hdescent : baseEnd_1585962 < baseStart_1585962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585970 : List Nat := [3, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_1585970 : Nat := 118140960795 + 1585970 * 2 ^ 59
def prefixEnd_1585970 : Nat := 4983230072969 + 3 ^ 40 * 1585970 * 2
def baseEnd_1585970 : Nat := 361939961605006719458339

theorem tailTrace_1585970 : CollatzResearch.WordTrace tailWord_1585970 prefixEnd_1585970 361939961605006719458339 := by
  unfold tailWord_1585970
  simp only [CollatzResearch.WordTrace]
  refine ⟨14461269516077256739168841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38563385376206017971116909 14461269516077256739168841)
  ·
    refine ⟨10845952137057942554376631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14461269516077256739168841 10845952137057942554376631)
    ·
      refine ⟨16268928205586913831564947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10845952137057942554376631 16268928205586913831564947)
      ·
        refine ⟨24403392308380370747347421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16268928205586913831564947 24403392308380370747347421)
        ·
          refine ⟨9151272115642639030255283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24403392308380370747347421 9151272115642639030255283)
          ·
            refine ⟨13726908173463958545382925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9151272115642639030255283 13726908173463958545382925)
            ·
              refine ⟨5147590565048984454518597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13726908173463958545382925 5147590565048984454518597)
              ·
                refine ⟨965173230946684585222237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5147590565048984454518597 965173230946684585222237)
                ·
                  refine ⟨361939961605006719458339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965173230946684585222237 361939961605006719458339)
                  ·
                    rfl

theorem cell21_1585970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_1585970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1585970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1585970 prefixEnd_1585970 := by exact prefixLift 1585970
  have htrace : WordTrace (prefixWord ++ tailWord_1585970) baseStart_1585970 baseEnd_1585970 := by
    simpa [prefixWord, tailWord_1585970, baseEnd_1585970] using wordTrace_append hprefix tailTrace_1585970
  have hstable : (prefixWord ++ tailWord_1585970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585970).length < 2 ^ (prefixWord ++ tailWord_1585970).sum := by decide
  have hdescent : baseEnd_1585970 < baseStart_1585970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586018 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1586018 : Nat := 118140960795 + 1586018 * 2 ^ 59
def prefixEnd_1586018 : Nat := 4983230072969 + 3 ^ 40 * 1586018 * 2
def baseEnd_1586018 : Nat := 361950915858969302658241

theorem tailTrace_1586018 : CollatzResearch.WordTrace tailWord_1586018 prefixEnd_1586018 361950915858969302658241 := by
  unfold tailWord_1586018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14461707192033782788605677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38564552512090087436281805 14461707192033782788605677)
  ·
    refine ⟨5423140197012668545727129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14461707192033782788605677 5423140197012668545727129)
    ·
      refine ⟨4067355147759501409295347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5423140197012668545727129 4067355147759501409295347)
      ·
        refine ⟨6101032721639252113943021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067355147759501409295347 6101032721639252113943021)
        ·
          refine ⟨2287887270614719542728633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6101032721639252113943021 2287887270614719542728633)
          ·
            refine ⟨1715915452961039657046475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2287887270614719542728633 1715915452961039657046475)
            ·
              refine ⟨2573873179441559485569713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715915452961039657046475 2573873179441559485569713)
              ·
                refine ⟨1930404884581169614177285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573873179441559485569713 1930404884581169614177285)
                ·
                  refine ⟨361950915858969302658241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930404884581169614177285 361950915858969302658241)
                  ·
                    rfl

theorem cell21_1586018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1586018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586018 prefixEnd_1586018 := by exact prefixLift 1586018
  have htrace : WordTrace (prefixWord ++ tailWord_1586018) baseStart_1586018 baseEnd_1586018 := by
    simpa [prefixWord, tailWord_1586018, baseEnd_1586018] using wordTrace_append hprefix tailTrace_1586018
  have hstable : (prefixWord ++ tailWord_1586018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586018).length < 2 ^ (prefixWord ++ tailWord_1586018).sum := by decide
  have hdescent : baseEnd_1586018 < baseStart_1586018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586043 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 4]
def baseStart_1586043 : Nat := 118140960795 + 1586043 * 2 ^ 59
def prefixEnd_1586043 : Nat := 4983230072969 + 3 ^ 40 * 1586043 * 2
def baseEnd_1586043 : Nat := 361956621199574814741523

theorem tailTrace_1586043 : CollatzResearch.WordTrace tailWord_1586043 prefixEnd_1586043 361956621199574814741523 := by
  unfold tailWord_1586043
  simp only [CollatzResearch.WordTrace]
  refine ⟨57847740593044560424082783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38565160395363040282721855 57847740593044560424082783)
  ·
    refine ⟨86771610889566840636124175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57847740593044560424082783 86771610889566840636124175)
    ·
      refine ⟨130157416334350260954186263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86771610889566840636124175 130157416334350260954186263)
      ·
        refine ⟨195236124501525391431279395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130157416334350260954186263 195236124501525391431279395)
        ·
          refine ⟨292854186752288087146919093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195236124501525391431279395 292854186752288087146919093)
          ·
            refine ⟨27455080008027008170023665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292854186752288087146919093 27455080008027008170023665)
            ·
              refine ⟨20591310006020256127517749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27455080008027008170023665 20591310006020256127517749)
              ·
                refine ⟨1930435313064399011954789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20591310006020256127517749 1930435313064399011954789)
                ·
                  refine ⟨361956621199574814741523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930435313064399011954789 361956621199574814741523)
                  ·
                    rfl

theorem cell21_1586043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 4].length) (baseStart_1586043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586043 prefixEnd_1586043 := by exact prefixLift 1586043
  have htrace : WordTrace (prefixWord ++ tailWord_1586043) baseStart_1586043 baseEnd_1586043 := by
    simpa [prefixWord, tailWord_1586043, baseEnd_1586043] using wordTrace_append hprefix tailTrace_1586043
  have hstable : (prefixWord ++ tailWord_1586043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586043).length < 2 ^ (prefixWord ++ tailWord_1586043).sum := by decide
  have hdescent : baseEnd_1586043 < baseStart_1586043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586125 : List Nat := [1, 6, 3, 1, 2, 8]
def baseStart_1586125 : Nat := 118140960795 + 1586125 * 2 ^ 59
def prefixEnd_1586125 : Nat := 4983230072969 + 3 ^ 40 * 1586125 * 2
def baseEnd_1586125 : Nat := 13406493878398551643507

theorem tailTrace_1586125 : CollatzResearch.WordTrace tailWord_1586125 prefixEnd_1586125 13406493878398551643507 := by
  unfold tailWord_1586125
  simp only [CollatzResearch.WordTrace]
  refine ⟨57850731378747488428567829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38567154252498325619045219 57850731378747488428567829)
  ·
    refine ⟨2711753033378788520089117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57850731378747488428567829 2711753033378788520089117)
    ·
      refine ⟨1016907387517045695033419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2711753033378788520089117 1016907387517045695033419)
      ·
        refine ⟨1525361081275568542550129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016907387517045695033419 1525361081275568542550129)
        ·
          refine ⟨1144020810956676406912597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525361081275568542550129 1144020810956676406912597)
          ·
            refine ⟨13406493878398551643507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1144020810956676406912597 13406493878398551643507)
            ·
              rfl

theorem cell21_1586125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 8].length) (baseStart_1586125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586125 prefixEnd_1586125 := by exact prefixLift 1586125
  have htrace : WordTrace (prefixWord ++ tailWord_1586125) baseStart_1586125 baseEnd_1586125 := by
    simpa [prefixWord, tailWord_1586125, baseEnd_1586125] using wordTrace_append hprefix tailTrace_1586125
  have hstable : (prefixWord ++ tailWord_1586125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586125).length < 2 ^ (prefixWord ++ tailWord_1586125).sum := by decide
  have hdescent : baseEnd_1586125 < baseStart_1586125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586133 : List Nat := [1, 3, 2, 3, 12]
def baseStart_1586133 : Nat := 118140960795 + 1586133 * 2 ^ 59
def prefixEnd_1586133 : Nat := 4983230072969 + 3 ^ 40 * 1586133 * 2
def baseEnd_1586133 : Nat := 4468853832416724175819

theorem tailTrace_1586133 : CollatzResearch.WordTrace tailWord_1586133 prefixEnd_1586133 4468853832416724175819 := by
  unfold tailWord_1586133
  simp only [CollatzResearch.WordTrace]
  refine ⟨57851023162718505794859053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38567348775145670529906035 57851023162718505794859053)
  ·
    refine ⟨21694133686019439673072145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57851023162718505794859053 21694133686019439673072145)
    ·
      refine ⟨16270600264514579754804109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21694133686019439673072145 16270600264514579754804109)
      ·
        refine ⟨6101475099192967408051541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16270600264514579754804109 6101475099192967408051541)
        ·
          refine ⟨4468853832416724175819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6101475099192967408051541 4468853832416724175819)
          ·
            rfl

theorem cell21_1586133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 12].length) (baseStart_1586133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586133 prefixEnd_1586133 := by exact prefixLift 1586133
  have htrace : WordTrace (prefixWord ++ tailWord_1586133) baseStart_1586133 baseEnd_1586133 := by
    simpa [prefixWord, tailWord_1586133, baseEnd_1586133] using wordTrace_append hprefix tailTrace_1586133
  have hstable : (prefixWord ++ tailWord_1586133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586133).length < 2 ^ (prefixWord ++ tailWord_1586133).sum := by decide
  have hdescent : baseEnd_1586133 < baseStart_1586133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586136 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_1586136 : Nat := 118140960795 + 1586136 * 2 ^ 59
def prefixEnd_1586136 : Nat := 4983230072969 + 3 ^ 40 * 1586136 * 2
def baseEnd_1586136 : Nat := 361977845066627319691333

theorem tailTrace_1586136 : CollatzResearch.WordTrace tailWord_1586136 prefixEnd_1586136 361977845066627319691333 := by
  unfold tailWord_1586136
  simp only [CollatzResearch.WordTrace]
  refine ⟨28925566290853818653609131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38567421721138424871478841 28925566290853818653609131)
  ·
    refine ⟨43388349436280727980413697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28925566290853818653609131 43388349436280727980413697)
    ·
      refine ⟨32541262077210545985310273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43388349436280727980413697 32541262077210545985310273)
      ·
        refine ⟨24405946557907909488982705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32541262077210545985310273 24405946557907909488982705)
        ·
          refine ⟨18304459918430932116737029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24405946557907909488982705 18304459918430932116737029)
          ·
            refine ⟨3432086234705799771888193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18304459918430932116737029 3432086234705799771888193)
            ·
              refine ⟨2574064676029349828916145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3432086234705799771888193 2574064676029349828916145)
              ·
                refine ⟨1930548507022012371687109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2574064676029349828916145 1930548507022012371687109)
                ·
                  refine ⟨361977845066627319691333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930548507022012371687109 361977845066627319691333)
                  ·
                    rfl

theorem cell21_1586136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_1586136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586136 prefixEnd_1586136 := by exact prefixLift 1586136
  have htrace : WordTrace (prefixWord ++ tailWord_1586136) baseStart_1586136 baseEnd_1586136 := by
    simpa [prefixWord, tailWord_1586136, baseEnd_1586136] using wordTrace_append hprefix tailTrace_1586136
  have hstable : (prefixWord ++ tailWord_1586136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586136).length < 2 ^ (prefixWord ++ tailWord_1586136).sum := by decide
  have hdescent : baseEnd_1586136 < baseStart_1586136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586257 : List Nat := [1, 2, 2, 1, 3, 1, 2, 6, 3]
def baseStart_1586257 : Nat := 118140960795 + 1586257 * 2 ^ 59
def prefixEnd_1586257 : Nat := 4983230072969 + 3 ^ 40 * 1586257 * 2
def baseEnd_1586257 : Nat := 362005458915157998174419

theorem tailTrace_1586257 : CollatzResearch.WordTrace tailWord_1586257 prefixEnd_1586257 362005458915157998174419 := by
  unfold tailWord_1586257
  simp only [CollatzResearch.WordTrace]
  refine ⟨57855545814269274972373025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38570363876179516648248683 57855545814269274972373025)
  ·
    refine ⟨43391659360701956229279769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57855545814269274972373025 43391659360701956229279769)
    ·
      refine ⟨32543744520526467171959827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43391659360701956229279769 32543744520526467171959827)
      ·
        refine ⟨48815616780789700757939741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32543744520526467171959827 48815616780789700757939741)
        ·
          refine ⟨18305856292796137784227403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48815616780789700757939741 18305856292796137784227403)
          ·
            refine ⟨27458784439194206676341105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18305856292796137784227403 27458784439194206676341105)
            ·
              refine ⟨20594088329395655007255829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27458784439194206676341105 20594088329395655007255829)
              ·
                refine ⟨965347890440421328465117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20594088329395655007255829 965347890440421328465117)
                ·
                  refine ⟨362005458915157998174419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965347890440421328465117 362005458915157998174419)
                  ·
                    rfl

theorem cell21_1586257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_1586257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586257 prefixEnd_1586257 := by exact prefixLift 1586257
  have htrace : WordTrace (prefixWord ++ tailWord_1586257) baseStart_1586257 baseEnd_1586257 := by
    simpa [prefixWord, tailWord_1586257, baseEnd_1586257] using wordTrace_append hprefix tailTrace_1586257
  have hstable : (prefixWord ++ tailWord_1586257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586257).length < 2 ^ (prefixWord ++ tailWord_1586257).sum := by decide
  have hdescent : baseEnd_1586257 < baseStart_1586257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586271 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 4]
def baseStart_1586271 : Nat := 118140960795 + 1586271 * 2 ^ 59
def prefixEnd_1586271 : Nat := 4983230072969 + 3 ^ 40 * 1586271 * 2
def baseEnd_1586271 : Nat := 362008653905897084941057

theorem tailTrace_1586271 : CollatzResearch.WordTrace tailWord_1586271 prefixEnd_1586271 362008653905897084941057 := by
  unfold tailWord_1586271
  simp only [CollatzResearch.WordTrace]
  refine ⟨57856056436218555363382667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38570704290812370242255111 57856056436218555363382667)
  ·
    refine ⟨86784084654327833045074001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57856056436218555363382667 86784084654327833045074001)
    ·
      refine ⟨65088063490745874783805501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86784084654327833045074001 65088063490745874783805501)
      ·
        refine ⟨24408023809029703043927063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65088063490745874783805501 24408023809029703043927063)
        ·
          refine ⟨36612035713544554565890595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24408023809029703043927063 36612035713544554565890595)
          ·
            refine ⟨54918053570316831848835893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36612035713544554565890595 54918053570316831848835893)
            ·
              refine ⟨5148567522217202985828365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54918053570316831848835893 5148567522217202985828365)
              ·
                refine ⟨1930712820831451119685637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5148567522217202985828365 1930712820831451119685637)
                ·
                  refine ⟨362008653905897084941057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930712820831451119685637 362008653905897084941057)
                  ·
                    rfl

theorem cell21_1586271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 4].length) (baseStart_1586271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586271 prefixEnd_1586271 := by exact prefixLift 1586271
  have htrace : WordTrace (prefixWord ++ tailWord_1586271) baseStart_1586271 baseEnd_1586271 := by
    simpa [prefixWord, tailWord_1586271, baseEnd_1586271] using wordTrace_append hprefix tailTrace_1586271
  have hstable : (prefixWord ++ tailWord_1586271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586271).length < 2 ^ (prefixWord ++ tailWord_1586271).sum := by decide
  have hdescent : baseEnd_1586271 < baseStart_1586271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586361 : List Nat := [1, 2, 1, 4, 1, 4, 8]
def baseStart_1586361 : Nat := 118140960795 + 1586361 * 2 ^ 59
def prefixEnd_1586361 : Nat := 4983230072969 + 3 ^ 40 * 1586361 * 2
def baseEnd_1586361 : Nat := 40225465903564103160097

theorem tailTrace_1586361 : CollatzResearch.WordTrace tailWord_1586361 prefixEnd_1586361 40225465903564103160097 := by
  unfold tailWord_1586361
  simp only [CollatzResearch.WordTrace]
  refine ⟨57859339005892500734158937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38572892670595000489439291 57859339005892500734158937)
  ·
    refine ⟨43394504254419375550619203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57859339005892500734158937 43394504254419375550619203)
    ·
      refine ⟨65091756381629063325928805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43394504254419375550619203 65091756381629063325928805)
      ·
        refine ⟨12204704321555449373611651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65091756381629063325928805 12204704321555449373611651)
        ·
          refine ⟨18307056482333174060417477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12204704321555449373611651 18307056482333174060417477)
          ·
            refine ⟨3432573090437470136328277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18307056482333174060417477 3432573090437470136328277)
            ·
              refine ⟨40225465903564103160097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3432573090437470136328277 40225465903564103160097)
              ·
                rfl

theorem cell21_1586361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 8].length) (baseStart_1586361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586361 prefixEnd_1586361 := by exact prefixLift 1586361
  have htrace : WordTrace (prefixWord ++ tailWord_1586361) baseStart_1586361 baseEnd_1586361 := by
    simpa [prefixWord, tailWord_1586361, baseEnd_1586361] using wordTrace_append hprefix tailTrace_1586361
  have hstable : (prefixWord ++ tailWord_1586361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586361).length < 2 ^ (prefixWord ++ tailWord_1586361).sum := by decide
  have hdescent : baseEnd_1586361 < baseStart_1586361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586364 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_1586364 : Nat := 118140960795 + 1586364 * 2 ^ 59
def prefixEnd_1586364 : Nat := 4983230072969 + 3 ^ 40 * 1586364 * 2
def baseEnd_1586364 : Nat := 362029877772949589890867

theorem tailTrace_1586364 : CollatzResearch.WordTrace tailWord_1586364 prefixEnd_1586364 362029877772949589890867 := by
  unfold tailWord_1586364
  simp only [CollatzResearch.WordTrace]
  refine ⟨28929724212440816123259073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38572965616587754831012097 28929724212440816123259073)
  ·
    refine ⟨21697293159330612092444305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28929724212440816123259073 21697293159330612092444305)
    ·
      refine ⟨16272969869497959069333229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21697293159330612092444305 16272969869497959069333229)
      ·
        refine ⟨6102363701061734650999961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16272969869497959069333229 6102363701061734650999961)
        ·
          refine ⟨4576772775796300988249971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6102363701061734650999961 4576772775796300988249971)
          ·
            refine ⟨6865159163694451482374957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576772775796300988249971 6865159163694451482374957)
            ·
              refine ⟨2574434686385419305890609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6865159163694451482374957 2574434686385419305890609)
              ·
                refine ⟨1930826014789064479417957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2574434686385419305890609 1930826014789064479417957)
                ·
                  refine ⟨362029877772949589890867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930826014789064479417957 362029877772949589890867)
                  ·
                    rfl

theorem cell21_1586364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_1586364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586364 prefixEnd_1586364 := by exact prefixLift 1586364
  have htrace : WordTrace (prefixWord ++ tailWord_1586364) baseStart_1586364 baseEnd_1586364 := by
    simpa [prefixWord, tailWord_1586364, baseEnd_1586364] using wordTrace_append hprefix tailTrace_1586364
  have hstable : (prefixWord ++ tailWord_1586364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586364).length < 2 ^ (prefixWord ++ tailWord_1586364).sum := by decide
  have hdescent : baseEnd_1586364 < baseStart_1586364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586426 : List Nat := [3, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_1586426 : Nat := 118140960795 + 1586426 * 2 ^ 59
def prefixEnd_1586426 : Nat := 4983230072969 + 3 ^ 40 * 1586426 * 2
def baseEnd_1586426 : Nat := 362044027017651259857407

theorem tailTrace_1586426 : CollatzResearch.WordTrace tailWord_1586426 prefixEnd_1586426 362044027017651259857407 := by
  unfold tailWord_1586426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14465427437664254208818783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38574473167104677890183421 14465427437664254208818783)
  ·
    refine ⟨21698141156496381313228175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14465427437664254208818783 21698141156496381313228175)
    ·
      refine ⟨32547211734744571969842263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21698141156496381313228175 32547211734744571969842263)
      ·
        refine ⟨48820817602116857954763395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32547211734744571969842263 48820817602116857954763395)
        ·
          refine ⟨73231226403175286932145093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48820817602116857954763395 73231226403175286932145093)
          ·
            refine ⟨13730854950595366299777205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73231226403175286932145093 13730854950595366299777205)
            ·
              refine ⟨1287267651618315590604113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13730854950595366299777205 1287267651618315590604113)
              ·
                refine ⟨965450738713736692953085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287267651618315590604113 965450738713736692953085)
                ·
                  refine ⟨362044027017651259857407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965450738713736692953085 362044027017651259857407)
                  ·
                    rfl

theorem cell21_1586426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_1586426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586426 prefixEnd_1586426 := by exact prefixLift 1586426
  have htrace : WordTrace (prefixWord ++ tailWord_1586426) baseStart_1586426 baseEnd_1586426 := by
    simpa [prefixWord, tailWord_1586426, baseEnd_1586426] using wordTrace_append hprefix tailTrace_1586426
  have hstable : (prefixWord ++ tailWord_1586426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586426).length < 2 ^ (prefixWord ++ tailWord_1586426).sum := by decide
  have hdescent : baseEnd_1586426 < baseStart_1586426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586437 : List Nat := [1, 3, 1, 1, 2, 1, 6, 6]
def baseStart_1586437 : Nat := 118140960795 + 1586437 * 2 ^ 59
def prefixEnd_1586437 : Nat := 4983230072969 + 3 ^ 40 * 1586437 * 2
def baseEnd_1586437 : Nat := 120682179122505895058017

theorem tailTrace_1586437 : CollatzResearch.WordTrace tailWord_1586437 prefixEnd_1586437 120682179122505895058017 := by
  unfold tailWord_1586437
  simp only [CollatzResearch.WordTrace]
  refine ⟨57862110953617165713925565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38574740635744777142617043 57862110953617165713925565)
  ·
    refine ⟨21698291607606437142722087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57862110953617165713925565 21698291607606437142722087)
    ·
      refine ⟨32547437411409655714083131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21698291607606437142722087 32547437411409655714083131)
      ·
        refine ⟨48821156117114483571124697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32547437411409655714083131 48821156117114483571124697)
        ·
          refine ⟨36615867087835862678343523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48821156117114483571124697 36615867087835862678343523)
          ·
            refine ⟨54923800631753794017515285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36615867087835862678343523 54923800631753794017515285)
            ·
              refine ⟨2574553154613459094571029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54923800631753794017515285 2574553154613459094571029)
              ·
                refine ⟨120682179122505895058017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2574553154613459094571029 120682179122505895058017)
                ·
                  rfl

theorem cell21_1586437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 6].length) (baseStart_1586437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586437 prefixEnd_1586437 := by exact prefixLift 1586437
  have htrace : WordTrace (prefixWord ++ tailWord_1586437) baseStart_1586437 baseEnd_1586437 := by
    simpa [prefixWord, tailWord_1586437, baseEnd_1586437] using wordTrace_append hprefix tailTrace_1586437
  have hstable : (prefixWord ++ tailWord_1586437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586437).length < 2 ^ (prefixWord ++ tailWord_1586437).sum := by decide
  have hdescent : baseEnd_1586437 < baseStart_1586437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586440 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_1586440 : Nat := 118140960795 + 1586440 * 2 ^ 59
def prefixEnd_1586440 : Nat := 4983230072969 + 3 ^ 40 * 1586440 * 2
def baseEnd_1586440 : Nat := 362047222008390346624045

theorem tailTrace_1586440 : CollatzResearch.WordTrace tailWord_1586440 prefixEnd_1586440 362047222008390346624045 := by
  unfold tailWord_1586440
  simp only [CollatzResearch.WordTrace]
  refine ⟨28931110186303148613142387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38574813581737531484189849 28931110186303148613142387)
  ·
    refine ⟨43396665279454722919713581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28931110186303148613142387 43396665279454722919713581)
    ·
      refine ⟨16273749479795521094892593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43396665279454722919713581 16273749479795521094892593)
      ·
        refine ⟨12205312109846640821169445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16273749479795521094892593 12205312109846640821169445)
        ·
          refine ⟨2288496020596245153969271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12205312109846640821169445 2288496020596245153969271)
          ·
            refine ⟨3432744030894367730953907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288496020596245153969271 3432744030894367730953907)
            ·
              refine ⟨5149116046341551596430861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432744030894367730953907 5149116046341551596430861)
              ·
                refine ⟨1930918517378081848661573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5149116046341551596430861 1930918517378081848661573)
                ·
                  refine ⟨362047222008390346624045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930918517378081848661573 362047222008390346624045)
                  ·
                    rfl

theorem cell21_1586440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_1586440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586440 prefixEnd_1586440 := by exact prefixLift 1586440
  have htrace : WordTrace (prefixWord ++ tailWord_1586440) baseStart_1586440 baseEnd_1586440 := by
    simpa [prefixWord, tailWord_1586440, baseEnd_1586440] using wordTrace_append hprefix tailTrace_1586440
  have hstable : (prefixWord ++ tailWord_1586440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586440).length < 2 ^ (prefixWord ++ tailWord_1586440).sum := by decide
  have hdescent : baseEnd_1586440 < baseStart_1586440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586527 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 9]
def baseStart_1586527 : Nat := 118140960795 + 1586527 * 2 ^ 59
def prefixEnd_1586527 : Nat := 4983230072969 + 3 ^ 40 * 1586527 * 2
def baseEnd_1586527 : Nat := 362067076593697528673867

theorem tailTrace_1586527 : CollatzResearch.WordTrace tailWord_1586527 prefixEnd_1586527 362067076593697528673867 := by
  unfold tailWord_1586527
  simp only [CollatzResearch.WordTrace]
  refine ⟨57865393523291111084701835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38576929015527407389801223 57865393523291111084701835)
  ·
    refine ⟨86798090284936666627052753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57865393523291111084701835 86798090284936666627052753)
    ·
      refine ⟨65098567713702499970289565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86798090284936666627052753 65098567713702499970289565)
      ·
        refine ⟨24411962892638437488858587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65098567713702499970289565 24411962892638437488858587)
        ·
          refine ⟨36617944338957656233287881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24411962892638437488858587 36617944338957656233287881)
          ·
            refine ⟨27463458254218242174965911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36617944338957656233287881 27463458254218242174965911)
            ·
              refine ⟨41195187381327363262448867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27463458254218242174965911 41195187381327363262448867)
              ·
                refine ⟨61792781071991044893673301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41195187381327363262448867 61792781071991044893673301)
                ·
                  refine ⟨362067076593697528673867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61792781071991044893673301 362067076593697528673867)
                  ·
                    rfl

theorem cell21_1586527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_1586527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586527 prefixEnd_1586527 := by exact prefixLift 1586527
  have htrace : WordTrace (prefixWord ++ tailWord_1586527) baseStart_1586527 baseEnd_1586527 := by
    simpa [prefixWord, tailWord_1586527, baseEnd_1586527] using wordTrace_append hprefix tailTrace_1586527
  have hstable : (prefixWord ++ tailWord_1586527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586527).length < 2 ^ (prefixWord ++ tailWord_1586527).sum := by decide
  have hdescent : baseEnd_1586527 < baseStart_1586527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586544 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_1586544 : Nat := 118140960795 + 1586544 * 2 ^ 59
def prefixEnd_1586544 : Nat := 4983230072969 + 3 ^ 40 * 1586544 * 2
def baseEnd_1586544 : Nat := 362070956225309276890499

theorem tailTrace_1586544 : CollatzResearch.WordTrace tailWord_1586544 prefixEnd_1586544 362070956225309276890499 := by
  unfold tailWord_1586544
  simp only [CollatzResearch.WordTrace]
  refine ⟨28933006782114761494035343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38577342376153015325380457 28933006782114761494035343)
  ·
    refine ⟨43399510173172142241053015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28933006782114761494035343 43399510173172142241053015)
    ·
      refine ⟨65099265259758213361579523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43399510173172142241053015 65099265259758213361579523)
      ·
        refine ⟨97648897889637320042369285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65099265259758213361579523 97648897889637320042369285)
        ·
          refine ⟨18309168354306997507944241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97648897889637320042369285 18309168354306997507944241)
          ·
            refine ⟨13731876265730248130958181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18309168354306997507944241 13731876265730248130958181)
            ·
              refine ⟨2574726799824421524554659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13731876265730248130958181 2574726799824421524554659)
              ·
                refine ⟨3862090199736632286831989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574726799824421524554659 3862090199736632286831989)
                ·
                  refine ⟨362070956225309276890499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3862090199736632286831989 362070956225309276890499)
                  ·
                    rfl

theorem cell21_1586544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_1586544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586544 prefixEnd_1586544 := by exact prefixLift 1586544
  have htrace : WordTrace (prefixWord ++ tailWord_1586544) baseStart_1586544 baseEnd_1586544 := by
    simpa [prefixWord, tailWord_1586544, baseEnd_1586544] using wordTrace_append hprefix tailTrace_1586544
  have hstable : (prefixWord ++ tailWord_1586544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586544).length < 2 ^ (prefixWord ++ tailWord_1586544).sum := by decide
  have hdescent : baseEnd_1586544 < baseStart_1586544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586589 : List Nat := [1, 4, 2, 1, 3, 1, 9]
def baseStart_1586589 : Nat := 118140960795 + 1586589 * 2 ^ 59
def prefixEnd_1586589 : Nat := 4983230072969 + 3 ^ 40 * 1586589 * 2
def baseEnd_1586589 : Nat := 40231247315377688737823

theorem tailTrace_1586589 : CollatzResearch.WordTrace tailWord_1586589 prefixEnd_1586589 40231247315377688737823 := by
  unfold tailWord_1586589
  simp only [CollatzResearch.WordTrace]
  refine ⟨57867654849066495673458821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38578436566044330448972547 57867654849066495673458821)
  ·
    refine ⟨10850185284199967938773529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57867654849066495673458821 10850185284199967938773529)
    ·
      refine ⟨8137638963149975954080147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10850185284199967938773529 8137638963149975954080147)
      ·
        refine ⟨12206458444724963931120221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137638963149975954080147 12206458444724963931120221)
        ·
          refine ⟨4577421916771861474170083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12206458444724963931120221 4577421916771861474170083)
          ·
            refine ⟨6866132875157792211255125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577421916771861474170083 6866132875157792211255125)
            ·
              refine ⟨40231247315377688737823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6866132875157792211255125 40231247315377688737823)
              ·
                rfl

theorem cell21_1586589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 9].length) (baseStart_1586589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586589 prefixEnd_1586589 := by exact prefixLift 1586589
  have htrace : WordTrace (prefixWord ++ tailWord_1586589) baseStart_1586589 baseEnd_1586589 := by
    simpa [prefixWord, tailWord_1586589, baseEnd_1586589] using wordTrace_append hprefix tailTrace_1586589
  have hstable : (prefixWord ++ tailWord_1586589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586589).length < 2 ^ (prefixWord ++ tailWord_1586589).sum := by decide
  have hdescent : baseEnd_1586589 < baseStart_1586589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586741 : List Nat := [1, 3, 3, 1, 1, 4, 1, 7]
def baseStart_1586741 : Nat := 118140960795 + 1586741 * 2 ^ 59
def prefixEnd_1586741 : Nat := 4983230072969 + 3 ^ 40 * 1586741 * 2
def baseEnd_1586741 : Nat := 120705304769760237368921

theorem tailTrace_1586741 : CollatzResearch.WordTrace tailWord_1586741 prefixEnd_1586741 120705304769760237368921 := by
  unfold tailWord_1586741
  simp only [CollatzResearch.WordTrace]
  refine ⟨57873198744515825632992077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38582132496343883755328051 57873198744515825632992077)
  ·
    refine ⟨21702449529193434612372029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57873198744515825632992077 21702449529193434612372029)
    ·
      refine ⟨8138418573447537979639511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21702449529193434612372029 8138418573447537979639511)
      ·
        refine ⟨12207627860171306969459267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8138418573447537979639511 12207627860171306969459267)
        ·
          refine ⟨18311441790256960454188901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12207627860171306969459267 18311441790256960454188901)
          ·
            refine ⟨3433395335673180085160419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18311441790256960454188901 3433395335673180085160419)
            ·
              refine ⟨5150093003509770127740629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433395335673180085160419 5150093003509770127740629)
              ·
                refine ⟨120705304769760237368921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5150093003509770127740629 120705304769760237368921)
                ·
                  rfl

theorem cell21_1586741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 7].length) (baseStart_1586741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586741 prefixEnd_1586741 := by exact prefixLift 1586741
  have htrace : WordTrace (prefixWord ++ tailWord_1586741) baseStart_1586741 baseEnd_1586741 := by
    simpa [prefixWord, tailWord_1586741, baseEnd_1586741] using wordTrace_append hprefix tailTrace_1586741
  have hstable : (prefixWord ++ tailWord_1586741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586741).length < 2 ^ (prefixWord ++ tailWord_1586741).sum := by decide
  have hdescent : baseEnd_1586741 < baseStart_1586741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586820 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1586820 : Nat := 118140960795 + 1586820 * 2 ^ 59
def prefixEnd_1586820 : Nat := 4983230072969 + 3 ^ 40 * 1586820 * 2
def baseEnd_1586820 : Nat := 362133943185594130289935

theorem tailTrace_1586820 : CollatzResearch.WordTrace tailWord_1586820 prefixEnd_1586820 362133943185594130289935 := by
  unfold tailWord_1586820
  simp only [CollatzResearch.WordTrace]
  refine ⟨28938040055614811062558957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38584053407486414750078609 28938040055614811062558957)
  ·
    refine ⟨10851765020855554148459609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28938040055614811062558957 10851765020855554148459609)
    ·
      refine ⟨8138823765641665611344707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10851765020855554148459609 8138823765641665611344707)
      ·
        refine ⟨12208235648462498417017061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8138823765641665611344707 12208235648462498417017061)
        ·
          refine ⟨2289044184086718453190699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12208235648462498417017061 2289044184086718453190699)
          ·
            refine ⟨3433566276130077679786049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289044184086718453190699 3433566276130077679786049)
            ·
              refine ⟨2575174707097558259839537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3433566276130077679786049 2575174707097558259839537)
              ·
                refine ⟨1931381030323168694879653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575174707097558259839537 1931381030323168694879653)
                ·
                  refine ⟨362133943185594130289935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931381030323168694879653 362133943185594130289935)
                  ·
                    rfl

theorem cell21_1586820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1586820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586820 prefixEnd_1586820 := by exact prefixLift 1586820
  have htrace : WordTrace (prefixWord ++ tailWord_1586820) baseStart_1586820 baseEnd_1586820 := by
    simpa [prefixWord, tailWord_1586820, baseEnd_1586820] using wordTrace_append hprefix tailTrace_1586820
  have hstable : (prefixWord ++ tailWord_1586820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586820).length < 2 ^ (prefixWord ++ tailWord_1586820).sum := by decide
  have hdescent : baseEnd_1586820 < baseStart_1586820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586848 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_1586848 : Nat := 118140960795 + 1586848 * 2 ^ 59
def prefixEnd_1586848 : Nat := 4983230072969 + 3 ^ 40 * 1586848 * 2
def baseEnd_1586848 : Nat := 362140333167072303823211

theorem tailTrace_1586848 : CollatzResearch.WordTrace tailWord_1586848 prefixEnd_1586848 362140333167072303823211 := by
  unfold tailWord_1586848
  simp only [CollatzResearch.WordTrace]
  refine ⟨28938550677564091453568599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38584734236752121938091465 28938550677564091453568599)
  ·
    refine ⟨43407826016346137180352899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28938550677564091453568599 43407826016346137180352899)
    ·
      refine ⟨65111739024519205770529349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43407826016346137180352899 65111739024519205770529349)
      ·
        refine ⟨12208451067097351081974253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65111739024519205770529349 12208451067097351081974253)
        ·
          refine ⟨4578169150161506655740345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12208451067097351081974253 4578169150161506655740345)
          ·
            refine ⟨3433626862621129991805259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4578169150161506655740345 3433626862621129991805259)
            ·
              refine ⟨5150440293931694987707889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433626862621129991805259 5150440293931694987707889)
              ·
                refine ⟨3862830220448771240780917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5150440293931694987707889 3862830220448771240780917)
                ·
                  refine ⟨362140333167072303823211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3862830220448771240780917 362140333167072303823211)
                  ·
                    rfl

theorem cell21_1586848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_1586848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586848 prefixEnd_1586848 := by exact prefixLift 1586848
  have htrace : WordTrace (prefixWord ++ tailWord_1586848) baseStart_1586848 baseEnd_1586848 := by
    simpa [prefixWord, tailWord_1586848, baseEnd_1586848] using wordTrace_append hprefix tailTrace_1586848
  have hstable : (prefixWord ++ tailWord_1586848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586848).length < 2 ^ (prefixWord ++ tailWord_1586848).sum := by decide
  have hdescent : baseEnd_1586848 < baseStart_1586848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586938 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_1586938 : Nat := 118140960795 + 1586938 * 2 ^ 59
def prefixEnd_1586938 : Nat := 4983230072969 + 3 ^ 40 * 1586938 * 2
def baseEnd_1586938 : Nat := 362160872393252147323027

theorem tailTrace_1586938 : CollatzResearch.WordTrace tailWord_1586938 prefixEnd_1586938 362160872393252147323027 := by
  unfold tailWord_1586938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14470095981200532069478367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38586922616534752185275645 14470095981200532069478367)
  ·
    refine ⟨21705143971800798104217551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14470095981200532069478367 21705143971800798104217551)
    ·
      refine ⟨32557715957701197156326327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21705143971800798104217551 32557715957701197156326327)
      ·
        refine ⟨48836573936551795734489491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32557715957701197156326327 48836573936551795734489491)
        ·
          refine ⟨73254860904827693601734237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48836573936551795734489491 73254860904827693601734237)
          ·
            refine ⟨27470572839310385100650339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73254860904827693601734237 27470572839310385100650339)
            ·
              refine ⟨41205859258965577650975509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27470572839310385100650339 41205859258965577650975509)
              ·
                refine ⟨1931524652764011452389477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41205859258965577650975509 1931524652764011452389477)
                ·
                  refine ⟨362160872393252147323027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931524652764011452389477 362160872393252147323027)
                  ·
                    rfl

theorem cell21_1586938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_1586938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586938 prefixEnd_1586938 := by exact prefixLift 1586938
  have htrace : WordTrace (prefixWord ++ tailWord_1586938) baseStart_1586938 baseEnd_1586938 := by
    simpa [prefixWord, tailWord_1586938, baseEnd_1586938] using wordTrace_append hprefix tailTrace_1586938
  have hstable : (prefixWord ++ tailWord_1586938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586938).length < 2 ^ (prefixWord ++ tailWord_1586938).sum := by decide
  have hdescent : baseEnd_1586938 < baseStart_1586938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586955 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 4]
def baseStart_1586955 : Nat := 118140960795 + 1586955 * 2 ^ 59
def prefixEnd_1586955 : Nat := 4983230072969 + 3 ^ 40 * 1586955 * 2
def baseEnd_1586955 : Nat := 362164752024863895539659

theorem tailTrace_1586955 : CollatzResearch.WordTrace tailWord_1586955 prefixEnd_1586955 362164752024863895539659 := by
  unfold tailWord_1586955
  simp only [CollatzResearch.WordTrace]
  refine ⟨57881003965740540181282319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38587335977160360120854879 57881003965740540181282319)
  ·
    refine ⟨86821505948610810271923479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57881003965740540181282319 86821505948610810271923479)
    ·
      refine ⟨130232258922916215407885219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86821505948610810271923479 130232258922916215407885219)
      ·
        refine ⟨195348388384374323111827829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130232258922916215407885219 195348388384374323111827829)
        ·
          refine ⟨18313911411035092791733859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195348388384374323111827829 18313911411035092791733859)
          ·
            refine ⟨27470867116552639187600789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18313911411035092791733859 27470867116552639187600789)
            ·
              refine ⟨1287696896088404961918787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27470867116552639187600789 1287696896088404961918787)
              ·
                refine ⟨1931545344132607442878181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287696896088404961918787 1931545344132607442878181)
                ·
                  refine ⟨362164752024863895539659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931545344132607442878181 362164752024863895539659)
                  ·
                    rfl

theorem cell21_1586955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 4].length) (baseStart_1586955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1586955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1586955 prefixEnd_1586955 := by exact prefixLift 1586955
  have htrace : WordTrace (prefixWord ++ tailWord_1586955) baseStart_1586955 baseEnd_1586955 := by
    simpa [prefixWord, tailWord_1586955, baseEnd_1586955] using wordTrace_append hprefix tailTrace_1586955
  have hstable : (prefixWord ++ tailWord_1586955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586955).length < 2 ^ (prefixWord ++ tailWord_1586955).sum := by decide
  have hdescent : baseEnd_1586955 < baseStart_1586955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587079 : List Nat := [1, 1, 4, 2, 5, 1, 2, 5]
def baseStart_1587079 : Nat := 118140960795 + 1587079 * 2 ^ 59
def prefixEnd_1587079 : Nat := 4983230072969 + 3 ^ 40 * 1587079 * 2
def baseEnd_1587079 : Nat := 120731016838089078490913

theorem tailTrace_1587079 : CollatzResearch.WordTrace tailWord_1587079 prefixEnd_1587079 120731016838089078490913 := by
  unfold tailWord_1587079
  simp only [CollatzResearch.WordTrace]
  refine ⟨57885526617291309358796291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38590351078194206239197527 57885526617291309358796291)
  ·
    refine ⟨86828289925936964038194437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57885526617291309358796291 86828289925936964038194437)
    ·
      refine ⟨16280304361113180757161457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86828289925936964038194437 16280304361113180757161457)
      ·
        refine ⟨12210228270834885567871093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16280304361113180757161457 12210228270834885567871093)
        ·
          refine ⟨1144708900390770521987915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12210228270834885567871093 1144708900390770521987915)
          ·
            refine ⟨1717063350586155782981873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144708900390770521987915 1717063350586155782981873)
            ·
              refine ⟨1287797512939616837236405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717063350586155782981873 1287797512939616837236405)
              ·
                refine ⟨120731016838089078490913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1287797512939616837236405 120731016838089078490913)
                ·
                  rfl

theorem cell21_1587079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 5].length) (baseStart_1587079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587079 prefixEnd_1587079 := by exact prefixLift 1587079
  have htrace : WordTrace (prefixWord ++ tailWord_1587079) baseStart_1587079 baseEnd_1587079 := by
    simpa [prefixWord, tailWord_1587079, baseEnd_1587079] using wordTrace_append hprefix tailTrace_1587079
  have hstable : (prefixWord ++ tailWord_1587079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587079).length < 2 ^ (prefixWord ++ tailWord_1587079).sum := by decide
  have hdescent : baseEnd_1587079 < baseStart_1587079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587121 : List Nat := [1, 2, 2, 4, 2, 2, 2, 6]
def baseStart_1587121 : Nat := 118140960795 + 1587121 * 2 ^ 59
def prefixEnd_1587121 : Nat := 4983230072969 + 3 ^ 40 * 1587121 * 2
def baseEnd_1587121 : Nat := 120734211828828165257551

theorem tailTrace_1587121 : CollatzResearch.WordTrace tailWord_1587121 prefixEnd_1587121 120734211828828165257551 := by
  unfold tailWord_1587121
  simp only [CollatzResearch.WordTrace]
  refine ⟨57887058483139150531825217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38591372322092767021216811 57887058483139150531825217)
  ·
    refine ⟨43415293862354362898868913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57887058483139150531825217 43415293862354362898868913)
    ·
      refine ⟨32561470396765772174151685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43415293862354362898868913 32561470396765772174151685)
      ·
        refine ⟨6105275699393582282653441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32561470396765772174151685 6105275699393582282653441)
        ·
          refine ⟨4578956774545186711990081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6105275699393582282653441 4578956774545186711990081)
          ·
            refine ⟨3434217580908890033992561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4578956774545186711990081 3434217580908890033992561)
            ·
              refine ⟨2575663185681667525494421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3434217580908890033992561 2575663185681667525494421)
              ·
                refine ⟨120734211828828165257551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2575663185681667525494421 120734211828828165257551)
                ·
                  rfl

theorem cell21_1587121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 6].length) (baseStart_1587121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587121 prefixEnd_1587121 := by exact prefixLift 1587121
  have htrace : WordTrace (prefixWord ++ tailWord_1587121) baseStart_1587121 baseEnd_1587121 := by
    simpa [prefixWord, tailWord_1587121, baseEnd_1587121] using wordTrace_append hprefix tailTrace_1587121
  have hstable : (prefixWord ++ tailWord_1587121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587121).length < 2 ^ (prefixWord ++ tailWord_1587121).sum := by decide
  have hdescent : baseEnd_1587121 < baseStart_1587121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587169 : List Nat := [1, 2, 3, 1, 2, 1, 6, 2, 3]
def baseStart_1587169 : Nat := 118140960795 + 1587169 * 2 ^ 59
def prefixEnd_1587169 : Nat := 4983230072969 + 3 ^ 40 * 1587169 * 2
def baseEnd_1587169 : Nat := 362213589740447078972555

theorem tailTrace_1587169 : CollatzResearch.WordTrace tailWord_1587169 prefixEnd_1587169 362213589740447078972555 := by
  unfold tailWord_1587169
  simp only [CollatzResearch.WordTrace]
  refine ⟨57888809186965254729572561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38592539457976836486381707 57888809186965254729572561)
  ·
    refine ⟨43416606890223941047179421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57888809186965254729572561 43416606890223941047179421)
    ·
      refine ⟨16281227583833977892692283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43416606890223941047179421 16281227583833977892692283)
      ·
        refine ⟨24421841375750966839038425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16281227583833977892692283 24421841375750966839038425)
        ·
          refine ⟨18316381031813225129278819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24421841375750966839038425 18316381031813225129278819)
          ·
            refine ⟨27474571547719837693918229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18316381031813225129278819 27474571547719837693918229)
            ·
              refine ⟨1287870541299367391902417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27474571547719837693918229 1287870541299367391902417)
              ·
                refine ⟨965902905974525543926813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287870541299367391902417 965902905974525543926813)
                ·
                  refine ⟨362213589740447078972555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965902905974525543926813 362213589740447078972555)
                  ·
                    rfl

theorem cell21_1587169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_1587169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587169 prefixEnd_1587169 := by exact prefixLift 1587169
  have htrace : WordTrace (prefixWord ++ tailWord_1587169) baseStart_1587169 baseEnd_1587169 := by
    simpa [prefixWord, tailWord_1587169, baseEnd_1587169] using wordTrace_append hprefix tailTrace_1587169
  have hstable : (prefixWord ++ tailWord_1587169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587169).length < 2 ^ (prefixWord ++ tailWord_1587169).sum := by decide
  have hdescent : baseEnd_1587169 < baseStart_1587169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587228 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_1587228 : Nat := 118140960795 + 1587228 * 2 ^ 59
def prefixEnd_1587228 : Nat := 4983230072969 + 3 ^ 40 * 1587228 * 2
def baseEnd_1587228 : Nat := 362227054344276087489101

theorem tailTrace_1587228 : CollatzResearch.WordTrace tailWord_1587228 prefixEnd_1587228 362227054344276087489101 := by
  unfold tailWord_1587228
  simp only [CollatzResearch.WordTrace]
  refine ⟨28945480546875753902985169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38593974062501005203980225 28945480546875753902985169)
  ·
    refine ⟨21709110410156815427238877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28945480546875753902985169 21709110410156815427238877)
    ·
      refine ⟨8140916403808805785214579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21709110410156815427238877 8140916403808805785214579)
      ·
        refine ⟨12211374605713208677821869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8140916403808805785214579 12211374605713208677821869)
        ·
          refine ⟨4579265477142453254183201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12211374605713208677821869 4579265477142453254183201)
          ·
            refine ⟨3434449107856839940637401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4579265477142453254183201 3434449107856839940637401)
            ·
              refine ⟨2575836830892629955478051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3434449107856839940637401 2575836830892629955478051)
              ·
                refine ⟨3863755246338944933217077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575836830892629955478051 3863755246338944933217077)
                ·
                  refine ⟨362227054344276087489101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3863755246338944933217077 362227054344276087489101)
                  ·
                    rfl

theorem cell21_1587228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_1587228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587228 prefixEnd_1587228 := by exact prefixLift 1587228
  have htrace : WordTrace (prefixWord ++ tailWord_1587228) baseStart_1587228 baseEnd_1587228 := by
    simpa [prefixWord, tailWord_1587228, baseEnd_1587228] using wordTrace_append hprefix tailTrace_1587228
  have hstable : (prefixWord ++ tailWord_1587228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587228).length < 2 ^ (prefixWord ++ tailWord_1587228).sum := by decide
  have hdescent : baseEnd_1587228 < baseStart_1587228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587287 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 5]
def baseStart_1587287 : Nat := 118140960795 + 1587287 * 2 ^ 59
def prefixEnd_1587287 : Nat := 4983230072969 + 3 ^ 40 * 1587287 * 2
def baseEnd_1587287 : Nat := 362240518948105096005647

theorem tailTrace_1587287 : CollatzResearch.WordTrace tailWord_1587287 prefixEnd_1587287 362240518948105096005647 := by
  unfold tailWord_1587287
  simp only [CollatzResearch.WordTrace]
  refine ⟨57893113000537760882368115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38595408667025173921578743 57893113000537760882368115)
  ·
    refine ⟨86839669500806641323552173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57893113000537760882368115 86839669500806641323552173)
    ·
      refine ⟨32564876062802490496332065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86839669500806641323552173 32564876062802490496332065)
      ·
        refine ⟨24423657047101867872249049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32564876062802490496332065 24423657047101867872249049)
        ·
          refine ⟨18317742785326400904186787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24423657047101867872249049 18317742785326400904186787)
          ·
            refine ⟨27476614177989601356280181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18317742785326400904186787 27476614177989601356280181)
            ·
              refine ⟨2575932579186525127151267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27476614177989601356280181 2575932579186525127151267)
              ·
                refine ⟨3863898868779787690726901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575932579186525127151267 3863898868779787690726901)
                ·
                  refine ⟨362240518948105096005647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3863898868779787690726901 362240518948105096005647)
                  ·
                    rfl

theorem cell21_1587287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 5].length) (baseStart_1587287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587287 prefixEnd_1587287 := by exact prefixLift 1587287
  have htrace : WordTrace (prefixWord ++ tailWord_1587287) baseStart_1587287 baseEnd_1587287 := by
    simpa [prefixWord, tailWord_1587287, baseEnd_1587287] using wordTrace_append hprefix tailTrace_1587287
  have hstable : (prefixWord ++ tailWord_1587287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587287).length < 2 ^ (prefixWord ++ tailWord_1587287).sum := by decide
  have hdescent : baseEnd_1587287 < baseStart_1587287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587293 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 4]
def baseStart_1587293 : Nat := 118140960795 + 1587293 * 2 ^ 59
def prefixEnd_1587293 : Nat := 4983230072969 + 3 ^ 40 * 1587293 * 2
def baseEnd_1587293 : Nat := 362241888229850418905635

theorem tailTrace_1587293 : CollatzResearch.WordTrace tailWord_1587293 prefixEnd_1587293 362241888229850418905635 := by
  unfold tailWord_1587293
  simp only [CollatzResearch.WordTrace]
  refine ⟨57893331838516023907086533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38595554559010682604724355 57893331838516023907086533)
  ·
    refine ⟨10854999719721754482578725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57893331838516023907086533 10854999719721754482578725)
    ·
      refine ⟨2035312447447828965483511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10854999719721754482578725 2035312447447828965483511)
      ·
        refine ⟨3052968671171743448225267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035312447447828965483511 3052968671171743448225267)
        ·
          refine ⟨4579453006757615172337901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052968671171743448225267 4579453006757615172337901)
          ·
            refine ⟨1717294877534105689626713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4579453006757615172337901 1717294877534105689626713)
            ·
              refine ⟨1287971158150579267220035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717294877534105689626713 1287971158150579267220035)
              ·
                refine ⟨1931956737225868900830053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287971158150579267220035 1931956737225868900830053)
                ·
                  refine ⟨362241888229850418905635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931956737225868900830053 362241888229850418905635)
                  ·
                    rfl

theorem cell21_1587293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_1587293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587293 prefixEnd_1587293 := by exact prefixLift 1587293
  have htrace : WordTrace (prefixWord ++ tailWord_1587293) baseStart_1587293 baseEnd_1587293 := by
    simpa [prefixWord, tailWord_1587293, baseEnd_1587293] using wordTrace_append hprefix tailTrace_1587293
  have hstable : (prefixWord ++ tailWord_1587293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587293).length < 2 ^ (prefixWord ++ tailWord_1587293).sum := by decide
  have hdescent : baseEnd_1587293 < baseStart_1587293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587338 : List Nat := [3, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_1587338 : Nat := 118140960795 + 1587338 * 2 ^ 59
def prefixEnd_1587338 : Nat := 4983230072969 + 3 ^ 40 * 1587338 * 2
def baseEnd_1587338 : Nat := 362252157842940340655543

theorem tailTrace_1587338 : CollatzResearch.WordTrace tailWord_1587338 prefixEnd_1587338 362252157842940340655543 := by
  unfold tailWord_1587338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14473743280838249148118667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38596648748901997728316445 14473743280838249148118667)
  ·
    refine ⟨21710614921257373722178001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14473743280838249148118667 21710614921257373722178001)
    ·
      refine ⟨16282961190943030291633501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21710614921257373722178001 16282961190943030291633501)
      ·
        refine ⟨6106110446603636359362563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16282961190943030291633501 6106110446603636359362563)
        ·
          refine ⟨9159165669905454539043845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6106110446603636359362563 9159165669905454539043845)
          ·
            refine ⟨1717343563107272726070721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9159165669905454539043845 1717343563107272726070721)
            ·
              refine ⟨1288007672330454544553041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717343563107272726070721 1288007672330454544553041)
              ·
                refine ⟨966005754247840908414781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288007672330454544553041 966005754247840908414781)
                ·
                  refine ⟨362252157842940340655543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966005754247840908414781 362252157842940340655543)
                  ·
                    rfl

theorem cell21_1587338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_1587338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587338 prefixEnd_1587338 := by exact prefixLift 1587338
  have htrace : WordTrace (prefixWord ++ tailWord_1587338) baseStart_1587338 baseEnd_1587338 := by
    simpa [prefixWord, tailWord_1587338, baseEnd_1587338] using wordTrace_append hprefix tailTrace_1587338
  have hstable : (prefixWord ++ tailWord_1587338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587338).length < 2 ^ (prefixWord ++ tailWord_1587338).sum := by decide
  have hdescent : baseEnd_1587338 < baseStart_1587338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587470 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_1587470 : Nat := 118140960795 + 1587470 * 2 ^ 59
def prefixEnd_1587470 : Nat := 4983230072969 + 3 ^ 40 * 1587470 * 2
def baseEnd_1587470 : Nat := 362282282041337444455273

theorem tailTrace_1587470 : CollatzResearch.WordTrace tailWord_1587470 prefixEnd_1587470 362282282041337444455273 := by
  unfold tailWord_1587470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237473444859347892034983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38599858372583188757519909 7237473444859347892034983)
  ·
    refine ⟨10856210167289021838052475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7237473444859347892034983 10856210167289021838052475)
    ·
      refine ⟨16284315250933532757078713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10856210167289021838052475 16284315250933532757078713)
      ·
        refine ⟨12213236438200149567809035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16284315250933532757078713 12213236438200149567809035)
        ·
          refine ⟨18319854657300224351713553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12213236438200149567809035 18319854657300224351713553)
          ·
            refine ⟨13739890992975168263785165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18319854657300224351713553 13739890992975168263785165)
            ·
              refine ⟨5152459122365688098919437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13739890992975168263785165 5152459122365688098919437)
              ·
                refine ⟨1932172170887133037094789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5152459122365688098919437 1932172170887133037094789)
                ·
                  refine ⟨362282282041337444455273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1932172170887133037094789 362282282041337444455273)
                  ·
                    rfl

theorem cell21_1587470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_1587470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587470 prefixEnd_1587470 := by exact prefixLift 1587470
  have htrace : WordTrace (prefixWord ++ tailWord_1587470) baseStart_1587470 baseEnd_1587470 := by
    simpa [prefixWord, tailWord_1587470, baseEnd_1587470] using wordTrace_append hprefix tailTrace_1587470
  have hstable : (prefixWord ++ tailWord_1587470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587470).length < 2 ^ (prefixWord ++ tailWord_1587470).sum := by decide
  have hdescent : baseEnd_1587470 < baseStart_1587470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587501 : List Nat := [1, 5, 3, 1, 2, 9]
def baseStart_1587501 : Nat := 118140960795 + 1587501 * 2 ^ 59
def prefixEnd_1587501 : Nat := 4983230072969 + 3 ^ 40 * 1587501 * 2
def baseEnd_1587501 : Nat := 13418124320877343682909

theorem tailTrace_1587501 : CollatzResearch.WordTrace tailWord_1587501 prefixEnd_1587501 13418124320877343682909 := by
  unfold tailWord_1587501
  simp only [CollatzResearch.WordTrace]
  refine ⟨57900918221762475430658357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38600612147841650287105571 57900918221762475430658357)
  ·
    refine ⟨5428211083290232071624221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57900918221762475430658357 5428211083290232071624221)
    ·
      refine ⟨2035579156233837026859083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5428211083290232071624221 2035579156233837026859083)
      ·
        refine ⟨3053368734350755540288625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035579156233837026859083 3053368734350755540288625)
        ·
          refine ⟨2290026550763066655216469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3053368734350755540288625 2290026550763066655216469)
          ·
            refine ⟨13418124320877343682909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2290026550763066655216469 13418124320877343682909)
            ·
              rfl

theorem cell21_1587501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 9].length) (baseStart_1587501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587501 prefixEnd_1587501 := by exact prefixLift 1587501
  have htrace : WordTrace (prefixWord ++ tailWord_1587501) baseStart_1587501 baseEnd_1587501 := by
    simpa [prefixWord, tailWord_1587501, baseEnd_1587501] using wordTrace_append hprefix tailTrace_1587501
  have hstable : (prefixWord ++ tailWord_1587501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587501).length < 2 ^ (prefixWord ++ tailWord_1587501).sum := by decide
  have hdescent : baseEnd_1587501 < baseStart_1587501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587560 : List Nat := [2, 1, 4, 2, 2, 2, 8]
def baseStart_1587560 : Nat := 118140960795 + 1587560 * 2 ^ 59
def prefixEnd_1587560 : Nat := 4983230072969 + 3 ^ 40 * 1587560 * 2
def baseEnd_1587560 : Nat := 40255869029724143106121

theorem tailTrace_1587560 : CollatzResearch.WordTrace tailWord_1587560 prefixEnd_1587560 40255869029724143106121 := by
  unfold tailWord_1587560
  simp only [CollatzResearch.WordTrace]
  refine ⟨28951535064274364253528067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38602046752365819004704089 28951535064274364253528067)
  ·
    refine ⟨43427302596411546380292101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28951535064274364253528067 43427302596411546380292101)
    ·
      refine ⟨8142619236827164946304769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43427302596411546380292101 8142619236827164946304769)
      ·
        refine ⟨6106964427620373709728577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8142619236827164946304769 6106964427620373709728577)
        ·
          refine ⟨4580223320715280282296433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6106964427620373709728577 4580223320715280282296433)
          ·
            refine ⟨3435167490536460211722325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4580223320715280282296433 3435167490536460211722325)
            ·
              refine ⟨40255869029724143106121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3435167490536460211722325 40255869029724143106121)
              ·
                rfl

theorem cell21_1587560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 8].length) (baseStart_1587560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587560 prefixEnd_1587560 := by exact prefixLift 1587560
  have htrace : WordTrace (prefixWord ++ tailWord_1587560) baseStart_1587560 baseEnd_1587560 := by
    simpa [prefixWord, tailWord_1587560, baseEnd_1587560] using wordTrace_append hprefix tailTrace_1587560
  have hstable : (prefixWord ++ tailWord_1587560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587560).length < 2 ^ (prefixWord ++ tailWord_1587560).sum := by decide
  have hdescent : baseEnd_1587560 < baseStart_1587560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587619 : List Nat := [1, 1, 1, 4, 1, 4, 9]
def baseStart_1587619 : Nat := 118140960795 + 1587619 * 2 ^ 59
def prefixEnd_1587619 : Nat := 4983230072969 + 3 ^ 40 * 1587619 * 2
def baseEnd_1587619 : Nat := 40257365096816255163515

theorem tailTrace_1587619 : CollatzResearch.WordTrace tailWord_1587619 prefixEnd_1587619 40257365096816255163515 := by
  unfold tailWord_1587619
  simp only [CollatzResearch.WordTrace]
  refine ⟨57905222035334981583453911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38603481356889987722302607 57905222035334981583453911)
  ·
    refine ⟨86857833053002472375180867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57905222035334981583453911 86857833053002472375180867)
    ·
      refine ⟨130286749579503708562771301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86857833053002472375180867 130286749579503708562771301)
      ·
        refine ⟨24428765546156945355519619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130286749579503708562771301 24428765546156945355519619)
        ·
          refine ⟨36643148319235418033279429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24428765546156945355519619 36643148319235418033279429)
          ·
            refine ⟨6870590309856640881239893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36643148319235418033279429 6870590309856640881239893)
            ·
              refine ⟨40257365096816255163515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6870590309856640881239893 40257365096816255163515)
              ·
                rfl

theorem cell21_1587619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 9].length) (baseStart_1587619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587619 prefixEnd_1587619 := by exact prefixLift 1587619
  have htrace : WordTrace (prefixWord ++ tailWord_1587619) baseStart_1587619 baseEnd_1587619 := by
    simpa [prefixWord, tailWord_1587619, baseEnd_1587619] using wordTrace_append hprefix tailTrace_1587619
  have hstable : (prefixWord ++ tailWord_1587619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587619).length < 2 ^ (prefixWord ++ tailWord_1587619).sum := by decide
  have hdescent : baseEnd_1587619 < baseStart_1587619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587639 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 4]
def baseStart_1587639 : Nat := 118140960795 + 1587639 * 2 ^ 59
def prefixEnd_1587639 : Nat := 4983230072969 + 3 ^ 40 * 1587639 * 2
def baseEnd_1587639 : Nat := 362320850143830706138261

theorem tailTrace_1587639 : CollatzResearch.WordTrace tailWord_1587639 prefixEnd_1587639 362320850143830706138261 := by
  unfold tailWord_1587639
  simp only [CollatzResearch.WordTrace]
  refine ⟨57905951495262524999181971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38603967663508349999454647 57905951495262524999181971)
  ·
    refine ⟨86858927242893787498772957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57905951495262524999181971 86858927242893787498772957)
    ·
      refine ⟨32572097716085170312039859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86858927242893787498772957 32572097716085170312039859)
      ·
        refine ⟨48858146574127755468059789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32572097716085170312039859 48858146574127755468059789)
        ·
          refine ⟨18321804965297908300522421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48858146574127755468059789 18321804965297908300522421)
          ·
            refine ⟨1717669215496678903173977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18321804965297908300522421 1717669215496678903173977)
            ·
              refine ⟨1288251911622509177380483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717669215496678903173977 1288251911622509177380483)
              ·
                refine ⟨1932377867433763766070725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288251911622509177380483 1932377867433763766070725)
                ·
                  refine ⟨362320850143830706138261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1932377867433763766070725 362320850143830706138261)
                  ·
                    rfl

theorem cell21_1587639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 4].length) (baseStart_1587639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587639 prefixEnd_1587639 := by exact prefixLift 1587639
  have htrace : WordTrace (prefixWord ++ tailWord_1587639) baseStart_1587639 baseEnd_1587639 := by
    simpa [prefixWord, tailWord_1587639, baseEnd_1587639] using wordTrace_append hprefix tailTrace_1587639
  have hstable : (prefixWord ++ tailWord_1587639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587639).length < 2 ^ (prefixWord ++ tailWord_1587639).sum := by decide
  have hdescent : baseEnd_1587639 < baseStart_1587639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587732 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1587732 : Nat := 118140960795 + 1587732 * 2 ^ 59
def prefixEnd_1587732 : Nat := 4983230072969 + 3 ^ 40 * 1587732 * 2
def baseEnd_1587732 : Nat := 362342074010883211088071

theorem tailTrace_1587732 : CollatzResearch.WordTrace tailWord_1587732 prefixEnd_1587732 362342074010883211088071 := by
  unfold tailWord_1587732
  simp only [CollatzResearch.WordTrace]
  refine ⟨28954671741962800941158725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38606228989283734588211633 28954671741962800941158725)
  ·
    refine ⟨5429000951618025176467261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28954671741962800941158725 5429000951618025176467261)
    ·
      refine ⟨2035875356856759441175223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5429000951618025176467261 2035875356856759441175223)
      ·
        refine ⟨3053813035285139161762835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035875356856759441175223 3053813035285139161762835)
        ·
          refine ⟨4580719552927708742644253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053813035285139161762835 4580719552927708742644253)
          ·
            refine ⟨1717769832347890778491595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4580719552927708742644253 1717769832347890778491595)
            ·
              refine ⟨2576654748521836167737393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717769832347890778491595 2576654748521836167737393)
              ·
                refine ⟨1932491061391377125803045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576654748521836167737393 1932491061391377125803045)
                ·
                  refine ⟨362342074010883211088071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1932491061391377125803045 362342074010883211088071)
                  ·
                    rfl

theorem cell21_1587732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1587732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587732 prefixEnd_1587732 := by exact prefixLift 1587732
  have htrace : WordTrace (prefixWord ++ tailWord_1587732) baseStart_1587732 baseEnd_1587732 := by
    simpa [prefixWord, tailWord_1587732, baseEnd_1587732] using wordTrace_append hprefix tailTrace_1587732
  have hstable : (prefixWord ++ tailWord_1587732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587732).length < 2 ^ (prefixWord ++ tailWord_1587732).sum := by decide
  have hdescent : baseEnd_1587732 < baseStart_1587732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587777 : List Nat := [1, 2, 5, 1, 1, 4, 1, 3, 3]
def baseStart_1587777 : Nat := 118140960795 + 1587777 * 2 ^ 59
def prefixEnd_1587777 : Nat := 4983230072969 + 3 ^ 40 * 1587777 * 2
def baseEnd_1587777 : Nat := 362352343623973132837979

theorem tailTrace_1587777 : CollatzResearch.WordTrace tailWord_1587777 prefixEnd_1587777 362352343623973132837979 := by
  unfold tailWord_1587777
  simp only [CollatzResearch.WordTrace]
  refine ⟨57910984768762574567705585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38607323179175049711803723 57910984768762574567705585)
  ·
    refine ⟨43433238576571930925779189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57910984768762574567705585 43433238576571930925779189)
    ·
      refine ⟨4071866116553618524291799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43433238576571930925779189 4071866116553618524291799)
      ·
        refine ⟨6107799174830427786437699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071866116553618524291799 6107799174830427786437699)
        ·
          refine ⟨9161698762245641679656549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6107799174830427786437699 9161698762245641679656549)
          ·
            refine ⟨1717818517921057814935603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9161698762245641679656549 1717818517921057814935603)
            ·
              refine ⟨2576727776881586722403405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717818517921057814935603 2576727776881586722403405)
              ·
                refine ⟨966272916330595020901277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2576727776881586722403405 966272916330595020901277)
                ·
                  refine ⟨362352343623973132837979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966272916330595020901277 362352343623973132837979)
                  ·
                    rfl

theorem cell21_1587777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_1587777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587777 prefixEnd_1587777 := by exact prefixLift 1587777
  have htrace : WordTrace (prefixWord ++ tailWord_1587777) baseStart_1587777 baseEnd_1587777 := by
    simpa [prefixWord, tailWord_1587777, baseEnd_1587777] using wordTrace_append hprefix tailTrace_1587777
  have hstable : (prefixWord ++ tailWord_1587777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587777).length < 2 ^ (prefixWord ++ tailWord_1587777).sum := by decide
  have hdescent : baseEnd_1587777 < baseStart_1587777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587940 : List Nat := [2, 3, 1, 1, 1, 4, 4, 5]
def baseStart_1587940 : Nat := 118140960795 + 1587940 * 2 ^ 59
def prefixEnd_1587940 : Nat := 4983230072969 + 3 ^ 40 * 1587940 * 2
def baseEnd_1587940 : Nat := 120796514148240357206993

theorem tailTrace_1587940 : CollatzResearch.WordTrace tailWord_1587940 prefixEnd_1587940 120796514148240357206993 := by
  unfold tailWord_1587940
  simp only [CollatzResearch.WordTrace]
  refine ⟨28958464933586026702944637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38611286578114702270592849 28958464933586026702944637)
  ·
    refine ⟨10859424350094760013604239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28958464933586026702944637 10859424350094760013604239)
    ·
      refine ⟨16289136525142140020406359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10859424350094760013604239 16289136525142140020406359)
      ·
        refine ⟨24433704787713210030609539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16289136525142140020406359 24433704787713210030609539)
        ·
          refine ⟨36650557181569815045914309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24433704787713210030609539 36650557181569815045914309)
          ·
            refine ⟨6871979471544340321108933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36650557181569815045914309 6871979471544340321108933)
            ·
              refine ⟨1288496150914563810207925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6871979471544340321108933 1288496150914563810207925)
              ·
                refine ⟨120796514148240357206993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1288496150914563810207925 120796514148240357206993)
                ·
                  rfl

theorem cell21_1587940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_1587940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587940 prefixEnd_1587940 := by exact prefixLift 1587940
  have htrace : WordTrace (prefixWord ++ tailWord_1587940) baseStart_1587940 baseEnd_1587940 := by
    simpa [prefixWord, tailWord_1587940, baseEnd_1587940] using wordTrace_append hprefix tailTrace_1587940
  have hstable : (prefixWord ++ tailWord_1587940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587940).length < 2 ^ (prefixWord ++ tailWord_1587940).sum := by decide
  have hdescent : baseEnd_1587940 < baseStart_1587940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587999 : List Nat := [1, 1, 2, 4, 2, 2, 2, 7]
def baseStart_1587999 : Nat := 118140960795 + 1587999 * 2 ^ 59
def prefixEnd_1587999 : Nat := 4983230072969 + 3 ^ 40 * 1587999 * 2
def baseEnd_1587999 : Nat := 120801002349516693379175

theorem tailTrace_1587999 : CollatzResearch.WordTrace tailWord_1587999 prefixEnd_1587999 120801002349516693379175 := by
  unfold tailWord_1587999
  simp only [CollatzResearch.WordTrace]
  refine ⟨57919081773958306482287051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38612721182638870988191367 57919081773958306482287051)
  ·
    refine ⟨86878622660937459723430577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57919081773958306482287051 86878622660937459723430577)
    ·
      refine ⟨65158966995703094792572933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86878622660937459723430577 65158966995703094792572933)
      ·
        refine ⟨12217306311694330273607425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65158966995703094792572933 12217306311694330273607425)
        ·
          refine ⟨9162979733770747705205569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12217306311694330273607425 9162979733770747705205569)
          ·
            refine ⟨6872234800328060778904177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9162979733770747705205569 6872234800328060778904177)
            ·
              refine ⟨5154176100246045584178133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6872234800328060778904177 5154176100246045584178133)
              ·
                refine ⟨120801002349516693379175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5154176100246045584178133 120801002349516693379175)
                ·
                  rfl

theorem cell21_1587999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 7].length) (baseStart_1587999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1587999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1587999 prefixEnd_1587999 := by exact prefixLift 1587999
  have htrace : WordTrace (prefixWord ++ tailWord_1587999) baseStart_1587999 baseEnd_1587999 := by
    simpa [prefixWord, tailWord_1587999, baseEnd_1587999] using wordTrace_append hprefix tailTrace_1587999
  have hstable : (prefixWord ++ tailWord_1587999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587999).length < 2 ^ (prefixWord ++ tailWord_1587999).sum := by decide
  have hdescent : baseEnd_1587999 < baseStart_1587999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588078 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_1588078 : Nat := 118140960795 + 1588078 * 2 ^ 59
def prefixEnd_1588078 : Nat := 4983230072969 + 3 ^ 40 * 1588078 * 2
def baseEnd_1588078 : Nat := 362421035924863498320697

theorem tailTrace_1588078 : CollatzResearch.WordTrace tailWord_1588078 prefixEnd_1588078 362421035924863498320697 := by
  unfold tailWord_1588078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240245392584012871801611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38614642093781401982941925 7240245392584012871801611)
  ·
    refine ⟨10860368088876019307702417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7240245392584012871801611 10860368088876019307702417)
    ·
      refine ⟨8145276066657014480776813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10860368088876019307702417 8145276066657014480776813)
      ·
        refine ⟨3054478524996380430291305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8145276066657014480776813 3054478524996380430291305)
        ·
          refine ⟨2290858893747285322718479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3054478524996380430291305 2290858893747285322718479)
          ·
            refine ⟨3436288340620927984077719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290858893747285322718479 3436288340620927984077719)
            ·
              refine ⟨5154432510931391976116579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436288340620927984077719 5154432510931391976116579)
              ·
                refine ⟨7731648766397087964174869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5154432510931391976116579 7731648766397087964174869)
                ·
                  refine ⟨362421035924863498320697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7731648766397087964174869 362421035924863498320697)
                  ·
                    rfl

theorem cell21_1588078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_1588078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588078 prefixEnd_1588078 := by exact prefixLift 1588078
  have htrace : WordTrace (prefixWord ++ tailWord_1588078) baseStart_1588078 baseEnd_1588078 := by
    simpa [prefixWord, tailWord_1588078, baseEnd_1588078] using wordTrace_append hprefix tailTrace_1588078
  have hstable : (prefixWord ++ tailWord_1588078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588078).length < 2 ^ (prefixWord ++ tailWord_1588078).sum := by decide
  have hdescent : baseEnd_1588078 < baseStart_1588078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588258 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1588258 : Nat := 118140960795 + 1588258 * 2 ^ 59
def prefixEnd_1588258 : Nat := 4983230072969 + 3 ^ 40 * 1588258 * 2
def baseEnd_1588258 : Nat := 362462114377223185320329

theorem tailTrace_1588258 : CollatzResearch.WordTrace tailWord_1588258 prefixEnd_1588258 362462114377223185320329 := by
  unfold tailWord_1588258
  simp only [CollatzResearch.WordTrace]
  refine ⟨14482132070004998428991357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38619018853346662477310285 14482132070004998428991357)
  ·
    refine ⟨5430799526251874410871759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14482132070004998428991357 5430799526251874410871759)
    ·
      refine ⟨8146199289377811616307639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5430799526251874410871759 8146199289377811616307639)
      ·
        refine ⟨12219298934066717424461459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8146199289377811616307639 12219298934066717424461459)
        ·
          refine ⟨18328948401100076136692189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12219298934066717424461459 18328948401100076136692189)
          ·
            refine ⟨6873355650412528551259571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18328948401100076136692189 6873355650412528551259571)
            ·
              refine ⟨10310033475618792826889357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6873355650412528551259571 10310033475618792826889357)
              ·
                refine ⟨3866262553357047310083509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10310033475618792826889357 3866262553357047310083509)
                ·
                  refine ⟨362462114377223185320329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3866262553357047310083509 362462114377223185320329)
                  ·
                    rfl

theorem cell21_1588258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1588258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588258 prefixEnd_1588258 := by exact prefixLift 1588258
  have htrace : WordTrace (prefixWord ++ tailWord_1588258) baseStart_1588258 baseEnd_1588258 := by
    simpa [prefixWord, tailWord_1588258, baseEnd_1588258] using wordTrace_append hprefix tailTrace_1588258
  have hstable : (prefixWord ++ tailWord_1588258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588258).length < 2 ^ (prefixWord ++ tailWord_1588258).sum := by decide
  have hdescent : baseEnd_1588258 < baseStart_1588258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588382 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1588382 : Nat := 118140960795 + 1588382 * 2 ^ 59
def prefixEnd_1588382 : Nat := 4983230072969 + 3 ^ 40 * 1588382 * 2
def baseEnd_1588382 : Nat := 362490412866626525253409

theorem tailTrace_1588382 : CollatzResearch.WordTrace tailWord_1588382 prefixEnd_1588382 362490412866626525253409 := by
  unfold tailWord_1588382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7241631366446345361684925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38622033954380508595652933 7241631366446345361684925)
  ·
    refine ⟨2715611762417379510631847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7241631366446345361684925 2715611762417379510631847)
    ·
      refine ⟨4073417643626069265947771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2715611762417379510631847 4073417643626069265947771)
      ·
        refine ⟨6110126465439103898921657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073417643626069265947771 6110126465439103898921657)
        ·
          refine ⟨4582594849079327924191243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6110126465439103898921657 4582594849079327924191243)
          ·
            refine ⟨6873892273618991886286865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582594849079327924191243 6873892273618991886286865)
            ·
              refine ⟨5155419205214243914715149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6873892273618991886286865 5155419205214243914715149)
              ·
                refine ⟨1933282201955341468018181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5155419205214243914715149 1933282201955341468018181)
                ·
                  refine ⟨362490412866626525253409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1933282201955341468018181 362490412866626525253409)
                  ·
                    rfl

theorem cell21_1588382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1588382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588382 prefixEnd_1588382 := by exact prefixLift 1588382
  have htrace : WordTrace (prefixWord ++ tailWord_1588382) baseStart_1588382 baseEnd_1588382 := by
    simpa [prefixWord, tailWord_1588382, baseEnd_1588382] using wordTrace_append hprefix tailTrace_1588382
  have hstable : (prefixWord ++ tailWord_1588382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588382).length < 2 ^ (prefixWord ++ tailWord_1588382).sum := by decide
  have hdescent : baseEnd_1588382 < baseStart_1588382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588537 : List Nat := [1, 2, 1, 6, 2, 2, 2, 2, 3]
def baseStart_1588537 : Nat := 118140960795 + 1588537 * 2 ^ 59
def prefixEnd_1588537 : Nat := 4983230072969 + 3 ^ 40 * 1588537 * 2
def baseEnd_1588537 : Nat := 362525785978380700169759

theorem tailTrace_1588537 : CollatzResearch.WordTrace tailWord_1588537 prefixEnd_1588537 362525785978380700169759 := by
  unfold tailWord_1588537
  simp only [CollatzResearch.WordTrace]
  refine ⟨57938704246009224365371865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38625802830672816243581243 57938704246009224365371865)
  ·
    refine ⟨43454028184506918274028899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57938704246009224365371865 43454028184506918274028899)
    ·
      refine ⟨65181042276760377411043349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43454028184506918274028899 65181042276760377411043349)
      ·
        refine ⟨3055361356723142691142657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65181042276760377411043349 3055361356723142691142657)
        ·
          refine ⟨2291521017542357018356993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3055361356723142691142657 2291521017542357018356993)
          ·
            refine ⟨1718640763156767763767745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2291521017542357018356993 1718640763156767763767745)
            ·
              refine ⟨1288980572367575822825809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718640763156767763767745 1288980572367575822825809)
              ·
                refine ⟨966735429275681867119357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288980572367575822825809 966735429275681867119357)
                ·
                  refine ⟨362525785978380700169759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966735429275681867119357 362525785978380700169759)
                  ·
                    rfl

theorem cell21_1588537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_1588537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588537 prefixEnd_1588537 := by exact prefixLift 1588537
  have htrace : WordTrace (prefixWord ++ tailWord_1588537) baseStart_1588537 baseEnd_1588537 := by
    simpa [prefixWord, tailWord_1588537, baseEnd_1588537] using wordTrace_append hprefix tailTrace_1588537
  have hstable : (prefixWord ++ tailWord_1588537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588537).length < 2 ^ (prefixWord ++ tailWord_1588537).sum := by decide
  have hdescent : baseEnd_1588537 < baseStart_1588537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588548 : List Nat := [2, 3, 4, 1, 1, 1, 3, 6]
def baseStart_1588548 : Nat := 118140960795 + 1588548 * 2 ^ 59
def prefixEnd_1588548 : Nat := 4983230072969 + 3 ^ 40 * 1588548 * 2
def baseEnd_1588548 : Nat := 120842765442749041828801

theorem tailTrace_1588548 : CollatzResearch.WordTrace tailWord_1588548 prefixEnd_1588548 120842765442749041828801 := by
  unfold tailWord_1588548
  simp only [CollatzResearch.WordTrace]
  refine ⟨28969552724484686622011149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38626070299312915496014865 28969552724484686622011149)
  ·
    refine ⟨10863582271681757483254181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28969552724484686622011149 10863582271681757483254181)
    ·
      refine ⟨2036921675940329528110159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10863582271681757483254181 2036921675940329528110159)
      ·
        refine ⟨3055382513910494292165239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036921675940329528110159 3055382513910494292165239)
        ·
          refine ⟨4583073770865741438247859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055382513910494292165239 4583073770865741438247859)
          ·
            refine ⟨6874610656298612157371789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583073770865741438247859 6874610656298612157371789)
            ·
              refine ⟨2577978996111979559014421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6874610656298612157371789 2577978996111979559014421)
              ·
                refine ⟨120842765442749041828801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2577978996111979559014421 120842765442749041828801)
                ·
                  rfl

theorem cell21_1588548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_1588548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588548 prefixEnd_1588548 := by exact prefixLift 1588548
  have htrace : WordTrace (prefixWord ++ tailWord_1588548) baseStart_1588548 baseEnd_1588548 := by
    simpa [prefixWord, tailWord_1588548, baseEnd_1588548] using wordTrace_append hprefix tailTrace_1588548
  have hstable : (prefixWord ++ tailWord_1588548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588548).length < 2 ^ (prefixWord ++ tailWord_1588548).sum := by decide
  have hdescent : baseEnd_1588548 < baseStart_1588548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588579 : List Nat := [1, 1, 1, 5, 2, 3, 2, 3, 3]
def baseStart_1588579 : Nat := 118140960795 + 1588579 * 2 ^ 59
def prefixEnd_1588579 : Nat := 4983230072969 + 3 ^ 40 * 1588579 * 2
def baseEnd_1588579 : Nat := 362535370950597960469673

theorem tailTrace_1588579 : CollatzResearch.WordTrace tailWord_1588579 prefixEnd_1588579 362535370950597960469673 := by
  unfold tailWord_1588579
  simp only [CollatzResearch.WordTrace]
  refine ⟨57940236111857065538400791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38626824074571377025600527 57940236111857065538400791)
  ·
    refine ⟨86910354167785598307601187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57940236111857065538400791 86910354167785598307601187)
    ·
      refine ⟨130365531251678397461401781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86910354167785598307601187 130365531251678397461401781)
      ·
        refine ⟨12221768554844849762006417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130365531251678397461401781 12221768554844849762006417)
        ·
          refine ⟨9166326416133637321504813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12221768554844849762006417 9166326416133637321504813)
          ·
            refine ⟨3437372406050113995564305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9166326416133637321504813 3437372406050113995564305)
            ·
              refine ⟨2578029304537585496673229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3437372406050113995564305 2578029304537585496673229)
              ·
                refine ⟨966760989201594561252461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2578029304537585496673229 966760989201594561252461)
                ·
                  refine ⟨362535370950597960469673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966760989201594561252461 362535370950597960469673)
                  ·
                    rfl

theorem cell21_1588579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 3].length) (baseStart_1588579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588579 prefixEnd_1588579 := by exact prefixLift 1588579
  have htrace : WordTrace (prefixWord ++ tailWord_1588579) baseStart_1588579 baseEnd_1588579 := by
    simpa [prefixWord, tailWord_1588579, baseEnd_1588579] using wordTrace_append hprefix tailTrace_1588579
  have hstable : (prefixWord ++ tailWord_1588579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588579).length < 2 ^ (prefixWord ++ tailWord_1588579).sum := by decide
  have hdescent : baseEnd_1588579 < baseStart_1588579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588717 : List Nat := [1, 5, 1, 3, 3, 1, 1, 6]
def baseStart_1588717 : Nat := 118140960795 + 1588717 * 2 ^ 59
def prefixEnd_1588717 : Nat := 4983230072969 + 3 ^ 40 * 1588717 * 2
def baseEnd_1588717 : Nat := 120855621476913462389797

theorem tailTrace_1588717 : CollatzResearch.WordTrace tailWord_1588717 prefixEnd_1588717 120855621476913462389797 := by
  unfold tailWord_1588717
  simp only [CollatzResearch.WordTrace]
  refine ⟨57945269385357115106924405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38630179590238076737949603 57945269385357115106924405)
  ·
    refine ⟨5432369004877229541274163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57945269385357115106924405 5432369004877229541274163)
    ·
      refine ⟨8148553507315844311911245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5432369004877229541274163 8148553507315844311911245)
      ·
        refine ⟨3055707565243441616966717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8148553507315844311911245 3055707565243441616966717)
        ·
          refine ⟨1145890336966290606362519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3055707565243441616966717 1145890336966290606362519)
          ·
            refine ⟨1718835505449435909543779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145890336966290606362519 1718835505449435909543779)
            ·
              refine ⟨2578253258174153864315669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718835505449435909543779 2578253258174153864315669)
              ·
                refine ⟨120855621476913462389797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2578253258174153864315669 120855621476913462389797)
                ·
                  rfl

theorem cell21_1588717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 6].length) (baseStart_1588717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588717 prefixEnd_1588717 := by exact prefixLift 1588717
  have htrace : WordTrace (prefixWord ++ tailWord_1588717) baseStart_1588717 baseEnd_1588717 := by
    simpa [prefixWord, tailWord_1588717, baseEnd_1588717] using wordTrace_append hprefix tailTrace_1588717
  have hstable : (prefixWord ++ tailWord_1588717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588717).length < 2 ^ (prefixWord ++ tailWord_1588717).sum := by decide
  have hdescent : baseEnd_1588717 < baseStart_1588717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588728 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_1588728 : Nat := 118140960795 + 1588728 * 2 ^ 59
def prefixEnd_1588728 : Nat := 4983230072969 + 3 ^ 40 * 1588728 * 2
def baseEnd_1588728 : Nat := 362569374780606812486035

theorem tailTrace_1588728 : CollatzResearch.WordTrace tailWord_1588728 prefixEnd_1588728 362569374780606812486035 := by
  unfold tailWord_1588728
  simp only [CollatzResearch.WordTrace]
  refine ⟨28972835294158631992787419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38630447058878175990383225 28972835294158631992787419)
  ·
    refine ⟨43459252941237947989181129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28972835294158631992787419 43459252941237947989181129)
    ·
      refine ⟨32594439705928460991885847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43459252941237947989181129 32594439705928460991885847)
      ·
        refine ⟨48891659558892691487828771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32594439705928460991885847 48891659558892691487828771)
        ·
          refine ⟨73337489338339037231743157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48891659558892691487828771 73337489338339037231743157)
          ·
            refine ⟨6875389625469284740475921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73337489338339037231743157 6875389625469284740475921)
            ·
              refine ⟨5156542219101963555356941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6875389625469284740475921 5156542219101963555356941)
              ·
                refine ⟨1933703332163236333258853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5156542219101963555356941 1933703332163236333258853)
                ·
                  refine ⟨362569374780606812486035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1933703332163236333258853 362569374780606812486035)
                  ·
                    rfl

theorem cell21_1588728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_1588728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588728 prefixEnd_1588728 := by exact prefixLift 1588728
  have htrace : WordTrace (prefixWord ++ tailWord_1588728) baseStart_1588728 baseEnd_1588728 := by
    simpa [prefixWord, tailWord_1588728, baseEnd_1588728] using wordTrace_append hprefix tailTrace_1588728
  have hstable : (prefixWord ++ tailWord_1588728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588728).length < 2 ^ (prefixWord ++ tailWord_1588728).sum := by decide
  have hdescent : baseEnd_1588728 < baseStart_1588728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588818 : List Nat := [3, 2, 2, 1, 2, 2, 9]
def baseStart_1588818 : Nat := 118140960795 + 1588818 * 2 ^ 59
def prefixEnd_1588818 : Nat := 4983230072969 + 3 ^ 40 * 1588818 * 2
def baseEnd_1588818 : Nat := 40287768222976295109539

theorem tailTrace_1588818 : CollatzResearch.WordTrace tailWord_1588818 prefixEnd_1588818 40287768222976295109539 := by
  unfold tailWord_1588818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14487238289497802339087777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38632635438660806237567405 14487238289497802339087777)
  ·
    refine ⟨10865428717123351754315833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14487238289497802339087777 10865428717123351754315833)
    ·
      refine ⟨8149071537842513815736875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10865428717123351754315833 8149071537842513815736875)
      ·
        refine ⟨12223607306763770723605313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8149071537842513815736875 12223607306763770723605313)
        ·
          refine ⟨9167705480072828042703985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12223607306763770723605313 9167705480072828042703985)
          ·
            refine ⟨6875779110054621032027989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9167705480072828042703985 6875779110054621032027989)
            ·
              refine ⟨40287768222976295109539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6875779110054621032027989 40287768222976295109539)
              ·
                rfl

theorem cell21_1588818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 9].length) (baseStart_1588818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588818 prefixEnd_1588818 := by exact prefixLift 1588818
  have htrace : WordTrace (prefixWord ++ tailWord_1588818) baseStart_1588818 baseEnd_1588818 := by
    simpa [prefixWord, tailWord_1588818, baseEnd_1588818] using wordTrace_append hprefix tailTrace_1588818
  have hstable : (prefixWord ++ tailWord_1588818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588818).length < 2 ^ (prefixWord ++ tailWord_1588818).sum := by decide
  have hdescent : baseEnd_1588818 < baseStart_1588818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588877 : List Nat := [1, 20]
def baseStart_1588877 : Nat := 118140960795 + 1588877 * 2 ^ 59
def prefixEnd_1588877 : Nat := 4983230072969 + 3 ^ 40 * 1588877 * 2
def baseEnd_1588877 : Nat := 165799441522915255831

theorem tailTrace_1588877 : CollatzResearch.WordTrace tailWord_1588877 prefixEnd_1588877 165799441522915255831 := by
  unfold tailWord_1588877
  simp only [CollatzResearch.WordTrace]
  refine ⟨57951105064777462432748885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38634070043184974955165923 57951105064777462432748885)
  ·
    refine ⟨165799441522915255831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 20 57951105064777462432748885 165799441522915255831)
    ·
      rfl

theorem cell21_1588877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 20].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 20].length) (baseStart_1588877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588877 prefixEnd_1588877 := by exact prefixLift 1588877
  have htrace : WordTrace (prefixWord ++ tailWord_1588877) baseStart_1588877 baseEnd_1588877 := by
    simpa [prefixWord, tailWord_1588877, baseEnd_1588877] using wordTrace_append hprefix tailTrace_1588877
  have hstable : (prefixWord ++ tailWord_1588877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588877).length < 2 ^ (prefixWord ++ tailWord_1588877).sum := by decide
  have hdescent : baseEnd_1588877 < baseStart_1588877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588942 : List Nat := [4, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_1588942 : Nat := 118140960795 + 1588942 * 2 ^ 59
def prefixEnd_1588942 : Nat := 4983230072969 + 3 ^ 40 * 1588942 * 2
def baseEnd_1588942 : Nat := 362618212496189995918931

theorem tailTrace_1588942 : CollatzResearch.WordTrace tailWord_1588942 prefixEnd_1588942 362618212496189995918931 := by
  unfold tailWord_1588942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7244184476192747316733135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38635650539694652355910053 7244184476192747316733135)
  ·
    refine ⟨10866276714289120975099703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7244184476192747316733135 10866276714289120975099703)
    ·
      refine ⟨16299415071433681462649555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10866276714289120975099703 16299415071433681462649555)
      ·
        refine ⟨24449122607150522193974333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16299415071433681462649555 24449122607150522193974333)
        ·
          refine ⟨9168420977681445822740375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24449122607150522193974333 9168420977681445822740375)
          ·
            refine ⟨13752631466522168734110563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168420977681445822740375 13752631466522168734110563)
            ·
              refine ⟨20628947199783253101165845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13752631466522168734110563 20628947199783253101165845)
              ·
                refine ⟨966981899989839989117149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20628947199783253101165845 966981899989839989117149)
                ·
                  refine ⟨362618212496189995918931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966981899989839989117149 362618212496189995918931)
                  ·
                    rfl

theorem cell21_1588942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_1588942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1588942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1588942 prefixEnd_1588942 := by exact prefixLift 1588942
  have htrace : WordTrace (prefixWord ++ tailWord_1588942) baseStart_1588942 baseEnd_1588942 := by
    simpa [prefixWord, tailWord_1588942, baseEnd_1588942] using wordTrace_append hprefix tailTrace_1588942
  have hstable : (prefixWord ++ tailWord_1588942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588942).length < 2 ^ (prefixWord ++ tailWord_1588942).sum := by decide
  have hdescent : baseEnd_1588942 < baseStart_1588942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589077 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 5]
def baseStart_1589077 : Nat := 118140960795 + 1589077 * 2 ^ 59
def prefixEnd_1589077 : Nat := 4983230072969 + 3 ^ 40 * 1589077 * 2
def baseEnd_1589077 : Nat := 362649021335459761168655

theorem tailTrace_1589077 : CollatzResearch.WordTrace tailWord_1589077 prefixEnd_1589077 362649021335459761168655 := by
  unfold tailWord_1589077
  simp only [CollatzResearch.WordTrace]
  refine ⟨57958399664052896590029485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38638933109368597726686323 57958399664052896590029485)
  ·
    refine ⟨21734399874019836221261057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57958399664052896590029485 21734399874019836221261057)
    ·
      refine ⟨16300799905514877165945793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21734399874019836221261057 16300799905514877165945793)
      ·
        refine ⟨12225599929136157874459345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16300799905514877165945793 12225599929136157874459345)
        ·
          refine ⟨9169199946852118405844509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12225599929136157874459345 9169199946852118405844509)
          ·
            refine ⟨3438449980069544402191691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9169199946852118405844509 3438449980069544402191691)
            ·
              refine ⟨5157674970104316603287537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3438449980069544402191691 5157674970104316603287537)
              ·
                refine ⟨3868256227578237452465653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5157674970104316603287537 3868256227578237452465653)
                ·
                  refine ⟨362649021335459761168655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3868256227578237452465653 362649021335459761168655)
                  ·
                    rfl

theorem cell21_1589077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_1589077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589077 prefixEnd_1589077 := by exact prefixLift 1589077
  have htrace : WordTrace (prefixWord ++ tailWord_1589077) baseStart_1589077 baseEnd_1589077 := by
    simpa [prefixWord, tailWord_1589077, baseEnd_1589077] using wordTrace_append hprefix tailTrace_1589077
  have hstable : (prefixWord ++ tailWord_1589077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589077).length < 2 ^ (prefixWord ++ tailWord_1589077).sum := by decide
  have hdescent : baseEnd_1589077 < baseStart_1589077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589105 : List Nat := [1, 2, 2, 2, 1, 3, 10]
def baseStart_1589105 : Nat := 118140960795 + 1589105 * 2 ^ 59
def prefixEnd_1589105 : Nat := 4983230072969 + 3 ^ 40 * 1589105 * 2
def baseEnd_1589105 : Nat := 40295045701881992744659

theorem tailTrace_1589105 : CollatzResearch.WordTrace tailWord_1589105 prefixEnd_1589105 40295045701881992744659 := by
  unfold tailWord_1589105
  simp only [CollatzResearch.WordTrace]
  refine ⟨57959420907951457372048769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38639613938634304914699179 57959420907951457372048769)
  ·
    refine ⟨43469565680963593029036577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57959420907951457372048769 43469565680963593029036577)
    ·
      refine ⟨32602174260722694771777433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43469565680963593029036577 32602174260722694771777433)
      ·
        refine ⟨24451630695542021078833075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32602174260722694771777433 24451630695542021078833075)
        ·
          refine ⟨36677446043313031618249613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24451630695542021078833075 36677446043313031618249613)
          ·
            refine ⟨13754042266242386856843605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36677446043313031618249613 13754042266242386856843605)
            ·
              refine ⟨40295045701881992744659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13754042266242386856843605 40295045701881992744659)
              ·
                rfl

theorem cell21_1589105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 10].length) (baseStart_1589105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589105 prefixEnd_1589105 := by exact prefixLift 1589105
  have htrace : WordTrace (prefixWord ++ tailWord_1589105) baseStart_1589105 baseEnd_1589105 := by
    simpa [prefixWord, tailWord_1589105, baseEnd_1589105] using wordTrace_append hprefix tailTrace_1589105
  have hstable : (prefixWord ++ tailWord_1589105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589105).length < 2 ^ (prefixWord ++ tailWord_1589105).sum := by decide
  have hdescent : baseEnd_1589105 < baseStart_1589105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589167 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 4]
def baseStart_1589167 : Nat := 118140960795 + 1589167 * 2 ^ 59
def prefixEnd_1589167 : Nat := 4983230072969 + 3 ^ 40 * 1589167 * 2
def baseEnd_1589167 : Nat := 362669560561639604668471

theorem tailTrace_1589167 : CollatzResearch.WordTrace tailWord_1589167 prefixEnd_1589167 362669560561639604668471 := by
  unfold tailWord_1589167
  simp only [CollatzResearch.WordTrace]
  refine ⟨57961682233726841960805755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38641121489151227973870503 57961682233726841960805755)
  ·
    refine ⟨86942523350590262941208633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57961682233726841960805755 86942523350590262941208633)
    ·
      refine ⟨65206892512942697205906475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86942523350590262941208633 65206892512942697205906475)
      ·
        refine ⟨97810338769414045808859713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65206892512942697205906475 97810338769414045808859713)
        ·
          refine ⟨73357754077060534356644785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97810338769414045808859713 73357754077060534356644785)
          ·
            refine ⟨55018315557795400767483589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73357754077060534356644785 55018315557795400767483589)
            ·
              refine ⟨10315934167086637643903173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55018315557795400767483589 10315934167086637643903173)
              ·
                refine ⟨1934237656328744558231845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10315934167086637643903173 1934237656328744558231845)
                ·
                  refine ⟨362669560561639604668471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1934237656328744558231845 362669560561639604668471)
                  ·
                    rfl

theorem cell21_1589167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 4].length) (baseStart_1589167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589167 prefixEnd_1589167 := by exact prefixLift 1589167
  have htrace : WordTrace (prefixWord ++ tailWord_1589167) baseStart_1589167 baseEnd_1589167 := by
    simpa [prefixWord, tailWord_1589167, baseEnd_1589167] using wordTrace_append hprefix tailTrace_1589167
  have hstable : (prefixWord ++ tailWord_1589167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589167).length < 2 ^ (prefixWord ++ tailWord_1589167).sum := by decide
  have hdescent : baseEnd_1589167 < baseStart_1589167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589218 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1589218 : Nat := 118140960795 + 1589218 * 2 ^ 59
def prefixEnd_1589218 : Nat := 4983230072969 + 3 ^ 40 * 1589218 * 2
def baseEnd_1589218 : Nat := 362681199456474849318367

theorem tailTrace_1589218 : CollatzResearch.WordTrace tailWord_1589218 prefixEnd_1589218 362681199456474849318367 := by
  unfold tailWord_1589218
  simp only [CollatzResearch.WordTrace]
  refine ⟨14490885589135519417728077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38642361571028051780608205 14490885589135519417728077)
  ·
    refine ⟨5434082095925819781648029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14490885589135519417728077 5434082095925819781648029)
    ·
      refine ⟨2037780785972182418118011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5434082095925819781648029 2037780785972182418118011)
      ·
        refine ⟨3056671178958273627177017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037780785972182418118011 3056671178958273627177017)
        ·
          refine ⟨2292503384218705220382763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3056671178958273627177017 2292503384218705220382763)
          ·
            refine ⟨3438755076328057830574145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292503384218705220382763 3438755076328057830574145)
            ·
              refine ⟨2579066307246043372930609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3438755076328057830574145 2579066307246043372930609)
              ·
                refine ⟨1934299730434532529697957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2579066307246043372930609 1934299730434532529697957)
                ·
                  refine ⟨362681199456474849318367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1934299730434532529697957 362681199456474849318367)
                  ·
                    rfl

theorem cell21_1589218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1589218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589218 prefixEnd_1589218 := by exact prefixLift 1589218
  have htrace : WordTrace (prefixWord ++ tailWord_1589218) baseStart_1589218 baseEnd_1589218 := by
    simpa [prefixWord, tailWord_1589218, baseEnd_1589218] using wordTrace_append hprefix tailTrace_1589218
  have hstable : (prefixWord ++ tailWord_1589218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589218).length < 2 ^ (prefixWord ++ tailWord_1589218).sum := by decide
  have hdescent : baseEnd_1589218 < baseStart_1589218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589243 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 4]
def baseStart_1589243 : Nat := 118140960795 + 1589243 * 2 ^ 59
def prefixEnd_1589243 : Nat := 4983230072969 + 3 ^ 40 * 1589243 * 2
def baseEnd_1589243 : Nat := 362686904797080361401649

theorem tailTrace_1589243 : CollatzResearch.WordTrace tailWord_1589243 prefixEnd_1589243 362686904797080361401649 := by
  unfold tailWord_1589243
  simp only [CollatzResearch.WordTrace]
  refine ⟨57964454181451506940572383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38642969454301004627048255 57964454181451506940572383)
  ·
    refine ⟨86946681272177260410858575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57964454181451506940572383 86946681272177260410858575)
    ·
      refine ⟨130420021908265890616287863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86946681272177260410858575 130420021908265890616287863)
      ·
        refine ⟨195630032862398835924431795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130420021908265890616287863 195630032862398835924431795)
        ·
          refine ⟨293445049293598253886647693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195630032862398835924431795 293445049293598253886647693)
          ·
            refine ⟨110041893485099345207492885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293445049293598253886647693 110041893485099345207492885)
            ·
              refine ⟨5158213757114031806601229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110041893485099345207492885 5158213757114031806601229)
              ·
                refine ⟨1934330158917761927475461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5158213757114031806601229 1934330158917761927475461)
                ·
                  refine ⟨362686904797080361401649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1934330158917761927475461 362686904797080361401649)
                  ·
                    rfl

theorem cell21_1589243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 4].length) (baseStart_1589243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589243 prefixEnd_1589243 := by exact prefixLift 1589243
  have htrace : WordTrace (prefixWord ++ tailWord_1589243) baseStart_1589243 baseEnd_1589243 := by
    simpa [prefixWord, tailWord_1589243, baseEnd_1589243] using wordTrace_append hprefix tailTrace_1589243
  have hstable : (prefixWord ++ tailWord_1589243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589243).length < 2 ^ (prefixWord ++ tailWord_1589243).sum := by decide
  have hdescent : baseEnd_1589243 < baseStart_1589243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589246 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1589246 : Nat := 118140960795 + 1589246 * 2 ^ 59
def prefixEnd_1589246 : Nat := 4983230072969 + 3 ^ 40 * 1589246 * 2
def baseEnd_1589246 : Nat := 362687589437953022851643

theorem tailTrace_1589246 : CollatzResearch.WordTrace tailWord_1589246 prefixEnd_1589246 362687589437953022851643 := by
  unfold tailWord_1589246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7245570450055079806616449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38643042400293758968621061 7245570450055079806616449)
  ·
    refine ⟨5434177837541309854962337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7245570450055079806616449 5434177837541309854962337)
    ·
      refine ⟨4075633378155982391221753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5434177837541309854962337 4075633378155982391221753)
      ·
        refine ⟨3056725033616986793416315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4075633378155982391221753 3056725033616986793416315)
        ·
          refine ⟨4585087550425480190124473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056725033616986793416315 4585087550425480190124473)
          ·
            refine ⟨3438815662819110142593355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4585087550425480190124473 3438815662819110142593355)
            ·
              refine ⟨5158223494228665213890033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3438815662819110142593355 5158223494228665213890033)
              ·
                refine ⟨3868667620671498910417525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5158223494228665213890033 3868667620671498910417525)
                ·
                  refine ⟨362687589437953022851643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3868667620671498910417525 362687589437953022851643)
                  ·
                    rfl

theorem cell21_1589246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1589246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589246 prefixEnd_1589246 := by exact prefixLift 1589246
  have htrace : WordTrace (prefixWord ++ tailWord_1589246) baseStart_1589246 baseEnd_1589246 := by
    simpa [prefixWord, tailWord_1589246, baseEnd_1589246] using wordTrace_append hprefix tailTrace_1589246
  have hstable : (prefixWord ++ tailWord_1589246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589246).length < 2 ^ (prefixWord ++ tailWord_1589246).sum := by decide
  have hdescent : baseEnd_1589246 < baseStart_1589246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589277 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 4]
def baseStart_1589277 : Nat := 118140960795 + 1589277 * 2 ^ 59
def prefixEnd_1589277 : Nat := 4983230072969 + 3 ^ 40 * 1589277 * 2
def baseEnd_1589277 : Nat := 362694664060303857834913

theorem tailTrace_1589277 : CollatzResearch.WordTrace tailWord_1589277 prefixEnd_1589277 362694664060303857834913 := by
  unfold tailWord_1589277
  simp only [CollatzResearch.WordTrace]
  refine ⟨57965694263328330747310085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38643796175552220498206723 57965694263328330747310085)
  ·
    refine ⟨10868567674374062015120641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57965694263328330747310085 10868567674374062015120641)
    ·
      refine ⟨8151425755780546511340481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10868567674374062015120641 8151425755780546511340481)
      ·
        refine ⟨6113569316835409883505361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8151425755780546511340481 6113569316835409883505361)
        ·
          refine ⟨4585176987626557412629021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6113569316835409883505361 4585176987626557412629021)
          ·
            refine ⟨1719441370359959029735883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4585176987626557412629021 1719441370359959029735883)
            ·
              refine ⟨2579162055539938544603825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719441370359959029735883 2579162055539938544603825)
              ·
                refine ⟨1934371541654953908452869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2579162055539938544603825 1934371541654953908452869)
                ·
                  refine ⟨362694664060303857834913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1934371541654953908452869 362694664060303857834913)
                  ·
                    rfl

theorem cell21_1589277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_1589277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589277 prefixEnd_1589277 := by exact prefixLift 1589277
  have htrace : WordTrace (prefixWord ++ tailWord_1589277) baseStart_1589277 baseEnd_1589277 := by
    simpa [prefixWord, tailWord_1589277, baseEnd_1589277] using wordTrace_append hprefix tailTrace_1589277
  have hstable : (prefixWord ++ tailWord_1589277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589277).length < 2 ^ (prefixWord ++ tailWord_1589277).sum := by decide
  have hdescent : baseEnd_1589277 < baseStart_1589277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589333 : List Nat := [1, 3, 2, 2, 1, 3, 9]
def baseStart_1589333 : Nat := 118140960795 + 1589333 * 2 ^ 59
def prefixEnd_1589333 : Nat := 4983230072969 + 3 ^ 40 * 1589333 * 2
def baseEnd_1589333 : Nat := 40300827113695578322385

theorem tailTrace_1589333 : CollatzResearch.WordTrace tailWord_1589333 prefixEnd_1589333 40300827113695578322385 := by
  unfold tailWord_1589333
  simp only [CollatzResearch.WordTrace]
  refine ⟨57967736751125452311348653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38645157834083634874232435 57967736751125452311348653)
  ·
    refine ⟨21737901281672044616755745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57967736751125452311348653 21737901281672044616755745)
    ·
      refine ⟨16303425961254033462566809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21737901281672044616755745 16303425961254033462566809)
      ·
        refine ⟨12227569470940525096925107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16303425961254033462566809 12227569470940525096925107)
        ·
          refine ⟨18341354206410787645387661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12227569470940525096925107 18341354206410787645387661)
          ·
            refine ⟨6878007827404045367020373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18341354206410787645387661 6878007827404045367020373)
            ·
              refine ⟨40300827113695578322385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6878007827404045367020373 40300827113695578322385)
              ·
                rfl

theorem cell21_1589333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 9].length) (baseStart_1589333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589333 prefixEnd_1589333 := by exact prefixLift 1589333
  have htrace : WordTrace (prefixWord ++ tailWord_1589333) baseStart_1589333 baseEnd_1589333 := by
    simpa [prefixWord, tailWord_1589333, baseEnd_1589333] using wordTrace_append hprefix tailTrace_1589333
  have hstable : (prefixWord ++ tailWord_1589333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589333).length < 2 ^ (prefixWord ++ tailWord_1589333).sum := by decide
  have hdescent : baseEnd_1589333 < baseStart_1589333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589426 : List Nat := [3, 2, 1, 1, 1, 3, 5, 5]
def baseStart_1589426 : Nat := 118140960795 + 1589426 * 2 ^ 59
def prefixEnd_1589426 : Nat := 4983230072969 + 3 ^ 40 * 1589426 * 2
def baseEnd_1589426 : Nat := 120909555963437569950425

theorem tailTrace_1589426 : CollatzResearch.WordTrace tailWord_1589426 prefixEnd_1589426 120909555963437569950425 := by
  unfold tailWord_1589426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492782184947132298621033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38647419159859019462989421 14492782184947132298621033)
  ·
    refine ⟨10869586638710349223965775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14492782184947132298621033 10869586638710349223965775)
    ·
      refine ⟨16304379958065523835948663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10869586638710349223965775 16304379958065523835948663)
      ·
        refine ⟨24456569937098285753922995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16304379958065523835948663 24456569937098285753922995)
        ·
          refine ⟨36684854905647428630884493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24456569937098285753922995 36684854905647428630884493)
          ·
            refine ⟨13756820589617785736581685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36684854905647428630884493 13756820589617785736581685)
            ·
              refine ⟨1289701930276667412804533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13756820589617785736581685 1289701930276667412804533)
              ·
                refine ⟨120909555963437569950425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1289701930276667412804533 120909555963437569950425)
                ·
                  rfl

theorem cell21_1589426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_1589426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589426 prefixEnd_1589426 := by exact prefixLift 1589426
  have htrace : WordTrace (prefixWord ++ tailWord_1589426) baseStart_1589426 baseEnd_1589426 := by
    simpa [prefixWord, tailWord_1589426, baseEnd_1589426] using wordTrace_append hprefix tailTrace_1589426
  have hstable : (prefixWord ++ tailWord_1589426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589426).length < 2 ^ (prefixWord ++ tailWord_1589426).sum := by decide
  have hdescent : baseEnd_1589426 < baseStart_1589426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589457 : List Nat := [1, 2, 2, 1, 2, 2, 4, 4, 3]
def baseStart_1589457 : Nat := 118140960795 + 1589457 * 2 ^ 59
def prefixEnd_1589457 : Nat := 4983230072969 + 3 ^ 40 * 1589457 * 2
def baseEnd_1589457 : Nat := 362735742512663544834545

theorem tailTrace_1589457 : CollatzResearch.WordTrace tailWord_1589457 prefixEnd_1589457 362735742512663544834545 := by
  unfold tailWord_1589457
  simp only [CollatzResearch.WordTrace]
  refine ⟨57972259402676221488862625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38648172935117480992575083 57972259402676221488862625)
  ·
    refine ⟨43479194552007166116646969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57972259402676221488862625 43479194552007166116646969)
    ·
      refine ⟨32609395914005374587485227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43479194552007166116646969 32609395914005374587485227)
      ·
        refine ⟨48914093871008061881227841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32609395914005374587485227 48914093871008061881227841)
        ·
          refine ⟨36685570403256046410920881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48914093871008061881227841 36685570403256046410920881)
          ·
            refine ⟨27514177802442034808190661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36685570403256046410920881 27514177802442034808190661)
            ·
              refine ⟨5158908337957881526535749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27514177802442034808190661 5158908337957881526535749)
              ·
                refine ⟨967295313367102786225453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5158908337957881526535749 967295313367102786225453)
                ·
                  refine ⟨362735742512663544834545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967295313367102786225453 362735742512663544834545)
                  ·
                    rfl

theorem cell21_1589457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_1589457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589457 prefixEnd_1589457 := by exact prefixLift 1589457
  have htrace : WordTrace (prefixWord ++ tailWord_1589457) baseStart_1589457 baseEnd_1589457 := by
    simpa [prefixWord, tailWord_1589457, baseEnd_1589457] using wordTrace_append hprefix tailTrace_1589457
  have hstable : (prefixWord ++ tailWord_1589457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589457).length < 2 ^ (prefixWord ++ tailWord_1589457).sum := by decide
  have hdescent : baseEnd_1589457 < baseStart_1589457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589561 : List Nat := [1, 2, 1, 6, 1, 10]
def baseStart_1589561 : Nat := 118140960795 + 1589561 * 2 ^ 59
def prefixEnd_1589561 : Nat := 4983230072969 + 3 ^ 40 * 1589561 * 2
def baseEnd_1589561 : Nat := 13435536175169721300037

theorem tailTrace_1589561 : CollatzResearch.WordTrace tailWord_1589561 prefixEnd_1589561 13435536175169721300037 := by
  unfold tailWord_1589561
  simp only [CollatzResearch.WordTrace]
  refine ⟨57976052594299447250648537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38650701729532964833765691 57976052594299447250648537)
  ·
    refine ⟨43482039445724585437986403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57976052594299447250648537 43482039445724585437986403)
    ·
      refine ⟨65223059168586878156979605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43482039445724585437986403 65223059168586878156979605)
      ·
        refine ⟨3057330898527509913608419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65223059168586878156979605 3057330898527509913608419)
        ·
          refine ⟨4585996347791264870412629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057330898527509913608419 4585996347791264870412629)
          ·
            refine ⟨13435536175169721300037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4585996347791264870412629 13435536175169721300037)
            ·
              rfl

theorem cell21_1589561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 10].length) (baseStart_1589561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589561 prefixEnd_1589561 := by exact prefixLift 1589561
  have htrace : WordTrace (prefixWord ++ tailWord_1589561) baseStart_1589561 baseEnd_1589561 := by
    simpa [prefixWord, tailWord_1589561, baseEnd_1589561] using wordTrace_append hprefix tailTrace_1589561
  have hstable : (prefixWord ++ tailWord_1589561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589561).length < 2 ^ (prefixWord ++ tailWord_1589561).sum := by decide
  have hdescent : baseEnd_1589561 < baseStart_1589561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589609 : List Nat := [1, 2, 1, 1, 1, 3, 6, 3, 3]
def baseStart_1589609 : Nat := 118140960795 + 1589609 * 2 ^ 59
def prefixEnd_1589609 : Nat := 4983230072969 + 3 ^ 40 * 1589609 * 2
def baseEnd_1589609 : Nat := 362770430983545058300901

theorem tailTrace_1589609 : CollatzResearch.WordTrace tailWord_1589609 prefixEnd_1589609 362770430983545058300901 := by
  unfold tailWord_1589609
  simp only [CollatzResearch.WordTrace]
  refine ⟨57977803298125551448395881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38651868865417034298930587 57977803298125551448395881)
  ·
    refine ⟨43483352473594163586296911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57977803298125551448395881 43483352473594163586296911)
    ·
      refine ⟨65225028710391245379445367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43483352473594163586296911 65225028710391245379445367)
      ·
        refine ⟨97837543065586868069168051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65225028710391245379445367 97837543065586868069168051)
        ·
          refine ⟨146756314598380302103752077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97837543065586868069168051 146756314598380302103752077)
          ·
            refine ⟨55033617974392613288907029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146756314598380302103752077 55033617974392613288907029)
            ·
              refine ⟨2579700842549653747917517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55033617974392613288907029 2579700842549653747917517)
              ·
                refine ⟨967387815956120155469069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2579700842549653747917517 967387815956120155469069)
                ·
                  refine ⟨362770430983545058300901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967387815956120155469069 362770430983545058300901)
                  ·
                    rfl

theorem cell21_1589609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_1589609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589609 prefixEnd_1589609 := by exact prefixLift 1589609
  have htrace : WordTrace (prefixWord ++ tailWord_1589609) baseStart_1589609 baseEnd_1589609 := by
    simpa [prefixWord, tailWord_1589609, baseEnd_1589609] using wordTrace_append hprefix tailTrace_1589609
  have hstable : (prefixWord ++ tailWord_1589609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589609).length < 2 ^ (prefixWord ++ tailWord_1589609).sum := by decide
  have hdescent : baseEnd_1589609 < baseStart_1589609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589640 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_1589640 : Nat := 118140960795 + 1589640 * 2 ^ 59
def prefixEnd_1589640 : Nat := 4983230072969 + 3 ^ 40 * 1589640 * 2
def baseEnd_1589640 : Nat := 362777505605895893284171

theorem tailTrace_1589640 : CollatzResearch.WordTrace tailWord_1589640 prefixEnd_1589640 362777505605895893284171 := by
  unfold tailWord_1589640
  simp only [CollatzResearch.WordTrace]
  refine ⟨28989466980506621871387187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38652622640675495828516249 28989466980506621871387187)
  ·
    refine ⟨43484200470759932807080781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28989466980506621871387187 43484200470759932807080781)
    ·
      refine ⟨16306575176534974802655293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43484200470759932807080781 16306575176534974802655293)
      ·
        refine ⟨6114965691200615550995735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16306575176534974802655293 6114965691200615550995735)
        ·
          refine ⟨9172448536800923326493603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6114965691200615550995735 9172448536800923326493603)
          ·
            refine ⟨13758672805201384989740405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9172448536800923326493603 13758672805201384989740405)
            ·
              refine ⟨1289875575487629842788163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13758672805201384989740405 1289875575487629842788163)
              ·
                refine ⟨1934813363231444764182245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289875575487629842788163 1934813363231444764182245)
                ·
                  refine ⟨362777505605895893284171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1934813363231444764182245 362777505605895893284171)
                  ·
                    rfl

theorem cell21_1589640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_1589640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589640 prefixEnd_1589640 := by exact prefixLift 1589640
  have htrace : WordTrace (prefixWord ++ tailWord_1589640) baseStart_1589640 baseEnd_1589640 := by
    simpa [prefixWord, tailWord_1589640, baseEnd_1589640] using wordTrace_append hprefix tailTrace_1589640
  have hstable : (prefixWord ++ tailWord_1589640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589640).length < 2 ^ (prefixWord ++ tailWord_1589640).sum := by decide
  have hdescent : baseEnd_1589640 < baseStart_1589640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589682 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1589682 : Nat := 118140960795 + 1589682 * 2 ^ 59
def prefixEnd_1589682 : Nat := 4983230072969 + 3 ^ 40 * 1589682 * 2
def baseEnd_1589682 : Nat := 362787090578113153584085

theorem tailTrace_1589682 : CollatzResearch.WordTrace tailWord_1589682 prefixEnd_1589682 362787090578113153584085 := by
  unfold tailWord_1589682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14495116456715271228950825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38653643884574056610535533 14495116456715271228950825)
  ·
    refine ⟨10871337342536453421713119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14495116456715271228950825 10871337342536453421713119)
    ·
      refine ⟨16307006013804680132569679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10871337342536453421713119 16307006013804680132569679)
      ·
        refine ⟨24460509020707020198854519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16307006013804680132569679 24460509020707020198854519)
        ·
          refine ⟨36690763531060530298281779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24460509020707020198854519 36690763531060530298281779)
          ·
            refine ⟨55036145296590795447422669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36690763531060530298281779 55036145296590795447422669)
            ·
              refine ⟨20638554486221548292783501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55036145296590795447422669 20638554486221548292783501)
              ·
                refine ⟨7739457932333080609793813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20638554486221548292783501 7739457932333080609793813)
                ·
                  refine ⟨362787090578113153584085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7739457932333080609793813 362787090578113153584085)
                  ·
                    rfl

theorem cell21_1589682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1589682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589682 prefixEnd_1589682 := by exact prefixLift 1589682
  have htrace : WordTrace (prefixWord ++ tailWord_1589682) baseStart_1589682 baseEnd_1589682 := by
    simpa [prefixWord, tailWord_1589682, baseEnd_1589682] using wordTrace_append hprefix tailTrace_1589682
  have hstable : (prefixWord ++ tailWord_1589682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589682).length < 2 ^ (prefixWord ++ tailWord_1589682).sum := by decide
  have hdescent : baseEnd_1589682 < baseStart_1589682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589730 : List Nat := [3, 3, 3, 2, 10]
def baseStart_1589730 : Nat := 118140960795 + 1589730 * 2 ^ 59
def prefixEnd_1589730 : Nat := 4983230072969 + 3 ^ 40 * 1589730 * 2
def baseEnd_1589730 : Nat := 4478988207803404157827

theorem tailTrace_1589730 : CollatzResearch.WordTrace tailWord_1589730 prefixEnd_1589730 4478988207803404157827 := by
  unfold tailWord_1589730
  simp only [CollatzResearch.WordTrace]
  refine ⟨14495554132671797278387661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38654811020458126075700429 14495554132671797278387661)
  ·
    refine ⟨5435832799751923979395373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14495554132671797278387661 5435832799751923979395373)
    ·
      refine ⟨2038437299906971492273265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5435832799751923979395373 2038437299906971492273265)
      ·
        refine ⟨1528827974930228619204949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2038437299906971492273265 1528827974930228619204949)
        ·
          refine ⟨4478988207803404157827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1528827974930228619204949 4478988207803404157827)
          ·
            rfl

theorem cell21_1589730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 10].length) (baseStart_1589730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589730 prefixEnd_1589730 := by exact prefixLift 1589730
  have htrace : WordTrace (prefixWord ++ tailWord_1589730) baseStart_1589730 baseEnd_1589730 := by
    simpa [prefixWord, tailWord_1589730, baseEnd_1589730] using wordTrace_append hprefix tailTrace_1589730
  have hstable : (prefixWord ++ tailWord_1589730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589730).length < 2 ^ (prefixWord ++ tailWord_1589730).sum := by decide
  have hdescent : baseEnd_1589730 < baseStart_1589730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589789 : List Nat := [1, 4, 2, 2, 1, 3, 8]
def baseStart_1589789 : Nat := 118140960795 + 1589789 * 2 ^ 59
def prefixEnd_1589789 : Nat := 4983230072969 + 3 ^ 40 * 1589789 * 2
def baseEnd_1589789 : Nat := 40312389937322749477837

theorem tailTrace_1589789 : CollatzResearch.WordTrace tailWord_1589789 prefixEnd_1589789 40312389937322749477837 := by
  unfold tailWord_1589789
  simp only [CollatzResearch.WordTrace]
  refine ⟨57984368437473442189948421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38656245624982294793298947 57984368437473442189948421)
  ·
    refine ⟨10872069082026270410615329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57984368437473442189948421 10872069082026270410615329)
    ·
      refine ⟨8154051811519702807961497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10872069082026270410615329 8154051811519702807961497)
      ·
        refine ⟨6115538858639777105971123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8154051811519702807961497 6115538858639777105971123)
        ·
          refine ⟨9173308287959665658956685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6115538858639777105971123 9173308287959665658956685)
          ·
            refine ⟨3439990607984874622108757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9173308287959665658956685 3439990607984874622108757)
            ·
              refine ⟨40312389937322749477837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3439990607984874622108757 40312389937322749477837)
              ·
                rfl

theorem cell21_1589789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 8].length) (baseStart_1589789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589789 prefixEnd_1589789 := by exact prefixLift 1589789
  have htrace : WordTrace (prefixWord ++ tailWord_1589789) baseStart_1589789 baseEnd_1589789 := by
    simpa [prefixWord, tailWord_1589789, baseEnd_1589789] using wordTrace_append hprefix tailTrace_1589789
  have hstable : (prefixWord ++ tailWord_1589789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589789).length < 2 ^ (prefixWord ++ tailWord_1589789).sum := by decide
  have hdescent : baseEnd_1589789 < baseStart_1589789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589820 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_1589820 : Nat := 118140960795 + 1589820 * 2 ^ 59
def prefixEnd_1589820 : Nat := 4983230072969 + 3 ^ 40 * 1589820 * 2
def baseEnd_1589820 : Nat := 362818584058255580283803

theorem tailTrace_1589820 : CollatzResearch.WordTrace tailWord_1589820 prefixEnd_1589820 362818584058255580283803 := by
  unfold tailWord_1589820
  simp only [CollatzResearch.WordTrace]
  refine ⟨28992749550180567242163457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38656999400240756322884609 28992749550180567242163457)
  ·
    refine ⟨21744562162635425431622593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28992749550180567242163457 21744562162635425431622593)
    ·
      refine ⟨16308421621976569073716945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21744562162635425431622593 16308421621976569073716945)
      ·
        refine ⟨12231316216482426805287709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16308421621976569073716945 12231316216482426805287709)
        ·
          refine ⟨4586743581180910051982891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12231316216482426805287709 4586743581180910051982891)
          ·
            refine ⟨6880115371771365077974337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586743581180910051982891 6880115371771365077974337)
            ·
              refine ⟨5160086528828523808480753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6880115371771365077974337 5160086528828523808480753)
              ·
                refine ⟨3870064896621392856360565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5160086528828523808480753 3870064896621392856360565)
                ·
                  refine ⟨362818584058255580283803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3870064896621392856360565 362818584058255580283803)
                  ·
                    rfl

theorem cell21_1589820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_1589820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589820 prefixEnd_1589820 := by exact prefixLift 1589820
  have htrace : WordTrace (prefixWord ++ tailWord_1589820) baseStart_1589820 baseEnd_1589820 := by
    simpa [prefixWord, tailWord_1589820, baseEnd_1589820] using wordTrace_append hprefix tailTrace_1589820
  have hstable : (prefixWord ++ tailWord_1589820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589820).length < 2 ^ (prefixWord ++ tailWord_1589820).sum := by decide
  have hdescent : baseEnd_1589820 < baseStart_1589820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589834 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_1589834 : Nat := 118140960795 + 1589834 * 2 ^ 59
def prefixEnd_1589834 : Nat := 4983230072969 + 3 ^ 40 * 1589834 * 2
def baseEnd_1589834 : Nat := 362821779048994667050441

theorem tailTrace_1589834 : CollatzResearch.WordTrace tailWord_1589834 prefixEnd_1589834 362821779048994667050441 := by
  unfold tailWord_1589834
  simp only [CollatzResearch.WordTrace]
  refine ⟨14496502430577603718834139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38657339814873609916891037 14496502430577603718834139)
  ·
    refine ⟨21744753645866405578251209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14496502430577603718834139 21744753645866405578251209)
    ·
      refine ⟨16308565234399804183688407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21744753645866405578251209 16308565234399804183688407)
      ·
        refine ⟨24462847851599706275532611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16308565234399804183688407 24462847851599706275532611)
        ·
          refine ⟨36694271777399559413298917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24462847851599706275532611 36694271777399559413298917)
          ·
            refine ⟨6880175958262417389993547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36694271777399559413298917 6880175958262417389993547)
            ·
              refine ⟨10320263937393626084990321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880175958262417389993547 10320263937393626084990321)
              ·
                refine ⟨7740197953045219563742741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10320263937393626084990321 7740197953045219563742741)
                ·
                  refine ⟨362821779048994667050441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7740197953045219563742741 362821779048994667050441)
                  ·
                    rfl

theorem cell21_1589834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_1589834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589834 prefixEnd_1589834 := by exact prefixLift 1589834
  have htrace : WordTrace (prefixWord ++ tailWord_1589834) baseStart_1589834 baseEnd_1589834 := by
    simpa [prefixWord, tailWord_1589834, baseEnd_1589834] using wordTrace_append hprefix tailTrace_1589834
  have hstable : (prefixWord ++ tailWord_1589834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589834).length < 2 ^ (prefixWord ++ tailWord_1589834).sum := by decide
  have hdescent : baseEnd_1589834 < baseStart_1589834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589848 : List Nat := [2, 1, 2, 2, 1, 2, 11]
def baseStart_1589848 : Nat := 118140960795 + 1589848 * 2 ^ 59
def prefixEnd_1589848 : Nat := 4983230072969 + 3 ^ 40 * 1589848 * 2
def baseEnd_1589848 : Nat := 40313886004414861535231

theorem tailTrace_1589848 : CollatzResearch.WordTrace tailWord_1589848 prefixEnd_1589848 40313886004414861535231 := by
  unfold tailWord_1589848
  simp only [CollatzResearch.WordTrace]
  refine ⟨28993260172129847633173099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38657680229506463510897465 28993260172129847633173099)
  ·
    refine ⟨43489890258194771449759649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28993260172129847633173099 43489890258194771449759649)
    ·
      refine ⟨32617417693646078587319737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43489890258194771449759649 32617417693646078587319737)
      ·
        refine ⟨24463063270234558940489803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32617417693646078587319737 24463063270234558940489803)
        ·
          refine ⟨36694594905351838410734705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24463063270234558940489803 36694594905351838410734705)
          ·
            refine ⟨27520946179013878808051029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36694594905351838410734705 27520946179013878808051029)
            ·
              refine ⟨40313886004414861535231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27520946179013878808051029 40313886004414861535231)
              ·
                rfl

theorem cell21_1589848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 11].length) (baseStart_1589848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589848 prefixEnd_1589848 := by exact prefixLift 1589848
  have htrace : WordTrace (prefixWord ++ tailWord_1589848) baseStart_1589848 baseEnd_1589848 := by
    simpa [prefixWord, tailWord_1589848, baseEnd_1589848] using wordTrace_append hprefix tailTrace_1589848
  have hstable : (prefixWord ++ tailWord_1589848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589848).length < 2 ^ (prefixWord ++ tailWord_1589848).sum := by decide
  have hdescent : baseEnd_1589848 < baseStart_1589848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589879 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 5]
def baseStart_1589879 : Nat := 118140960795 + 1589879 * 2 ^ 59
def prefixEnd_1589879 : Nat := 4983230072969 + 3 ^ 40 * 1589879 * 2
def baseEnd_1589879 : Nat := 362832048662084588800349

theorem tailTrace_1589879 : CollatzResearch.WordTrace tailWord_1589879 prefixEnd_1589879 362832048662084588800349 := by
  unfold tailWord_1589879
  simp only [CollatzResearch.WordTrace]
  refine ⟨57987651007147387560724691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38658434004764925040483127 57987651007147387560724691)
  ·
    refine ⟨86981476510721081341087037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57987651007147387560724691 86981476510721081341087037)
    ·
      refine ⟨32618053691520405502907639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86981476510721081341087037 32618053691520405502907639)
      ·
        refine ⟨48927080537280608254361459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32618053691520405502907639 48927080537280608254361459)
        ·
          refine ⟨73390620805920912381542189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48927080537280608254361459 73390620805920912381542189)
          ·
            refine ⟨27521482802220342143078321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73390620805920912381542189 27521482802220342143078321)
            ·
              refine ⟨20641112101665256607308741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27521482802220342143078321 20641112101665256607308741)
              ·
                refine ⟨3870208519062235613870389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20641112101665256607308741 3870208519062235613870389)
                ·
                  refine ⟨362832048662084588800349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3870208519062235613870389 362832048662084588800349)
                  ·
                    rfl

theorem cell21_1589879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_1589879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589879 prefixEnd_1589879 := by exact prefixLift 1589879
  have htrace : WordTrace (prefixWord ++ tailWord_1589879) baseStart_1589879 baseEnd_1589879 := by
    simpa [prefixWord, tailWord_1589879, baseEnd_1589879] using wordTrace_append hprefix tailTrace_1589879
  have hstable : (prefixWord ++ tailWord_1589879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589879).length < 2 ^ (prefixWord ++ tailWord_1589879).sum := by decide
  have hdescent : baseEnd_1589879 < baseStart_1589879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589930 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_1589930 : Nat := 118140960795 + 1589930 * 2 ^ 59
def prefixEnd_1589930 : Nat := 4983230072969 + 3 ^ 40 * 1589930 * 2
def baseEnd_1589930 : Nat := 362843687556919833450245

theorem tailTrace_1589930 : CollatzResearch.WordTrace tailWord_1589930 prefixEnd_1589930 362843687556919833450245 := by
  unfold tailWord_1589930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14497377782490655817707811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38659674086641748847220829 14497377782490655817707811)
  ·
    refine ⟨21746066673735983726561717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14497377782490655817707811 21746066673735983726561717)
    ·
      refine ⟨2038693750662748474365161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21746066673735983726561717 2038693750662748474365161)
      ·
        refine ⟨1529020312997061355773871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2038693750662748474365161 1529020312997061355773871)
        ·
          refine ⟨2293530469495592033660807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529020312997061355773871 2293530469495592033660807)
          ·
            refine ⟨3440295704243388050491211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293530469495592033660807 3440295704243388050491211)
            ·
              refine ⟨5160443556365082075736817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440295704243388050491211 5160443556365082075736817)
              ·
                refine ⟨3870332667273811556802613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5160443556365082075736817 3870332667273811556802613)
                ·
                  refine ⟨362843687556919833450245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3870332667273811556802613 362843687556919833450245)
                  ·
                    rfl

theorem cell21_1589930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_1589930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1589930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1589930 prefixEnd_1589930 := by exact prefixLift 1589930
  have htrace : WordTrace (prefixWord ++ tailWord_1589930) baseStart_1589930 baseEnd_1589930 := by
    simpa [prefixWord, tailWord_1589930, baseEnd_1589930] using wordTrace_append hprefix tailTrace_1589930
  have hstable : (prefixWord ++ tailWord_1589930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589930).length < 2 ^ (prefixWord ++ tailWord_1589930).sum := by decide
  have hdescent : baseEnd_1589930 < baseStart_1589930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590000 : List Nat := [2, 1, 1, 1, 3, 1, 5, 7]
def baseStart_1590000 : Nat := 118140960795 + 1590000 * 2 ^ 59
def prefixEnd_1590000 : Nat := 4983230072969 + 3 ^ 40 * 1590000 * 2
def baseEnd_1590000 : Nat := 120953220836871755761145

theorem tailTrace_1590000 : CollatzResearch.WordTrace tailWord_1590000 prefixEnd_1590000 120953220836871755761145 := by
  unfold tailWord_1590000
  simp only [CollatzResearch.WordTrace]
  refine ⟨28996032119854512612939727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38661376159806016817252969 28996032119854512612939727)
  ·
    refine ⟨43494048179781768919409591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28996032119854512612939727 43494048179781768919409591)
    ·
      refine ⟨65241072269672653379114387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43494048179781768919409591 65241072269672653379114387)
      ·
        refine ⟨97861608404508980068671581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65241072269672653379114387 97861608404508980068671581)
        ·
          refine ⟨36698103151690867525751843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97861608404508980068671581 36698103151690867525751843)
          ·
            refine ⟨55047154727536301288627765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36698103151690867525751843 55047154727536301288627765)
            ·
              refine ⟨5160670755706528245808853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55047154727536301288627765 5160670755706528245808853)
              ·
                refine ⟨120953220836871755761145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5160670755706528245808853 120953220836871755761145)
                ·
                  rfl

theorem cell21_1590000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_1590000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590000 prefixEnd_1590000 := by exact prefixLift 1590000
  have htrace : WordTrace (prefixWord ++ tailWord_1590000) baseStart_1590000 baseEnd_1590000 := by
    simpa [prefixWord, tailWord_1590000, baseEnd_1590000] using wordTrace_append hprefix tailTrace_1590000
  have hstable : (prefixWord ++ tailWord_1590000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590000).length < 2 ^ (prefixWord ++ tailWord_1590000).sum := by decide
  have hdescent : baseEnd_1590000 < baseStart_1590000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590079 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 4]
def baseStart_1590079 : Nat := 118140960795 + 1590079 * 2 ^ 59
def prefixEnd_1590079 : Nat := 4983230072969 + 3 ^ 40 * 1590079 * 2
def baseEnd_1590079 : Nat := 362877691386928685466607

theorem tailTrace_1590079 : CollatzResearch.WordTrace tailWord_1590079 prefixEnd_1590079 362877691386928685466607 := by
  unfold tailWord_1590079
  simp only [CollatzResearch.WordTrace]
  refine ⟨57994945606422821718005291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38663297070948547812003527 57994945606422821718005291)
  ·
    refine ⟨86992418409634232577007937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57994945606422821718005291 86992418409634232577007937)
    ·
      refine ⟨65244313807225674432755953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86992418409634232577007937 65244313807225674432755953)
      ·
        refine ⟨48933235355419255824566965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65244313807225674432755953 48933235355419255824566965)
        ·
          refine ⟨4587490814570555233553153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48933235355419255824566965 4587490814570555233553153)
          ·
            refine ⟨3440618110927916425164865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4587490814570555233553153 3440618110927916425164865)
            ·
              refine ⟨2580463583195937318873649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3440618110927916425164865 2580463583195937318873649)
              ·
                refine ⟨1935347687396952989155237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580463583195937318873649 1935347687396952989155237)
                ·
                  refine ⟨362877691386928685466607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1935347687396952989155237 362877691386928685466607)
                  ·
                    rfl

theorem cell21_1590079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 4].length) (baseStart_1590079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590079 prefixEnd_1590079 := by exact prefixLift 1590079
  have htrace : WordTrace (prefixWord ++ tailWord_1590079) baseStart_1590079 baseEnd_1590079 := by
    simpa [prefixWord, tailWord_1590079, baseEnd_1590079] using wordTrace_append hprefix tailTrace_1590079
  have hstable : (prefixWord ++ tailWord_1590079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590079).length < 2 ^ (prefixWord ++ tailWord_1590079).sum := by decide
  have hdescent : baseEnd_1590079 < baseStart_1590079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590200 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_1590200 : Nat := 118140960795 + 1590200 * 2 ^ 59
def prefixEnd_1590200 : Nat := 4983230072969 + 3 ^ 40 * 1590200 * 2
def baseEnd_1590200 : Nat := 362905305235459363949693

theorem tailTrace_1590200 : CollatzResearch.WordTrace tailWord_1590200 prefixEnd_1590200 362905305235459363949693 := by
  unfold tailWord_1590200
  simp only [CollatzResearch.WordTrace]
  refine ⟨28999679419492229691580027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38666239225989639588773369 28999679419492229691580027)
  ·
    refine ⟨43499519129238344537370041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28999679419492229691580027 43499519129238344537370041)
    ·
      refine ⟨32624639346928758403027531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43499519129238344537370041 32624639346928758403027531)
      ·
        refine ⟨48936959020393137604541297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32624639346928758403027531 48936959020393137604541297)
        ·
          refine ⟨36702719265294853203405973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48936959020393137604541297 36702719265294853203405973)
          ·
            refine ⟨1720439965560696243909655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36702719265294853203405973 1720439965560696243909655)
            ·
              refine ⟨2580659948341044365864483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720439965560696243909655 2580659948341044365864483)
              ·
                refine ⟨3870989922511566548796725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580659948341044365864483 3870989922511566548796725)
                ·
                  refine ⟨362905305235459363949693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3870989922511566548796725 362905305235459363949693)
                  ·
                    rfl

theorem cell21_1590200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_1590200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590200 prefixEnd_1590200 := by exact prefixLift 1590200
  have htrace : WordTrace (prefixWord ++ tailWord_1590200) baseStart_1590200 baseEnd_1590200 := by
    simpa [prefixWord, tailWord_1590200, baseEnd_1590200] using wordTrace_append hprefix tailTrace_1590200
  have hstable : (prefixWord ++ tailWord_1590200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590200).length < 2 ^ (prefixWord ++ tailWord_1590200).sum := by decide
  have hdescent : baseEnd_1590200 < baseStart_1590200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590245 : List Nat := [1, 3, 1, 6, 1, 9]
def baseStart_1590245 : Nat := 118140960795 + 1590245 * 2 ^ 59
def prefixEnd_1590245 : Nat := 4983230072969 + 3 ^ 40 * 1590245 * 2
def baseEnd_1590245 : Nat := 13441317586983306877763

theorem tailTrace_1590245 : CollatzResearch.WordTrace tailWord_1590245 prefixEnd_1590245 13441317586983306877763 := by
  unfold tailWord_1590245
  simp only [CollatzResearch.WordTrace]
  refine ⟨58001000123821432068548189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38667333415880954712365459 58001000123821432068548189)
  ·
    refine ⟨21750375046433037025705571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58001000123821432068548189 21750375046433037025705571)
    ·
      refine ⟨32625562569649555538558357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21750375046433037025705571 32625562569649555538558357)
      ·
        refine ⟨1529323245452322915869923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32625562569649555538558357 1529323245452322915869923)
        ·
          refine ⟨2293984868178484373804885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529323245452322915869923 2293984868178484373804885)
          ·
            refine ⟨13441317586983306877763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2293984868178484373804885 13441317586983306877763)
            ·
              rfl

theorem cell21_1590245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 9].length) (baseStart_1590245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590245 prefixEnd_1590245 := by exact prefixLift 1590245
  have htrace : WordTrace (prefixWord ++ tailWord_1590245) baseStart_1590245 baseEnd_1590245 := by
    simpa [prefixWord, tailWord_1590245, baseEnd_1590245] using wordTrace_append hprefix tailTrace_1590245
  have hstable : (prefixWord ++ tailWord_1590245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590245).length < 2 ^ (prefixWord ++ tailWord_1590245).sum := by decide
  have hdescent : baseEnd_1590245 < baseStart_1590245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590262 : List Nat := [5, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1590262 : Nat := 118140960795 + 1590262 * 2 ^ 59
def prefixEnd_1590262 : Nat := 4983230072969 + 3 ^ 40 * 1590262 * 2
def baseEnd_1590262 : Nat := 120973151493387011305411

theorem tailTrace_1590262 : CollatzResearch.WordTrace tailWord_1590262 prefixEnd_1590262 120973151493387011305411 := by
  unfold tailWord_1590262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3625101260297490248244815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38667746776506562647944693 3625101260297490248244815)
  ·
    refine ⟨5437651890446235372367223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3625101260297490248244815 5437651890446235372367223)
    ·
      refine ⟨8156477835669353058550835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5437651890446235372367223 8156477835669353058550835)
      ·
        refine ⟨12234716753504029587826253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8156477835669353058550835 12234716753504029587826253)
        ·
          refine ⟨4588018782564011095434845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12234716753504029587826253 4588018782564011095434845)
          ·
            refine ⟨1720507043461504160788067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4588018782564011095434845 1720507043461504160788067)
            ·
              refine ⟨2580760565192256241182101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720507043461504160788067 2580760565192256241182101)
              ·
                refine ⟨120973151493387011305411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2580760565192256241182101 120973151493387011305411)
                ·
                  rfl

theorem cell21_1590262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1590262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590262 prefixEnd_1590262 := by exact prefixLift 1590262
  have htrace : WordTrace (prefixWord ++ tailWord_1590262) baseStart_1590262 baseEnd_1590262 := by
    simpa [prefixWord, tailWord_1590262, baseEnd_1590262] using wordTrace_append hprefix tailTrace_1590262
  have hstable : (prefixWord ++ tailWord_1590262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590262).length < 2 ^ (prefixWord ++ tailWord_1590262).sum := by decide
  have hdescent : baseEnd_1590262 < baseStart_1590262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590293 : List Nat := [1, 3, 2, 1, 4, 2, 2, 3, 3]
def baseStart_1590293 : Nat := 118140960795 + 1590293 * 2 ^ 59
def prefixEnd_1590293 : Nat := 4983230072969 + 3 ^ 40 * 1590293 * 2
def baseEnd_1590293 : Nat := 362926529102511868899503

theorem tailTrace_1590293 : CollatzResearch.WordTrace tailWord_1590293 prefixEnd_1590293 362926529102511868899503 := by
  unfold tailWord_1590293
  simp only [CollatzResearch.WordTrace]
  refine ⟨58002750827647536266295533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38668500551765024177530355 58002750827647536266295533)
  ·
    refine ⟨21751031560367826099860825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58002750827647536266295533 21751031560367826099860825)
    ·
      refine ⟨16313273670275869574895619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21751031560367826099860825 16313273670275869574895619)
      ·
        refine ⟨24469910505413804362343429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16313273670275869574895619 24469910505413804362343429)
        ·
          refine ⟨4588108219765088317939393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24469910505413804362343429 4588108219765088317939393)
          ·
            refine ⟨3441081164823816238454545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4588108219765088317939393 3441081164823816238454545)
            ·
              refine ⟨2580810873617862178840909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3441081164823816238454545 2580810873617862178840909)
              ·
                refine ⟨967804077606698317065341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2580810873617862178840909 967804077606698317065341)
                ·
                  refine ⟨362926529102511868899503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967804077606698317065341 362926529102511868899503)
                  ·
                    rfl

theorem cell21_1590293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_1590293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590293 prefixEnd_1590293 := by exact prefixLift 1590293
  have htrace : WordTrace (prefixWord ++ tailWord_1590293) baseStart_1590293 baseEnd_1590293 := by
    simpa [prefixWord, tailWord_1590293, baseEnd_1590293] using wordTrace_append hprefix tailTrace_1590293
  have hstable : (prefixWord ++ tailWord_1590293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590293).length < 2 ^ (prefixWord ++ tailWord_1590293).sum := by decide
  have hdescent : baseEnd_1590293 < baseStart_1590293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590307 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 4]
def baseStart_1590307 : Nat := 118140960795 + 1590307 * 2 ^ 59
def prefixEnd_1590307 : Nat := 4983230072969 + 3 ^ 40 * 1590307 * 2
def baseEnd_1590307 : Nat := 362929724093250955666141

theorem tailTrace_1590307 : CollatzResearch.WordTrace tailWord_1590307 prefixEnd_1590307 362929724093250955666141 := by
  unfold tailWord_1590307
  simp only [CollatzResearch.WordTrace]
  refine ⟨58003261449596816657305175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38668840966397877771536783 58003261449596816657305175)
  ·
    refine ⟨87004892174395224985957763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58003261449596816657305175 87004892174395224985957763)
    ·
      refine ⟨130507338261592837478936645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87004892174395224985957763 130507338261592837478936645)
      ·
        refine ⟨24470125924048657027300621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130507338261592837478936645 24470125924048657027300621)
        ·
          refine ⟨9176297221518246385237733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24470125924048657027300621 9176297221518246385237733)
          ·
            refine ⟨1720555729034671197232075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9176297221518246385237733 1720555729034671197232075)
            ·
              refine ⟨2580833593552006795848113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720555729034671197232075 2580833593552006795848113)
              ·
                refine ⟨1935625195164005096886085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580833593552006795848113 1935625195164005096886085)
                ·
                  refine ⟨362929724093250955666141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1935625195164005096886085 362929724093250955666141)
                  ·
                    rfl

theorem cell21_1590307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 4].length) (baseStart_1590307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590307 prefixEnd_1590307 := by exact prefixLift 1590307
  have htrace : WordTrace (prefixWord ++ tailWord_1590307) baseStart_1590307 baseEnd_1590307 := by
    simpa [prefixWord, tailWord_1590307, baseEnd_1590307] using wordTrace_append hprefix tailTrace_1590307
  have hstable : (prefixWord ++ tailWord_1590307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590307).length < 2 ^ (prefixWord ++ tailWord_1590307).sum := by decide
  have hdescent : baseEnd_1590307 < baseStart_1590307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590380 : List Nat := [2, 2, 1, 1, 3, 2, 4, 6]
def baseStart_1590380 : Nat := 118140960795 + 1590380 * 2 ^ 59
def prefixEnd_1590380 : Nat := 4983230072969 + 3 ^ 40 * 1590380 * 2
def baseEnd_1590380 : Nat := 120982127895939683649775

theorem tailTrace_1590380 : CollatzResearch.WordTrace tailWord_1590380 prefixEnd_1590380 120982127895939683649775 := by
  unfold tailWord_1590380
  simp only [CollatzResearch.WordTrace]
  refine ⟨29002961989166175062356297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38670615985554900083141729 29002961989166175062356297)
  ·
    refine ⟨21752221491874631296767223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29002961989166175062356297 21752221491874631296767223)
    ·
      refine ⟨32628332237811946945150835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21752221491874631296767223 32628332237811946945150835)
      ·
        refine ⟨48942498356717920417726253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32628332237811946945150835 48942498356717920417726253)
        ·
          refine ⟨18353436883769220156647345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48942498356717920417726253 18353436883769220156647345)
          ·
            refine ⟨13765077662826915117485509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18353436883769220156647345 13765077662826915117485509)
            ·
              refine ⟨2580952061780046584528533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13765077662826915117485509 2580952061780046584528533)
              ·
                refine ⟨120982127895939683649775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2580952061780046584528533 120982127895939683649775)
                ·
                  rfl

theorem cell21_1590380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_1590380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590380 prefixEnd_1590380 := by exact prefixLift 1590380
  have htrace : WordTrace (prefixWord ++ tailWord_1590380) baseStart_1590380 baseEnd_1590380 := by
    simpa [prefixWord, tailWord_1590380, baseEnd_1590380] using wordTrace_append hprefix tailTrace_1590380
  have hstable : (prefixWord ++ tailWord_1590380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590380).length < 2 ^ (prefixWord ++ tailWord_1590380).sum := by decide
  have hdescent : baseEnd_1590380 < baseStart_1590380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590532 : List Nat := [2, 3, 2, 2, 2, 1, 9]
def baseStart_1590532 : Nat := 118140960795 + 1590532 * 2 ^ 59
def prefixEnd_1590532 : Nat := 4983230072969 + 3 ^ 40 * 1590532 * 2
def baseEnd_1590532 : Nat := 40331230239855618268409

theorem tailTrace_1590532 : CollatzResearch.WordTrace tailWord_1590532 prefixEnd_1590532 40331230239855618268409 := by
  unfold tailWord_1590532
  simp only [CollatzResearch.WordTrace]
  refine ⟨29005733936890840042122925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38674311915854453389497233 29005733936890840042122925)
  ·
    refine ⟨10877150226334065015796097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29005733936890840042122925 10877150226334065015796097)
    ·
      refine ⟨8157862669750548761847073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10877150226334065015796097 8157862669750548761847073)
      ·
        refine ⟨6118397002312911571385305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8157862669750548761847073 6118397002312911571385305)
        ·
          refine ⟨4588797751734683678538979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6118397002312911571385305 4588797751734683678538979)
          ·
            refine ⟨6883196627602025517808469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588797751734683678538979 6883196627602025517808469)
            ·
              refine ⟨40331230239855618268409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6883196627602025517808469 40331230239855618268409)
              ·
                rfl

theorem cell21_1590532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 9].length) (baseStart_1590532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590532 prefixEnd_1590532 := by exact prefixLift 1590532
  have htrace : WordTrace (prefixWord ++ tailWord_1590532) baseStart_1590532 baseEnd_1590532 := by
    simpa [prefixWord, tailWord_1590532, baseEnd_1590532] using wordTrace_append hprefix tailTrace_1590532
  have hstable : (prefixWord ++ tailWord_1590532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590532).length < 2 ^ (prefixWord ++ tailWord_1590532).sum := by decide
  have hdescent : baseEnd_1590532 < baseStart_1590532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590591 : List Nat := [1, 1, 2, 2, 4, 11]
def baseStart_1590591 : Nat := 118140960795 + 1590591 * 2 ^ 59
def prefixEnd_1590591 : Nat := 4983230072969 + 3 ^ 40 * 1590591 * 2
def baseEnd_1590591 : Nat := 13444242102315910108601

theorem tailTrace_1590591 : CollatzResearch.WordTrace tailWord_1590591 prefixEnd_1590591 13444242102315910108601 := by
  unfold tailWord_1590591
  simp only [CollatzResearch.WordTrace]
  refine ⟨58013619780567933160643627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38675746520378622107095751 58013619780567933160643627)
  ·
    refine ⟨87020429670851899740965441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58013619780567933160643627 87020429670851899740965441)
    ·
      refine ⟨65265322253138924805724081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87020429670851899740965441 65265322253138924805724081)
      ·
        refine ⟨48948991689854193604293061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65265322253138924805724081 48948991689854193604293061)
        ·
          refine ⟨9177935941847661300804949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48948991689854193604293061 9177935941847661300804949)
          ·
            refine ⟨13444242102315910108601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9177935941847661300804949 13444242102315910108601)
            ·
              rfl

theorem cell21_1590591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 11].length) (baseStart_1590591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590591 prefixEnd_1590591 := by exact prefixLift 1590591
  have htrace : WordTrace (prefixWord ++ tailWord_1590591) baseStart_1590591 baseEnd_1590591 := by
    simpa [prefixWord, tailWord_1590591, baseEnd_1590591] using wordTrace_append hprefix tailTrace_1590591
  have hstable : (prefixWord ++ tailWord_1590591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590591).length < 2 ^ (prefixWord ++ tailWord_1590591).sum := by decide
  have hdescent : baseEnd_1590591 < baseStart_1590591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590653 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 6]
def baseStart_1590653 : Nat := 118140960795 + 1590653 * 2 ^ 59
def prefixEnd_1590653 : Nat := 4983230072969 + 3 ^ 40 * 1590653 * 2
def baseEnd_1590653 : Nat := 363008686007231242898767

theorem tailTrace_1590653 : CollatzResearch.WordTrace tailWord_1590653 prefixEnd_1590653 363008686007231242898767 := by
  unfold tailWord_1590653
  simp only [CollatzResearch.WordTrace]
  refine ⟨58015881106343317749400613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38677254070895545166267075 58015881106343317749400613)
  ·
    refine ⟨10877977707439372078012615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58015881106343317749400613 10877977707439372078012615)
    ·
      refine ⟨16316966561159058117018923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10877977707439372078012615 16316966561159058117018923)
      ·
        refine ⟨24475449841738587175528385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16316966561159058117018923 24475449841738587175528385)
        ·
          refine ⟨18356587381303940381646289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24475449841738587175528385 18356587381303940381646289)
          ·
            refine ⟨13767440535977955286234717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18356587381303940381646289 13767440535977955286234717)
            ·
              refine ⟨5162790200991733232338019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13767440535977955286234717 5162790200991733232338019)
              ·
                refine ⟨7744185301487599848507029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162790200991733232338019 7744185301487599848507029)
                ·
                  refine ⟨363008686007231242898767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7744185301487599848507029 363008686007231242898767)
                  ·
                    rfl

theorem cell21_1590653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_1590653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590653 prefixEnd_1590653 := by exact prefixLift 1590653
  have htrace : WordTrace (prefixWord ++ tailWord_1590653) baseStart_1590653 baseEnd_1590653 := by
    simpa [prefixWord, tailWord_1590653, baseEnd_1590653] using wordTrace_append hprefix tailTrace_1590653
  have hstable : (prefixWord ++ tailWord_1590653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590653).length < 2 ^ (prefixWord ++ tailWord_1590653).sum := by decide
  have hdescent : baseEnd_1590653 < baseStart_1590653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590667 : List Nat := [1, 1, 1, 1, 4, 3, 2, 8]
def baseStart_1590667 : Nat := 118140960795 + 1590667 * 2 ^ 59
def prefixEnd_1590667 : Nat := 4983230072969 + 3 ^ 40 * 1590667 * 2
def baseEnd_1590667 : Nat := 121003960332656776555135

theorem tailTrace_1590667 : CollatzResearch.WordTrace tailWord_1590667 prefixEnd_1590667 121003960332656776555135 := by
  unfold tailWord_1590667
  simp only [CollatzResearch.WordTrace]
  refine ⟨58016391728292598140410255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38677594485528398760273503 58016391728292598140410255)
  ·
    refine ⟨87024587592438897210615383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58016391728292598140410255 87024587592438897210615383)
    ·
      refine ⟨130536881388658345815923075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87024587592438897210615383 130536881388658345815923075)
      ·
        refine ⟨195805322082987518723884613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130536881388658345815923075 195805322082987518723884613)
        ·
          refine ⟨36713497890560159760728365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195805322082987518723884613 36713497890560159760728365)
          ·
            refine ⟨13767561708960059910273137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36713497890560159760728365 13767561708960059910273137)
            ·
              refine ⟨10325671281720044932704853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13767561708960059910273137 10325671281720044932704853)
              ·
                refine ⟨121003960332656776555135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10325671281720044932704853 121003960332656776555135)
                ·
                  rfl

theorem cell21_1590667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 8].length) (baseStart_1590667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590667 prefixEnd_1590667 := by exact prefixLift 1590667
  have htrace : WordTrace (prefixWord ++ tailWord_1590667) baseStart_1590667 baseEnd_1590667 := by
    simpa [prefixWord, tailWord_1590667, baseEnd_1590667] using wordTrace_append hprefix tailTrace_1590667
  have hstable : (prefixWord ++ tailWord_1590667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590667).length < 2 ^ (prefixWord ++ tailWord_1590667).sum := by decide
  have hdescent : baseEnd_1590667 < baseStart_1590667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590701 : List Nat := [1, 5, 2, 2, 1, 3, 7]
def baseStart_1590701 : Nat := 118140960795 + 1590701 * 2 ^ 59
def prefixEnd_1590701 : Nat := 4983230072969 + 3 ^ 40 * 1590701 * 2
def baseEnd_1590701 : Nat := 40335515584577091788741

theorem tailTrace_1590701 : CollatzResearch.WordTrace tailWord_1590701 prefixEnd_1590701 40335515584577091788741 := by
  unfold tailWord_1590701
  simp only [CollatzResearch.WordTrace]
  refine ⟨58017631810169421947147957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38678421206779614631431971 58017631810169421947147957)
  ·
    refine ⟨5439152982203383307545121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58017631810169421947147957 5439152982203383307545121)
    ·
      refine ⟨4079364736652537480658841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5439152982203383307545121 4079364736652537480658841)
      ·
        refine ⟨3059523552489403110494131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4079364736652537480658841 3059523552489403110494131)
        ·
          refine ⟨4589285328734104665741197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3059523552489403110494131 4589285328734104665741197)
          ·
            refine ⟨1720981998275289249652949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4589285328734104665741197 1720981998275289249652949)
            ·
              refine ⟨40335515584577091788741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1720981998275289249652949 40335515584577091788741)
              ·
                rfl

theorem cell21_1590701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 7].length) (baseStart_1590701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590701 prefixEnd_1590701 := by exact prefixLift 1590701
  have htrace : WordTrace (prefixWord ++ tailWord_1590701) baseStart_1590701 baseEnd_1590701 := by
    simpa [prefixWord, tailWord_1590701, baseEnd_1590701] using wordTrace_append hprefix tailTrace_1590701
  have hstable : (prefixWord ++ tailWord_1590701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590701).length < 2 ^ (prefixWord ++ tailWord_1590701).sum := by decide
  have hdescent : baseEnd_1590701 < baseStart_1590701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590791 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 5]
def baseStart_1590791 : Nat := 118140960795 + 1590791 * 2 ^ 59
def prefixEnd_1590791 : Nat := 4983230072969 + 3 ^ 40 * 1590791 * 2
def baseEnd_1590791 : Nat := 363040179487373669598485

theorem tailTrace_1590791 : CollatzResearch.WordTrace tailWord_1590791 prefixEnd_1590791 363040179487373669598485 := by
  unfold tailWord_1590791
  simp only [CollatzResearch.WordTrace]
  refine ⟨58020914379843367317924227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38680609586562244878616151 58020914379843367317924227)
  ·
    refine ⟨87031371569765050976886341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58020914379843367317924227 87031371569765050976886341)
    ·
      refine ⟨16318382169330947058166189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87031371569765050976886341 16318382169330947058166189)
      ·
        refine ⟨6119393313499105146812321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16318382169330947058166189 6119393313499105146812321)
        ·
          refine ⟨4589544985124328860109241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6119393313499105146812321 4589544985124328860109241)
          ·
            refine ⟨3442158738843246645081931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4589544985124328860109241 3442158738843246645081931)
            ·
              refine ⟨5163238108264869967622897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442158738843246645081931 5163238108264869967622897)
              ·
                refine ⟨3872428581198652475717173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5163238108264869967622897 3872428581198652475717173)
                ·
                  refine ⟨363040179487373669598485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3872428581198652475717173 363040179487373669598485)
                  ·
                    rfl

theorem cell21_1590791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_1590791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590791 prefixEnd_1590791 := by exact prefixLift 1590791
  have htrace : WordTrace (prefixWord ++ tailWord_1590791) baseStart_1590791 baseEnd_1590791 := by
    simpa [prefixWord, tailWord_1590791, baseEnd_1590791] using wordTrace_append hprefix tailTrace_1590791
  have hstable : (prefixWord ++ tailWord_1590791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590791).length < 2 ^ (prefixWord ++ tailWord_1590791).sum := by decide
  have hdescent : baseEnd_1590791 < baseStart_1590791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590814 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1590814 : Nat := 118140960795 + 1590814 * 2 ^ 59
def prefixEnd_1590814 : Nat := 4983230072969 + 3 ^ 40 * 1590814 * 2
def baseEnd_1590814 : Nat := 363045428400730740715105

theorem tailTrace_1590814 : CollatzResearch.WordTrace tailWord_1590814 prefixEnd_1590814 363045428400730740715105 := by
  unfold tailWord_1590814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7252719157345005280751437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38681168839173361497340997 7252719157345005280751437)
  ·
    refine ⟨2719769684004376980281789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7252719157345005280751437 2719769684004376980281789)
    ·
      refine ⟨1019913631501641367605671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2719769684004376980281789 1019913631501641367605671)
      ·
        refine ⟨1529870447252462051408507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019913631501641367605671 1529870447252462051408507)
        ·
          refine ⟨2294805670878693077112761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529870447252462051408507 2294805670878693077112761)
          ·
            refine ⟨1721104253159019807834571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2294805670878693077112761 1721104253159019807834571)
            ·
              refine ⟨2581656379738529711751857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721104253159019807834571 2581656379738529711751857)
              ·
                refine ⟨1936242284803897283813893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2581656379738529711751857 1936242284803897283813893)
                ·
                  refine ⟨363045428400730740715105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936242284803897283813893 363045428400730740715105)
                  ·
                    rfl

theorem cell21_1590814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1590814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590814 prefixEnd_1590814 := by exact prefixLift 1590814
  have htrace : WordTrace (prefixWord ++ tailWord_1590814) baseStart_1590814 baseEnd_1590814 := by
    simpa [prefixWord, tailWord_1590814, baseEnd_1590814] using wordTrace_append hprefix tailTrace_1590814
  have hstable : (prefixWord ++ tailWord_1590814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590814).length < 2 ^ (prefixWord ++ tailWord_1590814).sum := by decide
  have hdescent : baseEnd_1590814 < baseStart_1590814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590864 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_1590864 : Nat := 118140960795 + 1590864 * 2 ^ 59
def prefixEnd_1590864 : Nat := 4983230072969 + 3 ^ 40 * 1590864 * 2
def baseEnd_1590864 : Nat := 363056839081941764881669

theorem tailTrace_1590864 : CollatzResearch.WordTrace tailWord_1590864 prefixEnd_1590864 363056839081941764881669 := by
  unfold tailWord_1590864
  simp only [CollatzResearch.WordTrace]
  refine ⟨29011788454289450392665823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38682384605719267190221097 29011788454289450392665823)
  ·
    refine ⟨43517682681434175588998735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29011788454289450392665823 43517682681434175588998735)
    ·
      refine ⟨65276524022151263383498103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43517682681434175588998735 65276524022151263383498103)
      ·
        refine ⟨97914786033226895075247155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65276524022151263383498103 97914786033226895075247155)
        ·
          refine ⟨146872179049840342612870733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97914786033226895075247155 146872179049840342612870733)
          ·
            refine ⟨55077067143690128479826525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146872179049840342612870733 55077067143690128479826525)
            ·
              refine ⟨20653900178883798179934947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55077067143690128479826525 20653900178883798179934947)
              ·
                refine ⟨30980850268325697269902421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20653900178883798179934947 30980850268325697269902421)
                ·
                  refine ⟨363056839081941764881669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30980850268325697269902421 363056839081941764881669)
                  ·
                    rfl

theorem cell21_1590864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_1590864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590864 prefixEnd_1590864 := by exact prefixLift 1590864
  have htrace : WordTrace (prefixWord ++ tailWord_1590864) baseStart_1590864 baseEnd_1590864 := by
    simpa [prefixWord, tailWord_1590864, baseEnd_1590864] using wordTrace_append hprefix tailTrace_1590864
  have hstable : (prefixWord ++ tailWord_1590864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590864).length < 2 ^ (prefixWord ++ tailWord_1590864).sum := by decide
  have hdescent : baseEnd_1590864 < baseStart_1590864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590881 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 4]
def baseStart_1590881 : Nat := 118140960795 + 1590881 * 2 ^ 59
def prefixEnd_1590881 : Nat := 4983230072969 + 3 ^ 40 * 1590881 * 2
def baseEnd_1590881 : Nat := 363060718713553513098301

theorem tailTrace_1590881 : CollatzResearch.WordTrace tailWord_1590881 prefixEnd_1590881 363060718713553513098301 := by
  unfold tailWord_1590881
  simp only [CollatzResearch.WordTrace]
  refine ⟨58024196949517312688700497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38682797966344875125800331 58024196949517312688700497)
  ·
    refine ⟨43518147712137984516525373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58024196949517312688700497 43518147712137984516525373)
    ·
      refine ⟨16319305392051744193697015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43518147712137984516525373 16319305392051744193697015)
      ·
        refine ⟨24478958088077616290545523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16319305392051744193697015 24478958088077616290545523)
        ·
          refine ⟨36718437132116424435818285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24478958088077616290545523 36718437132116424435818285)
          ·
            refine ⟨13769413924543659163431857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36718437132116424435818285 13769413924543659163431857)
            ·
              refine ⟨10327060443407744372573893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13769413924543659163431857 10327060443407744372573893)
              ·
                refine ⟨1936323833138952069857605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10327060443407744372573893 1936323833138952069857605)
                ·
                  refine ⟨363060718713553513098301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936323833138952069857605 363060718713553513098301)
                  ·
                    rfl

theorem cell21_1590881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_1590881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590881 prefixEnd_1590881 := by exact prefixLift 1590881
  have htrace : WordTrace (prefixWord ++ tailWord_1590881) baseStart_1590881 baseEnd_1590881 := by
    simpa [prefixWord, tailWord_1590881, baseEnd_1590881] using wordTrace_append hprefix tailTrace_1590881
  have hstable : (prefixWord ++ tailWord_1590881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590881).length < 2 ^ (prefixWord ++ tailWord_1590881).sum := by decide
  have hdescent : baseEnd_1590881 < baseStart_1590881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590898 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1590898 : Nat := 118140960795 + 1590898 * 2 ^ 59
def prefixEnd_1590898 : Nat := 4983230072969 + 3 ^ 40 * 1590898 * 2
def baseEnd_1590898 : Nat := 363064598345165261314933

theorem tailTrace_1590898 : CollatzResearch.WordTrace tailWord_1590898 prefixEnd_1590898 363064598345165261314933 := by
  unfold tailWord_1590898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14506204247613931148017337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38683211326970483061379565 14506204247613931148017337)
  ·
    refine ⟨10879653185710448361013003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14506204247613931148017337 10879653185710448361013003)
    ·
      refine ⟨16319479778565672541519505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10879653185710448361013003 16319479778565672541519505)
      ·
        refine ⟨12239609833924254406139629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16319479778565672541519505 12239609833924254406139629)
        ·
          refine ⟨4589853687721595402302361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12239609833924254406139629 4589853687721595402302361)
          ·
            refine ⟨3442390265791196551726771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4589853687721595402302361 3442390265791196551726771)
            ·
              refine ⟨5163585398686794827590157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442390265791196551726771 5163585398686794827590157)
              ·
                refine ⟨1936344524507548060346309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5163585398686794827590157 1936344524507548060346309)
                ·
                  refine ⟨363064598345165261314933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936344524507548060346309 363064598345165261314933)
                  ·
                    rfl

theorem cell21_1590898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1590898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590898 prefixEnd_1590898 := by exact prefixLift 1590898
  have htrace : WordTrace (prefixWord ++ tailWord_1590898) baseStart_1590898 baseEnd_1590898 := by
    simpa [prefixWord, tailWord_1590898, baseEnd_1590898] using wordTrace_append hprefix tailTrace_1590898
  have hstable : (prefixWord ++ tailWord_1590898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590898).length < 2 ^ (prefixWord ++ tailWord_1590898).sum := by decide
  have hdescent : baseEnd_1590898 < baseStart_1590898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590946 : List Nat := [3, 3, 1, 4, 1, 2, 1, 6]
def baseStart_1590946 : Nat := 118140960795 + 1590946 * 2 ^ 59
def prefixEnd_1590946 : Nat := 4983230072969 + 3 ^ 40 * 1590946 * 2
def baseEnd_1590946 : Nat := 121025184199709281504945

theorem tailTrace_1590946 : CollatzResearch.WordTrace tailWord_1590946 prefixEnd_1590946 121025184199709281504945 := by
  unfold tailWord_1590946
  simp only [CollatzResearch.WordTrace]
  refine ⟨14506641923570457197454173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38684378462854552526544461 14506641923570457197454173)
  ·
    refine ⟨5439990721338921449045315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14506641923570457197454173 5439990721338921449045315)
    ·
      refine ⟨8159986082008382173567973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439990721338921449045315 8159986082008382173567973)
      ·
        refine ⟨1529997390376571657543995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8159986082008382173567973 1529997390376571657543995)
        ·
          refine ⟨2294996085564857486315993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529997390376571657543995 2294996085564857486315993)
          ·
            refine ⟨1721247064173643114736995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2294996085564857486315993 1721247064173643114736995)
            ·
              refine ⟨2581870596260464672105493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721247064173643114736995 2581870596260464672105493)
              ·
                refine ⟨121025184199709281504945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2581870596260464672105493 121025184199709281504945)
                ·
                  rfl

theorem cell21_1590946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_1590946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590946 prefixEnd_1590946 := by exact prefixLift 1590946
  have htrace : WordTrace (prefixWord ++ tailWord_1590946) baseStart_1590946 baseEnd_1590946 := by
    simpa [prefixWord, tailWord_1590946, baseEnd_1590946] using wordTrace_append hprefix tailTrace_1590946
  have hstable : (prefixWord ++ tailWord_1590946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590946).length < 2 ^ (prefixWord ++ tailWord_1590946).sum := by decide
  have hdescent : baseEnd_1590946 < baseStart_1590946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590988 : List Nat := [2, 2, 1, 5, 2, 1, 8]
def baseStart_1590988 : Nat := 118140960795 + 1590988 * 2 ^ 59
def prefixEnd_1590988 : Nat := 4983230072969 + 3 ^ 40 * 1590988 * 2
def baseEnd_1590988 : Nat := 40342793063482789423861

theorem tailTrace_1590988 : CollatzResearch.WordTrace tailWord_1590988 prefixEnd_1590988 40342793063482789423861 := by
  unfold tailWord_1590988
  simp only [CollatzResearch.WordTrace]
  refine ⟨29014049780064834981422809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38685399706753113308563745 29014049780064834981422809)
  ·
    refine ⟨21760537335048626236067107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29014049780064834981422809 21760537335048626236067107)
    ·
      refine ⟨32640806002572939354100661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21760537335048626236067107 32640806002572939354100661)
      ·
        refine ⟨3060075562741213064446937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32640806002572939354100661 3060075562741213064446937)
        ·
          refine ⟨2295056672055909798335203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060075562741213064446937 2295056672055909798335203)
          ·
            refine ⟨3442585008083864697502805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295056672055909798335203 3442585008083864697502805)
            ·
              refine ⟨40342793063482789423861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3442585008083864697502805 40342793063482789423861)
              ·
                rfl

theorem cell21_1590988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 8].length) (baseStart_1590988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1590988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1590988 prefixEnd_1590988 := by exact prefixLift 1590988
  have htrace : WordTrace (prefixWord ++ tailWord_1590988) baseStart_1590988 baseEnd_1590988 := by
    simpa [prefixWord, tailWord_1590988, baseEnd_1590988] using wordTrace_append hprefix tailTrace_1590988
  have hstable : (prefixWord ++ tailWord_1590988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590988).length < 2 ^ (prefixWord ++ tailWord_1590988).sum := by decide
  have hdescent : baseEnd_1590988 < baseStart_1590988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591002 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_1591002 : Nat := 118140960795 + 1591002 * 2 ^ 59
def prefixEnd_1591002 : Nat := 4983230072969 + 3 ^ 40 * 1591002 * 2
def baseEnd_1591002 : Nat := 363088332562084191581387

theorem tailTrace_1591002 : CollatzResearch.WordTrace tailWord_1591002 prefixEnd_1591002 363088332562084191581387 := by
  unfold tailWord_1591002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14507152545519737588463815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38685740121385966902570173 14507152545519737588463815)
  ·
    refine ⟨21760728818279606382695723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14507152545519737588463815 21760728818279606382695723)
    ·
      refine ⟨32641093227419409574043585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21760728818279606382695723 32641093227419409574043585)
      ·
        refine ⟨24480819920564557180532689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32641093227419409574043585 24480819920564557180532689)
        ·
          refine ⟨18360614940423417885399517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24480819920564557180532689 18360614940423417885399517)
          ·
            refine ⟨6885230602658781707024819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18360614940423417885399517 6885230602658781707024819)
            ·
              refine ⟨10327845903988172560537229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6885230602658781707024819 10327845903988172560537229)
              ·
                refine ⟨3872942213995564710201461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10327845903988172560537229 3872942213995564710201461)
                ·
                  refine ⟨363088332562084191581387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3872942213995564710201461 363088332562084191581387)
                  ·
                    rfl

theorem cell21_1591002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_1591002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591002 prefixEnd_1591002 := by exact prefixLift 1591002
  have htrace : WordTrace (prefixWord ++ tailWord_1591002) baseStart_1591002 baseEnd_1591002 := by
    simpa [prefixWord, tailWord_1591002, baseEnd_1591002] using wordTrace_append hprefix tailTrace_1591002
  have hstable : (prefixWord ++ tailWord_1591002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591002).length < 2 ^ (prefixWord ++ tailWord_1591002).sum := by decide
  have hdescent : baseEnd_1591002 < baseStart_1591002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591109 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 4]
def baseStart_1591109 : Nat := 118140960795 + 1591109 * 2 ^ 59
def prefixEnd_1591109 : Nat := 4983230072969 + 3 ^ 40 * 1591109 * 2
def baseEnd_1591109 : Nat := 363112751419875783297835

theorem tailTrace_1591109 : CollatzResearch.WordTrace tailWord_1591109 prefixEnd_1591109 363112751419875783297835 := by
  unfold tailWord_1591109
  simp only [CollatzResearch.WordTrace]
  refine ⟨58032512792691307628000381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38688341861794205085333587 58032512792691307628000381)
  ·
    refine ⟨21762192297259240360500143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58032512792691307628000381 21762192297259240360500143)
    ·
      refine ⟨32643288445888860540750215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21762192297259240360500143 32643288445888860540750215)
      ·
        refine ⟨48964932668833290811125323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32643288445888860540750215 48964932668833290811125323)
        ·
          refine ⟨73447399003249936216687985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48964932668833290811125323 73447399003249936216687985)
          ·
            refine ⟨55085549252437452162515989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73447399003249936216687985 55085549252437452162515989)
            ·
              refine ⟨2582135121208005570117937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55085549252437452162515989 2582135121208005570117937)
              ·
                refine ⟨1936601340906004177588453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2582135121208005570117937 1936601340906004177588453)
                ·
                  refine ⟨363112751419875783297835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936601340906004177588453 363112751419875783297835)
                  ·
                    rfl

theorem cell21_1591109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_1591109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591109 prefixEnd_1591109 := by exact prefixLift 1591109
  have htrace : WordTrace (prefixWord ++ tailWord_1591109) baseStart_1591109 baseEnd_1591109 := by
    simpa [prefixWord, tailWord_1591109, baseEnd_1591109] using wordTrace_append hprefix tailTrace_1591109
  have hstable : (prefixWord ++ tailWord_1591109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591109).length < 2 ^ (prefixWord ++ tailWord_1591109).sum := by decide
  have hdescent : baseEnd_1591109 < baseStart_1591109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591112 : List Nat := [2, 1, 3, 1, 1, 4, 4, 2, 3]
def baseStart_1591112 : Nat := 118140960795 + 1591112 * 2 ^ 59
def prefixEnd_1591112 : Nat := 4983230072969 + 3 ^ 40 * 1591112 * 2
def baseEnd_1591112 : Nat := 363113436060748444747829

theorem tailTrace_1591112 : CollatzResearch.WordTrace tailWord_1591112 prefixEnd_1591112 363113436060748444747829 := by
  unfold tailWord_1591112
  simp only [CollatzResearch.WordTrace]
  refine ⟨29016311105840219570179795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38688414807786959426906393 29016311105840219570179795)
  ·
    refine ⟨43524466658760329355269693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29016311105840219570179795 43524466658760329355269693)
    ·
      refine ⟨16321674997035123508226135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43524466658760329355269693 16321674997035123508226135)
      ·
        refine ⟨24482512495552685262339203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16321674997035123508226135 24482512495552685262339203)
        ·
          refine ⟨36723768743329027893508805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24482512495552685262339203 36723768743329027893508805)
          ·
            refine ⟨6885706639374192730032901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36723768743329027893508805 6885706639374192730032901)
            ·
              refine ⟨1291069994882661136881169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6885706639374192730032901 1291069994882661136881169)
              ·
                refine ⟨968302496161995852660877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291069994882661136881169 968302496161995852660877)
                ·
                  refine ⟨363113436060748444747829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968302496161995852660877 363113436060748444747829)
                  ·
                    rfl

theorem cell21_1591112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_1591112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591112 prefixEnd_1591112 := by exact prefixLift 1591112
  have htrace : WordTrace (prefixWord ++ tailWord_1591112) baseStart_1591112 baseEnd_1591112 := by
    simpa [prefixWord, tailWord_1591112, baseEnd_1591112] using wordTrace_append hprefix tailTrace_1591112
  have hstable : (prefixWord ++ tailWord_1591112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591112).length < 2 ^ (prefixWord ++ tailWord_1591112).sum := by decide
  have hdescent : baseEnd_1591112 < baseStart_1591112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591168 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_1591168 : Nat := 118140960795 + 1591168 * 2 ^ 59
def prefixEnd_1591168 : Nat := 4983230072969 + 3 ^ 40 * 1591168 * 2
def baseEnd_1591168 : Nat := 363126216023704791814381

theorem tailTrace_1591168 : CollatzResearch.WordTrace tailWord_1591168 prefixEnd_1591168 363126216023704791814381 := by
  unfold tailWord_1591168
  simp only [CollatzResearch.WordTrace]
  refine ⟨29017332349738780352199079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38689776466318373802932105 29017332349738780352199079)
  ·
    refine ⟨43525998524608170528298619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29017332349738780352199079 43525998524608170528298619)
    ·
      refine ⟨65288997786912255792447929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43525998524608170528298619 65288997786912255792447929)
      ·
        refine ⟨48966748340184191844335947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65288997786912255792447929 48966748340184191844335947)
        ·
          refine ⟨73450122510276287766503921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48966748340184191844335947 73450122510276287766503921)
          ·
            refine ⟨55087591882707215824877941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73450122510276287766503921 55087591882707215824877941)
            ·
              refine ⟨5164461739003801483582307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55087591882707215824877941 5164461739003801483582307)
              ·
                refine ⟨7746692608505702225373461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5164461739003801483582307 7746692608505702225373461)
                ·
                  refine ⟨363126216023704791814381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7746692608505702225373461 363126216023704791814381)
                  ·
                    rfl

theorem cell21_1591168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_1591168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591168 prefixEnd_1591168 := by exact prefixLift 1591168
  have htrace : WordTrace (prefixWord ++ tailWord_1591168) baseStart_1591168 baseEnd_1591168 := by
    simpa [prefixWord, tailWord_1591168, baseEnd_1591168] using wordTrace_append hprefix tailTrace_1591168
  have hstable : (prefixWord ++ tailWord_1591168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591168).length < 2 ^ (prefixWord ++ tailWord_1591168).sum := by decide
  have hdescent : baseEnd_1591168 < baseStart_1591168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591171 : List Nat := [1, 1, 1, 3, 4, 2, 2, 4, 3]
def baseStart_1591171 : Nat := 118140960795 + 1591171 * 2 ^ 59
def prefixEnd_1591171 : Nat := 4983230072969 + 3 ^ 40 * 1591171 * 2
def baseEnd_1591171 : Nat := 363126900664577453264375

theorem tailTrace_1591171 : CollatzResearch.WordTrace tailWord_1591171 prefixEnd_1591171 363126900664577453264375 := by
  unfold tailWord_1591171
  simp only [CollatzResearch.WordTrace]
  refine ⟨58034774118466692216757367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38689849412311128144504911 58034774118466692216757367)
  ·
    refine ⟨87052161177700038325136051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58034774118466692216757367 87052161177700038325136051)
    ·
      refine ⟨130578241766550057487704077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87052161177700038325136051 130578241766550057487704077)
      ·
        refine ⟨48966840662456271557889029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130578241766550057487704077 48966840662456271557889029)
        ·
          refine ⟨9181282624210550917104193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48966840662456271557889029 9181282624210550917104193)
          ·
            refine ⟨6885961968157913187828145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9181282624210550917104193 6885961968157913187828145)
            ·
              refine ⟨5164471476118434890871109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6885961968157913187828145 5164471476118434890871109)
              ·
                refine ⟨968338401772206542038333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5164471476118434890871109 968338401772206542038333)
                ·
                  refine ⟨363126900664577453264375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968338401772206542038333 363126900664577453264375)
                  ·
                    rfl

theorem cell21_1591171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 3].length) (baseStart_1591171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591171 prefixEnd_1591171 := by exact prefixLift 1591171
  have htrace : WordTrace (prefixWord ++ tailWord_1591171) baseStart_1591171 baseEnd_1591171 := by
    simpa [prefixWord, tailWord_1591171, baseEnd_1591171] using wordTrace_append hprefix tailTrace_1591171
  have hstable : (prefixWord ++ tailWord_1591171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591171).length < 2 ^ (prefixWord ++ tailWord_1591171).sum := by decide
  have hdescent : baseEnd_1591171 < baseStart_1591171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591278 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_1591278 : Nat := 118140960795 + 1591278 * 2 ^ 59
def prefixEnd_1591278 : Nat := 4983230072969 + 3 ^ 40 * 1591278 * 2
def baseEnd_1591278 : Nat := 363151319522369044980823

theorem tailTrace_1591278 : CollatzResearch.WordTrace tailWord_1591278 prefixEnd_1591278 363151319522369044980823 := by
  unfold tailWord_1591278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254834591134881186362811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38692451152719366327268325 7254834591134881186362811)
  ·
    refine ⟨10882251886702321779544217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7254834591134881186362811 10882251886702321779544217)
    ·
      refine ⟨8161688915026741334658163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10882251886702321779544217 8161688915026741334658163)
      ·
        refine ⟨12242533372540112001987245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161688915026741334658163 12242533372540112001987245)
        ·
          refine ⟨4590950014702542000745217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12242533372540112001987245 4590950014702542000745217)
          ·
            refine ⟨3443212511026906500558913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4590950014702542000745217 3443212511026906500558913)
            ·
              refine ⟨2582409383270179875419185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443212511026906500558913 2582409383270179875419185)
              ·
                refine ⟨1936807037452634906564389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2582409383270179875419185 1936807037452634906564389)
                ·
                  refine ⟨363151319522369044980823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936807037452634906564389 363151319522369044980823)
                  ·
                    rfl

theorem cell21_1591278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_1591278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591278 prefixEnd_1591278 := by exact prefixLift 1591278
  have htrace : WordTrace (prefixWord ++ tailWord_1591278) baseStart_1591278 baseEnd_1591278 := by
    simpa [prefixWord, tailWord_1591278, baseEnd_1591278] using wordTrace_append hprefix tailTrace_1591278
  have hstable : (prefixWord ++ tailWord_1591278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591278).length < 2 ^ (prefixWord ++ tailWord_1591278).sum := by decide
  have hdescent : baseEnd_1591278 < baseStart_1591278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591281 : List Nat := [1, 2, 2, 2, 5, 2, 2, 2, 3]
def baseStart_1591281 : Nat := 118140960795 + 1591281 * 2 ^ 59
def prefixEnd_1591281 : Nat := 4983230072969 + 3 ^ 40 * 1591281 * 2
def baseEnd_1591281 : Nat := 363152004163241706430817

theorem tailTrace_1591281 : CollatzResearch.WordTrace tailWord_1591281 prefixEnd_1591281 363152004163241706430817 := by
  unfold tailWord_1591281
  simp only [CollatzResearch.WordTrace]
  refine ⟨58038786148068181003261697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38692524098712120668841131 58038786148068181003261697)
  ·
    refine ⟨43529089611051135752446273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58038786148068181003261697 43529089611051135752446273)
    ·
      refine ⟨32646817208288351814334705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43529089611051135752446273 32646817208288351814334705)
      ·
        refine ⟨24485112906216263860751029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32646817208288351814334705 24485112906216263860751029)
        ·
          refine ⟨2295479334957774736945409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24485112906216263860751029 2295479334957774736945409)
          ·
            refine ⟨1721609501218331052709057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2295479334957774736945409 1721609501218331052709057)
            ·
              refine ⟨1291207125913748289531793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721609501218331052709057 1291207125913748289531793)
              ·
                refine ⟨968405344435311217148845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291207125913748289531793 968405344435311217148845)
                ·
                  refine ⟨363152004163241706430817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968405344435311217148845 363152004163241706430817)
                  ·
                    rfl

theorem cell21_1591281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_1591281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591281 prefixEnd_1591281 := by exact prefixLift 1591281
  have htrace : WordTrace (prefixWord ++ tailWord_1591281) baseStart_1591281 baseEnd_1591281 := by
    simpa [prefixWord, tailWord_1591281, baseEnd_1591281] using wordTrace_append hprefix tailTrace_1591281
  have hstable : (prefixWord ++ tailWord_1591281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591281).length < 2 ^ (prefixWord ++ tailWord_1591281).sum := by decide
  have hdescent : baseEnd_1591281 < baseStart_1591281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591320 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_1591320 : Nat := 118140960795 + 1591320 * 2 ^ 59
def prefixEnd_1591320 : Nat := 4983230072969 + 3 ^ 40 * 1591320 * 2
def baseEnd_1591320 : Nat := 363160904494586305280737

theorem tailTrace_1591320 : CollatzResearch.WordTrace tailWord_1591320 prefixEnd_1591320 363160904494586305280737 := by
  unfold tailWord_1591320
  simp only [CollatzResearch.WordTrace]
  refine ⟨29020104297463445331965707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38693472396617927109287609 29020104297463445331965707)
  ·
    refine ⟨43530156446195167997948561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29020104297463445331965707 43530156446195167997948561)
    ·
      refine ⟨32647617334646375998461421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43530156446195167997948561 32647617334646375998461421)
      ·
        refine ⟨12242856500492390999423033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32647617334646375998461421 12242856500492390999423033)
        ·
          refine ⟨9182142375369293249567275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12242856500492390999423033 9182142375369293249567275)
          ·
            refine ⟨13773213563053939874350913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9182142375369293249567275 13773213563053939874350913)
            ·
              refine ⟨10329910172290454905763185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13773213563053939874350913 10329910172290454905763185)
              ·
                refine ⟨7747432629217841179322389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10329910172290454905763185 7747432629217841179322389)
                ·
                  refine ⟨363160904494586305280737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7747432629217841179322389 363160904494586305280737)
                  ·
                    rfl

theorem cell21_1591320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_1591320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591320 prefixEnd_1591320 := by exact prefixLift 1591320
  have htrace : WordTrace (prefixWord ++ tailWord_1591320) baseStart_1591320 baseEnd_1591320 := by
    simpa [prefixWord, tailWord_1591320, baseEnd_1591320] using wordTrace_append hprefix tailTrace_1591320
  have hstable : (prefixWord ++ tailWord_1591320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591320).length < 2 ^ (prefixWord ++ tailWord_1591320).sum := by decide
  have hdescent : baseEnd_1591320 < baseStart_1591320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591396 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_1591396 : Nat := 118140960795 + 1591396 * 2 ^ 59
def prefixEnd_1591396 : Nat := 4983230072969 + 3 ^ 40 * 1591396 * 2
def baseEnd_1591396 : Nat := 363178248730027062013915

theorem tailTrace_1591396 : CollatzResearch.WordTrace tailWord_1591396 prefixEnd_1591396 363178248730027062013915 := by
  unfold tailWord_1591396
  simp only [CollatzResearch.WordTrace]
  refine ⟨29021490271325777821849021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38695320361767703762465361 29021490271325777821849021)
  ·
    refine ⟨10883058851747166683193383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29021490271325777821849021 10883058851747166683193383)
    ·
      refine ⟨16324588277620750024790075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10883058851747166683193383 16324588277620750024790075)
      ·
        refine ⟨24486882416431125037185113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16324588277620750024790075 24486882416431125037185113)
        ·
          refine ⟨18365161812323343777888835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24486882416431125037185113 18365161812323343777888835)
          ·
            refine ⟨27547742718485015666833253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18365161812323343777888835 27547742718485015666833253)
            ·
              refine ⟨5165201759715940437531235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27547742718485015666833253 5165201759715940437531235)
              ·
                refine ⟨7747802639573910656296853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5165201759715940437531235 7747802639573910656296853)
                ·
                  refine ⟨363178248730027062013915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7747802639573910656296853 363178248730027062013915)
                  ·
                    rfl

theorem cell21_1591396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_1591396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591396 prefixEnd_1591396 := by exact prefixLift 1591396
  have htrace : WordTrace (prefixWord ++ tailWord_1591396) baseStart_1591396 baseEnd_1591396 := by
    simpa [prefixWord, tailWord_1591396, baseEnd_1591396] using wordTrace_append hprefix tailTrace_1591396
  have hstable : (prefixWord ++ tailWord_1591396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591396).length < 2 ^ (prefixWord ++ tailWord_1591396).sum := by decide
  have hdescent : baseEnd_1591396 < baseStart_1591396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591444 : List Nat := [2, 4, 2, 3, 1, 9]
def baseStart_1591444 : Nat := 118140960795 + 1591444 * 2 ^ 59
def prefixEnd_1591444 : Nat := 4983230072969 + 3 ^ 40 * 1591444 * 2
def baseEnd_1591444 : Nat := 13451451962369986859771

theorem tailTrace_1591444 : CollatzResearch.WordTrace tailWord_1591444 prefixEnd_1591444 13451451962369986859771 := by
  unfold tailWord_1591444
  simp only [CollatzResearch.WordTrace]
  refine ⟨29022365623238829920722693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38696487497651773227630257 29022365623238829920722693)
  ·
    refine ⟨5441693554357280610135505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29022365623238829920722693 5441693554357280610135505)
    ·
      refine ⟨4081270165767960457601629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5441693554357280610135505 4081270165767960457601629)
      ·
        refine ⟨1530476312162985171600611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4081270165767960457601629 1530476312162985171600611)
        ·
          refine ⟨2295714468244477757400917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530476312162985171600611 2295714468244477757400917)
          ·
            refine ⟨13451451962369986859771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2295714468244477757400917 13451451962369986859771)
            ·
              rfl

theorem cell21_1591444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 9].length) (baseStart_1591444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591444 prefixEnd_1591444 := by exact prefixLift 1591444
  have htrace : WordTrace (prefixWord ++ tailWord_1591444) baseStart_1591444 baseEnd_1591444 := by
    simpa [prefixWord, tailWord_1591444, baseEnd_1591444] using wordTrace_append hprefix tailTrace_1591444
  have hstable : (prefixWord ++ tailWord_1591444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591444).length < 2 ^ (prefixWord ++ tailWord_1591444).sum := by decide
  have hdescent : baseEnd_1591444 < baseStart_1591444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591450 : List Nat := [3, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_1591450 : Nat := 118140960795 + 1591450 * 2 ^ 59
def prefixEnd_1591450 : Nat := 4983230072969 + 3 ^ 40 * 1591450 * 2
def baseEnd_1591450 : Nat := 363190572265734968113805

theorem tailTrace_1591450 : CollatzResearch.WordTrace tailWord_1591450 prefixEnd_1591450 363190572265734968113805 := by
  unfold tailWord_1591450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14511237521113980716540951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38696633389637281910775869 14511237521113980716540951)
  ·
    refine ⟨21766856281670971074811427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14511237521113980716540951 21766856281670971074811427)
    ·
      refine ⟨32650284422506456612217141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21766856281670971074811427 32650284422506456612217141)
      ·
        refine ⟨3060964164609980307395357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32650284422506456612217141 3060964164609980307395357)
        ·
          refine ⟨1147861561728742615273259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3060964164609980307395357 1147861561728742615273259)
          ·
            refine ⟨1721792342593113922909889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147861561728742615273259 1721792342593113922909889)
            ·
              refine ⟨1291344256944835442182417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721792342593113922909889 1291344256944835442182417)
              ·
                refine ⟨968508192708626581636813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291344256944835442182417 968508192708626581636813)
                ·
                  refine ⟨363190572265734968113805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968508192708626581636813 363190572265734968113805)
                  ·
                    rfl

theorem cell21_1591450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_1591450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591450 prefixEnd_1591450 := by exact prefixLift 1591450
  have htrace : WordTrace (prefixWord ++ tailWord_1591450) baseStart_1591450 baseEnd_1591450 := by
    simpa [prefixWord, tailWord_1591450, baseEnd_1591450] using wordTrace_append hprefix tailTrace_1591450
  have hstable : (prefixWord ++ tailWord_1591450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591450).length < 2 ^ (prefixWord ++ tailWord_1591450).sum := by decide
  have hdescent : baseEnd_1591450 < baseStart_1591450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591492 : List Nat := [2, 3, 3, 1, 2, 2, 2, 3, 3]
def baseStart_1591492 : Nat := 118140960795 + 1591492 * 2 ^ 59
def prefixEnd_1591492 : Nat := 4983230072969 + 3 ^ 40 * 1591492 * 2
def baseEnd_1591492 : Nat := 363200157237952228413719

theorem tailTrace_1591492 : CollatzResearch.WordTrace tailWord_1591492 prefixEnd_1591492 363200157237952228413719 := by
  unfold tailWord_1591492
  simp only [CollatzResearch.WordTrace]
  refine ⟨29023240975151882019596365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38697654633535842692795153 29023240975151882019596365)
  ·
    refine ⟨10883715365681955757348637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29023240975151882019596365 10883715365681955757348637)
    ·
      refine ⟨4081393262130733409005739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10883715365681955757348637 4081393262130733409005739)
      ·
        refine ⟨6122089893196100113508609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4081393262130733409005739 6122089893196100113508609)
        ·
          refine ⟨4591567419897075085131457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6122089893196100113508609 4591567419897075085131457)
          ·
            refine ⟨3443675564922806313848593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4591567419897075085131457 3443675564922806313848593)
            ·
              refine ⟨2582756673692104735386445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443675564922806313848593 2582756673692104735386445)
              ·
                refine ⟨968533752634539275769917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2582756673692104735386445 968533752634539275769917)
                ·
                  refine ⟨363200157237952228413719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968533752634539275769917 363200157237952228413719)
                  ·
                    rfl

theorem cell21_1591492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_1591492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591492 prefixEnd_1591492 := by exact prefixLift 1591492
  have htrace : WordTrace (prefixWord ++ tailWord_1591492) baseStart_1591492 baseEnd_1591492 := by
    simpa [prefixWord, tailWord_1591492, baseEnd_1591492] using wordTrace_append hprefix tailTrace_1591492
  have hstable : (prefixWord ++ tailWord_1591492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591492).length < 2 ^ (prefixWord ++ tailWord_1591492).sum := by decide
  have hdescent : baseEnd_1591492 < baseStart_1591492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591506 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1591506 : Nat := 118140960795 + 1591506 * 2 ^ 59
def prefixEnd_1591506 : Nat := 4983230072969 + 3 ^ 40 * 1591506 * 2
def baseEnd_1591506 : Nat := 363203352228691315180357

theorem tailTrace_1591506 : CollatzResearch.WordTrace tailWord_1591506 prefixEnd_1591506 363203352228691315180357 := by
  unfold tailWord_1591506
  simp only [CollatzResearch.WordTrace]
  refine ⟨14511748143063261107550593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38697995048168696286801581 14511748143063261107550593)
  ·
    refine ⟨10883811107297445830662945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14511748143063261107550593 10883811107297445830662945)
    ·
      refine ⟨8162858330473084372997209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10883811107297445830662945 8162858330473084372997209)
      ·
        refine ⟨6122143747854813279747907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8162858330473084372997209 6122143747854813279747907)
        ·
          refine ⟨9183215621782219919621861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6122143747854813279747907 9183215621782219919621861)
          ·
            refine ⟨1721852929084166234929099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9183215621782219919621861 1721852929084166234929099)
            ·
              refine ⟨2582779393626249352393649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721852929084166234929099 2582779393626249352393649)
              ·
                refine ⟨1937084545219687014295237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2582779393626249352393649 1937084545219687014295237)
                ·
                  refine ⟨363203352228691315180357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937084545219687014295237 363203352228691315180357)
                  ·
                    rfl

theorem cell21_1591506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1591506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591506 prefixEnd_1591506 := by exact prefixLift 1591506
  have htrace : WordTrace (prefixWord ++ tailWord_1591506) baseStart_1591506 baseEnd_1591506 := by
    simpa [prefixWord, tailWord_1591506, baseEnd_1591506] using wordTrace_append hprefix tailTrace_1591506
  have hstable : (prefixWord ++ tailWord_1591506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591506).length < 2 ^ (prefixWord ++ tailWord_1591506).sum := by decide
  have hdescent : baseEnd_1591506 < baseStart_1591506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591523 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 4]
def baseStart_1591523 : Nat := 118140960795 + 1591523 * 2 ^ 59
def prefixEnd_1591523 : Nat := 4983230072969 + 3 ^ 40 * 1591523 * 2
def baseEnd_1591523 : Nat := 363207231860303063396989

theorem tailTrace_1591523 : CollatzResearch.WordTrace tailWord_1591523 prefixEnd_1591523 363207231860303063396989 := by
  unfold tailWord_1591523
  simp only [CollatzResearch.WordTrace]
  refine ⟨58047612613191456333571223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38698408408794304222380815 58047612613191456333571223)
  ·
    refine ⟨87071418919787184500356835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58047612613191456333571223 87071418919787184500356835)
    ·
      refine ⟨130607128379680776750535253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87071418919787184500356835 130607128379680776750535253)
      ·
        refine ⟨1530552285699384102545335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 130607128379680776750535253 1530552285699384102545335)
        ·
          refine ⟨2295828428549076153818003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530552285699384102545335 2295828428549076153818003)
          ·
            refine ⟨3443742642823614230727005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295828428549076153818003 3443742642823614230727005)
            ·
              refine ⟨1291403491058855336522627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3443742642823614230727005 1291403491058855336522627)
              ·
                refine ⟨1937105236588283004783941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291403491058855336522627 1937105236588283004783941)
                ·
                  refine ⟨363207231860303063396989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937105236588283004783941 363207231860303063396989)
                  ·
                    rfl

theorem cell21_1591523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 4].length) (baseStart_1591523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591523 prefixEnd_1591523 := by exact prefixLift 1591523
  have htrace : WordTrace (prefixWord ++ tailWord_1591523) baseStart_1591523 baseEnd_1591523 := by
    simpa [prefixWord, tailWord_1591523, baseEnd_1591523] using wordTrace_append hprefix tailTrace_1591523
  have hstable : (prefixWord ++ tailWord_1591523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591523).length < 2 ^ (prefixWord ++ tailWord_1591523).sum := by decide
  have hdescent : baseEnd_1591523 < baseStart_1591523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591548 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_1591548 : Nat := 118140960795 + 1591548 * 2 ^ 59
def prefixEnd_1591548 : Nat := 4983230072969 + 3 ^ 40 * 1591548 * 2
def baseEnd_1591548 : Nat := 363212937200908575480271

theorem tailTrace_1591548 : CollatzResearch.WordTrace tailWord_1591548 prefixEnd_1591548 363212937200908575480271 := by
  unfold tailWord_1591548
  simp only [CollatzResearch.WordTrace]
  refine ⟨29024262219050442801615649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38699016292067257068820865 29024262219050442801615649)
  ·
    refine ⟨21768196664287832101211737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29024262219050442801615649 21768196664287832101211737)
    ·
      refine ⟨16326147498215874075908803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21768196664287832101211737 16326147498215874075908803)
      ·
        refine ⟨24489221247323811113863205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16326147498215874075908803 24489221247323811113863205)
        ·
          refine ⟨4591728983873214583849351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24489221247323811113863205 4591728983873214583849351)
          ·
            refine ⟨6887593475809821875774027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591728983873214583849351 6887593475809821875774027)
            ·
              refine ⟨10331390213714732813661041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6887593475809821875774027 10331390213714732813661041)
              ·
                refine ⟨7748542660286049610245781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10331390213714732813661041 7748542660286049610245781)
                ·
                  refine ⟨363212937200908575480271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7748542660286049610245781 363212937200908575480271)
                  ·
                    rfl

theorem cell21_1591548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_1591548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591548 prefixEnd_1591548 := by exact prefixLift 1591548
  have htrace : WordTrace (prefixWord ++ tailWord_1591548) baseStart_1591548 baseEnd_1591548 := by
    simpa [prefixWord, tailWord_1591548, baseEnd_1591548] using wordTrace_append hprefix tailTrace_1591548
  have hstable : (prefixWord ++ tailWord_1591548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591548).length < 2 ^ (prefixWord ++ tailWord_1591548).sum := by decide
  have hdescent : baseEnd_1591548 < baseStart_1591548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591562 : List Nat := [3, 1, 2, 2, 1, 1, 11]
def baseStart_1591562 : Nat := 118140960795 + 1591562 * 2 ^ 59
def prefixEnd_1591562 : Nat := 4983230072969 + 3 ^ 40 * 1591562 * 2
def baseEnd_1591562 : Nat := 40357348021294184694101

theorem tailTrace_1591562 : CollatzResearch.WordTrace tailWord_1591562 prefixEnd_1591562 40357348021294184694101 := by
  unfold tailWord_1591562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14512258765012541498560235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38699356706700110662827293 14512258765012541498560235)
  ·
    refine ⟨21768388147518812247840353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14512258765012541498560235 21768388147518812247840353)
    ·
      refine ⟨16326291110639109185880265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21768388147518812247840353 16326291110639109185880265)
      ·
        refine ⟨12244718332979331889410199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16326291110639109185880265 12244718332979331889410199)
        ·
          refine ⟨18367077499468997834115299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12244718332979331889410199 18367077499468997834115299)
          ·
            refine ⟨27550616249203496751172949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18367077499468997834115299 27550616249203496751172949)
            ·
              refine ⟨40357348021294184694101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27550616249203496751172949 40357348021294184694101)
              ·
                rfl

theorem cell21_1591562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 11].length) (baseStart_1591562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591562 prefixEnd_1591562 := by exact prefixLift 1591562
  have htrace : WordTrace (prefixWord ++ tailWord_1591562) baseStart_1591562 baseEnd_1591562 := by
    simpa [prefixWord, tailWord_1591562, baseEnd_1591562] using wordTrace_append hprefix tailTrace_1591562
  have hstable : (prefixWord ++ tailWord_1591562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591562).length < 2 ^ (prefixWord ++ tailWord_1591562).sum := by decide
  have hdescent : baseEnd_1591562 < baseStart_1591562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591607 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 8]
def baseStart_1591607 : Nat := 118140960795 + 1591607 * 2 ^ 59
def prefixEnd_1591607 : Nat := 4983230072969 + 3 ^ 40 * 1591607 * 2
def baseEnd_1591607 : Nat := 363226401804737583996817

theorem tailTrace_1591607 : CollatzResearch.WordTrace tailWord_1591607 prefixEnd_1591607 363226401804737583996817 := by
  unfold tailWord_1591607
  simp only [CollatzResearch.WordTrace]
  refine ⟨58050676344887138679629075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38700450896591425786419383 58050676344887138679629075)
  ·
    refine ⟨87076014517330708019443613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58050676344887138679629075 87076014517330708019443613)
    ·
      refine ⟨32653505443999015507291355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87076014517330708019443613 32653505443999015507291355)
      ·
        refine ⟨48980258165998523260937033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32653505443999015507291355 48980258165998523260937033)
        ·
          refine ⟨36735193624498892445702775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48980258165998523260937033 36735193624498892445702775)
          ·
            refine ⟨55102790436748338668554163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36735193624498892445702775 55102790436748338668554163)
            ·
              refine ⟨82654185655122508002831245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55102790436748338668554163 82654185655122508002831245)
              ·
                refine ⟨30995319620670940501061717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82654185655122508002831245 30995319620670940501061717)
                ·
                  refine ⟨363226401804737583996817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30995319620670940501061717 363226401804737583996817)
                  ·
                    rfl

theorem cell21_1591607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_1591607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591607 prefixEnd_1591607 := by exact prefixLift 1591607
  have htrace : WordTrace (prefixWord ++ tailWord_1591607) baseStart_1591607 baseEnd_1591607 := by
    simpa [prefixWord, tailWord_1591607, baseEnd_1591607] using wordTrace_append hprefix tailTrace_1591607
  have hstable : (prefixWord ++ tailWord_1591607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591607).length < 2 ^ (prefixWord ++ tailWord_1591607).sum := by decide
  have hdescent : baseEnd_1591607 < baseStart_1591607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591624 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_1591624 : Nat := 118140960795 + 1591624 * 2 ^ 59
def prefixEnd_1591624 : Nat := 4983230072969 + 3 ^ 40 * 1591624 * 2
def baseEnd_1591624 : Nat := 363230281436349332213449

theorem tailTrace_1591624 : CollatzResearch.WordTrace tailWord_1591624 prefixEnd_1591624 363230281436349332213449 := by
  unfold tailWord_1591624
  simp only [CollatzResearch.WordTrace]
  refine ⟨29025648192912775291498963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38700864257217033721998617 29025648192912775291498963)
  ·
    refine ⟨43538472289369162937248445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29025648192912775291498963 43538472289369162937248445)
    ·
      refine ⟨16326927108513436101468167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43538472289369162937248445 16326927108513436101468167)
      ·
        refine ⟨24490390662770154152202251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16326927108513436101468167 24490390662770154152202251)
        ·
          refine ⟨36735585994155231228303377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24490390662770154152202251 36735585994155231228303377)
          ·
            refine ⟨27551689495616423421227533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36735585994155231228303377 27551689495616423421227533)
            ·
              refine ⟨10331883560856158782960325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27551689495616423421227533 10331883560856158782960325)
              ·
                refine ⟨1937228167660529771805061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10331883560856158782960325 1937228167660529771805061)
                ·
                  refine ⟨363230281436349332213449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937228167660529771805061 363230281436349332213449)
                  ·
                    rfl

theorem cell21_1591624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_1591624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591624 prefixEnd_1591624 := by exact prefixLift 1591624
  have htrace : WordTrace (prefixWord ++ tailWord_1591624) baseStart_1591624 baseEnd_1591624 := by
    simpa [prefixWord, tailWord_1591624, baseEnd_1591624] using wordTrace_append hprefix tailTrace_1591624
  have hstable : (prefixWord ++ tailWord_1591624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591624).length < 2 ^ (prefixWord ++ tailWord_1591624).sum := by decide
  have hdescent : baseEnd_1591624 < baseStart_1591624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591720 : List Nat := [2, 1, 6, 1, 1, 1, 3, 3, 3]
def baseStart_1591720 : Nat := 118140960795 + 1591720 * 2 ^ 59
def prefixEnd_1591720 : Nat := 4983230072969 + 3 ^ 40 * 1591720 * 2
def baseEnd_1591720 : Nat := 363252189944274498613253

theorem tailTrace_1591720 : CollatzResearch.WordTrace tailWord_1591720 prefixEnd_1591720 363252189944274498613253 := by
  unfold tailWord_1591720
  simp only [CollatzResearch.WordTrace]
  refine ⟨29027398896738879489246307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38703198528985172652328409 29027398896738879489246307)
  ·
    refine ⟨43541098345108319233869461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29027398896738879489246307 43541098345108319233869461)
    ·
      refine ⟨2040988984926952464087631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43541098345108319233869461 2040988984926952464087631)
      ·
        refine ⟨3061483477390428696131447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040988984926952464087631 3061483477390428696131447)
        ·
          refine ⟨4592225216085643044197171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061483477390428696131447 4592225216085643044197171)
          ·
            refine ⟨6888337824128464566295757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592225216085643044197171 6888337824128464566295757)
            ·
              refine ⟨2583126684048174212360909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6888337824128464566295757 2583126684048174212360909)
              ·
                refine ⟨968672506518065329635341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2583126684048174212360909 968672506518065329635341)
                ·
                  refine ⟨363252189944274498613253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968672506518065329635341 363252189944274498613253)
                  ·
                    rfl

theorem cell21_1591720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_1591720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591720 prefixEnd_1591720 := by exact prefixLift 1591720
  have htrace : WordTrace (prefixWord ++ tailWord_1591720) baseStart_1591720 baseEnd_1591720 := by
    simpa [prefixWord, tailWord_1591720, baseEnd_1591720] using wordTrace_append hprefix tailTrace_1591720
  have hstable : (prefixWord ++ tailWord_1591720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591720).length < 2 ^ (prefixWord ++ tailWord_1591720).sum := by decide
  have hdescent : baseEnd_1591720 < baseStart_1591720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591748 : List Nat := [2, 3, 3, 2, 2, 1, 2, 6]
def baseStart_1591748 : Nat := 118140960795 + 1591748 * 2 ^ 59
def prefixEnd_1591748 : Nat := 4983230072969 + 3 ^ 40 * 1591748 * 2
def baseEnd_1591748 : Nat := 121086193308584224048843

theorem tailTrace_1591748 : CollatzResearch.WordTrace tailWord_1591748 prefixEnd_1591748 121086193308584224048843 := by
  unfold tailWord_1591748
  simp only [CollatzResearch.WordTrace]
  refine ⟨29027909518688159880255949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38703879358250879840341265 29027909518688159880255949)
  ·
    refine ⟨10885466069508059955095981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29027909518688159880255949 10885466069508059955095981)
    ·
      refine ⟨4082049776065522483160993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10885466069508059955095981 4082049776065522483160993)
      ·
        refine ⟨3061537332049141862370745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4082049776065522483160993 3061537332049141862370745)
        ·
          refine ⟨2296152999036856396778059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3061537332049141862370745 2296152999036856396778059)
          ·
            refine ⟨3444229498555284595167089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296152999036856396778059 3444229498555284595167089)
            ·
              refine ⟨2583172123916463446375317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444229498555284595167089 2583172123916463446375317)
              ·
                refine ⟨121086193308584224048843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2583172123916463446375317 121086193308584224048843)
                ·
                  rfl

theorem cell21_1591748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_1591748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591748 prefixEnd_1591748 := by exact prefixLift 1591748
  have htrace : WordTrace (prefixWord ++ tailWord_1591748) baseStart_1591748 baseEnd_1591748 := by
    simpa [prefixWord, tailWord_1591748, baseEnd_1591748] using wordTrace_append hprefix tailTrace_1591748
  have hstable : (prefixWord ++ tailWord_1591748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591748).length < 2 ^ (prefixWord ++ tailWord_1591748).sum := by decide
  have hdescent : baseEnd_1591748 < baseStart_1591748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591790 : List Nat := [4, 1, 2, 1, 2, 11]
def baseStart_1591790 : Nat := 118140960795 + 1591790 * 2 ^ 59
def prefixEnd_1591790 : Nat := 4983230072969 + 3 ^ 40 * 1591790 * 2
def baseEnd_1591790 : Nat := 13454376477702590090609

theorem tailTrace_1591790 : CollatzResearch.WordTrace tailWord_1591790 prefixEnd_1591790 13454376477702590090609 := by
  unfold tailWord_1591790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257168862903020116692603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38704900602149440622360549 7257168862903020116692603)
  ·
    refine ⟨10885753294354530175038905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7257168862903020116692603 10885753294354530175038905)
    ·
      refine ⟨8164314970765897631279179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10885753294354530175038905 8164314970765897631279179)
      ·
        refine ⟨12246472456148846446918769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8164314970765897631279179 12246472456148846446918769)
        ·
          refine ⟨9184854342111634835189077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12246472456148846446918769 9184854342111634835189077)
          ·
            refine ⟨13454376477702590090609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9184854342111634835189077 13454376477702590090609)
            ·
              rfl

theorem cell21_1591790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 11].length) (baseStart_1591790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591790 prefixEnd_1591790 := by exact prefixLift 1591790
  have htrace : WordTrace (prefixWord ++ tailWord_1591790) baseStart_1591790 baseEnd_1591790 := by
    simpa [prefixWord, tailWord_1591790, baseEnd_1591790] using wordTrace_append hprefix tailTrace_1591790
  have hstable : (prefixWord ++ tailWord_1591790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591790).length < 2 ^ (prefixWord ++ tailWord_1591790).sum := by decide
  have hdescent : baseEnd_1591790 < baseStart_1591790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591900 : List Nat := [2, 2, 4, 1, 4, 1, 7]
def baseStart_1591900 : Nat := 118140960795 + 1591900 * 2 ^ 59
def prefixEnd_1591900 : Nat := 4983230072969 + 3 ^ 40 * 1591900 * 2
def baseEnd_1591900 : Nat := 40365918710737131734765

theorem tailTrace_1591900 : CollatzResearch.WordTrace tailWord_1591900 prefixEnd_1591900 40365918710737131734765 := by
  unfold tailWord_1591900
  simp only [CollatzResearch.WordTrace]
  refine ⟨29030681466412824860022577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38707575288550433146696769 29030681466412824860022577)
  ·
    refine ⟨21773011099809618645016933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29030681466412824860022577 21773011099809618645016933)
    ·
      refine ⟨4082439581214303495940675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21773011099809618645016933 4082439581214303495940675)
      ·
        refine ⟨6123659371821455243911013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082439581214303495940675 6123659371821455243911013)
        ·
          refine ⟨1148186132216522858233315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6123659371821455243911013 1148186132216522858233315)
          ·
            refine ⟨1722279198324784287349973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148186132216522858233315 1722279198324784287349973)
            ·
              refine ⟨40365918710737131734765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1722279198324784287349973 40365918710737131734765)
              ·
                rfl

theorem cell21_1591900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 7].length) (baseStart_1591900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591900 prefixEnd_1591900 := by exact prefixLift 1591900
  have htrace : WordTrace (prefixWord ++ tailWord_1591900) baseStart_1591900 baseEnd_1591900 := by
    simpa [prefixWord, tailWord_1591900, baseEnd_1591900] using wordTrace_append hprefix tailTrace_1591900
  have hstable : (prefixWord ++ tailWord_1591900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591900).length < 2 ^ (prefixWord ++ tailWord_1591900).sum := by decide
  have hdescent : baseEnd_1591900 < baseStart_1591900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591962 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_1591962 : Nat := 118140960795 + 1591962 * 2 ^ 59
def prefixEnd_1591962 : Nat := 4983230072969 + 3 ^ 40 * 1591962 * 2
def baseEnd_1591962 : Nat := 363307417641335855579425

theorem tailTrace_1591962 : CollatzResearch.WordTrace tailWord_1591962 prefixEnd_1591962 363307417641335855579425 := by
  unfold tailWord_1591962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14515906064650258577200535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38709082839067356205868093 14515906064650258577200535)
  ·
    refine ⟨21773859096975387865800803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14515906064650258577200535 21773859096975387865800803)
    ·
      refine ⟨32660788645463081798701205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21773859096975387865800803 32660788645463081798701205)
      ·
        refine ⟨1530974467756081959314119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32660788645463081798701205 1530974467756081959314119)
        ·
          refine ⟨2296461701634122938971179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530974467756081959314119 2296461701634122938971179)
          ·
            refine ⟨3444692552451184408456769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296461701634122938971179 3444692552451184408456769)
            ·
              refine ⟨2583519414338388306342577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444692552451184408456769 2583519414338388306342577)
              ·
                refine ⟨1937639560753791229756933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2583519414338388306342577 1937639560753791229756933)
                ·
                  refine ⟨363307417641335855579425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937639560753791229756933 363307417641335855579425)
                  ·
                    rfl

theorem cell21_1591962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_1591962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1591962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1591962 prefixEnd_1591962 := by exact prefixLift 1591962
  have htrace : WordTrace (prefixWord ++ tailWord_1591962) baseStart_1591962 baseEnd_1591962 := by
    simpa [prefixWord, tailWord_1591962, baseEnd_1591962] using wordTrace_append hprefix tailTrace_1591962
  have hstable : (prefixWord ++ tailWord_1591962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591962).length < 2 ^ (prefixWord ++ tailWord_1591962).sum := by decide
  have hdescent : baseEnd_1591962 < baseStart_1591962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592021 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 6]
def baseStart_1592021 : Nat := 118140960795 + 1592021 * 2 ^ 59
def prefixEnd_1592021 : Nat := 4983230072969 + 3 ^ 40 * 1592021 * 2
def baseEnd_1592021 : Nat := 363320882245164864095971

theorem tailTrace_1592021 : CollatzResearch.WordTrace tailWord_1592021 prefixEnd_1592021 363320882245164864095971 := by
  unfold tailWord_1592021
  simp only [CollatzResearch.WordTrace]
  refine ⟨58065776165387287385199917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38710517443591524923466611 58065776165387287385199917)
  ·
    refine ⟨21774666062020232769449969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58065776165387287385199917 21774666062020232769449969)
    ·
      refine ⟨16330999546515174577087477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21774666062020232769449969 16330999546515174577087477)
      ·
        refine ⟨1531031207485797616601951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16330999546515174577087477 1531031207485797616601951)
        ·
          refine ⟨2296546811228696424902927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531031207485797616601951 2296546811228696424902927)
          ·
            refine ⟨3444820216843044637354391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296546811228696424902927 3444820216843044637354391)
            ·
              refine ⟨5167230325264566956031587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444820216843044637354391 5167230325264566956031587)
              ·
                refine ⟨7750845487896850434047381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167230325264566956031587 7750845487896850434047381)
                ·
                  refine ⟨363320882245164864095971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7750845487896850434047381 363320882245164864095971)
                  ·
                    rfl

theorem cell21_1592021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_1592021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592021 prefixEnd_1592021 := by exact prefixLift 1592021
  have htrace : WordTrace (prefixWord ++ tailWord_1592021) baseStart_1592021 baseEnd_1592021 := by
    simpa [prefixWord, tailWord_1592021, baseEnd_1592021] using wordTrace_append hprefix tailTrace_1592021
  have hstable : (prefixWord ++ tailWord_1592021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592021).length < 2 ^ (prefixWord ++ tailWord_1592021).sum := by decide
  have hdescent : baseEnd_1592021 < baseStart_1592021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592108 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_1592108 : Nat := 118140960795 + 1592108 * 2 ^ 59
def prefixEnd_1592108 : Nat := 4983230072969 + 3 ^ 40 * 1592108 * 2
def baseEnd_1592108 : Nat := 363340736830472046145793

theorem tailTrace_1592108 : CollatzResearch.WordTrace tailWord_1592108 prefixEnd_1592108 363340736830472046145793 := by
  unfold tailWord_1592108
  simp only [CollatzResearch.WordTrace]
  refine ⟨29034474658036050621808489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38712632877381400829077985 29034474658036050621808489)
  ·
    refine ⟨21775855993527037966356367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29034474658036050621808489 21775855993527037966356367)
    ·
      refine ⟨32663783990290556949534551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21775855993527037966356367 32663783990290556949534551)
      ·
        refine ⟨48995675985435835424301827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32663783990290556949534551 48995675985435835424301827)
        ·
          refine ⟨73493513978153753136452741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48995675985435835424301827 73493513978153753136452741)
          ·
            refine ⟨13780033870903828713084889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73493513978153753136452741 13780033870903828713084889)
            ·
              refine ⟨10335025403177871534813667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13780033870903828713084889 10335025403177871534813667)
              ·
                refine ⟨15502538104766807302220501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10335025403177871534813667 15502538104766807302220501)
                ·
                  refine ⟨363340736830472046145793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15502538104766807302220501 363340736830472046145793)
                  ·
                    rfl

theorem cell21_1592108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_1592108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592108 prefixEnd_1592108 := by exact prefixLift 1592108
  have htrace : WordTrace (prefixWord ++ tailWord_1592108) baseStart_1592108 baseEnd_1592108 := by
    simpa [prefixWord, tailWord_1592108, baseEnd_1592108] using wordTrace_append hprefix tailTrace_1592108
  have hstable : (prefixWord ++ tailWord_1592108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592108).length < 2 ^ (prefixWord ++ tailWord_1592108).sum := by decide
  have hdescent : baseEnd_1592108 < baseStart_1592108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592134 : List Nat := [6, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1592134 : Nat := 118140960795 + 1592134 * 2 ^ 59
def prefixEnd_1592134 : Nat := 4983230072969 + 3 ^ 40 * 1592134 * 2
def baseEnd_1592134 : Nat := 363346670384701778712407

theorem tailTrace_1592134 : CollatzResearch.WordTrace tailWord_1592134 prefixEnd_1592134 363346670384701778712407 := by
  unfold tailWord_1592134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814684300436809615126983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38713265075985271789375637 1814684300436809615126983)
  ·
    refine ⟨2722026450655214422690475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1814684300436809615126983 2722026450655214422690475)
    ·
      refine ⟨4083039675982821634035713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722026450655214422690475 4083039675982821634035713)
      ·
        refine ⟨3062279756987116225526785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4083039675982821634035713 3062279756987116225526785)
        ·
          refine ⟨2296709817740337169145089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3062279756987116225526785 2296709817740337169145089)
          ·
            refine ⟨1722532363305252876858817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2296709817740337169145089 1722532363305252876858817)
            ·
              refine ⟨1291899272478939657644113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1722532363305252876858817 1291899272478939657644113)
              ·
                refine ⟨968924454359204743233085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291899272478939657644113 968924454359204743233085)
                ·
                  refine ⟨363346670384701778712407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968924454359204743233085 363346670384701778712407)
                  ·
                    rfl

theorem cell21_1592134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1592134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592134 prefixEnd_1592134 := by exact prefixLift 1592134
  have htrace : WordTrace (prefixWord ++ tailWord_1592134) baseStart_1592134 baseEnd_1592134 := by
    simpa [prefixWord, tailWord_1592134, baseEnd_1592134] using wordTrace_append hprefix tailTrace_1592134
  have hstable : (prefixWord ++ tailWord_1592134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592134).length < 2 ^ (prefixWord ++ tailWord_1592134).sum := by decide
  have hdescent : baseEnd_1592134 < baseStart_1592134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592201 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 5]
def baseStart_1592201 : Nat := 118140960795 + 1592201 * 2 ^ 59
def prefixEnd_1592201 : Nat := 4983230072969 + 3 ^ 40 * 1592201 * 2
def baseEnd_1592201 : Nat := 363361960697524551095603

theorem tailTrace_1592201 : CollatzResearch.WordTrace tailWord_1592201 prefixEnd_1592201 363361960697524551095603 := by
  unfold tailWord_1592201
  simp only [CollatzResearch.WordTrace]
  refine ⟨58072341304735178126752457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38714894203156785417834971 58072341304735178126752457)
  ·
    refine ⟨43554255978551383595064343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58072341304735178126752457 43554255978551383595064343)
    ·
      refine ⟨65331383967827075392596515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43554255978551383595064343 65331383967827075392596515)
      ·
        refine ⟨97997075951740613088894773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65331383967827075392596515 97997075951740613088894773)
        ·
          refine ⟨9187225870475682477083885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97997075951740613088894773 9187225870475682477083885)
          ·
            refine ⟨3445209701428380928906457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9187225870475682477083885 3445209701428380928906457)
            ·
              refine ⟨2583907276071285696679843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3445209701428380928906457 2583907276071285696679843)
              ·
                refine ⟨3875860914106928545019765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583907276071285696679843 3875860914106928545019765)
                ·
                  refine ⟨363361960697524551095603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3875860914106928545019765 363361960697524551095603)
                  ·
                    rfl

theorem cell21_1592201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_1592201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592201 prefixEnd_1592201 := by exact prefixLift 1592201
  have htrace : WordTrace (prefixWord ++ tailWord_1592201) baseStart_1592201 baseEnd_1592201 := by
    simpa [prefixWord, tailWord_1592201, baseEnd_1592201] using wordTrace_append hprefix tailTrace_1592201
  have hstable : (prefixWord ++ tailWord_1592201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592201).length < 2 ^ (prefixWord ++ tailWord_1592201).sum := by decide
  have hdescent : baseEnd_1592201 < baseStart_1592201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592305 : List Nat := [1, 2, 2, 2, 4, 10]
def baseStart_1592305 : Nat := 118140960795 + 1592305 * 2 ^ 59
def prefixEnd_1592305 : Nat := 4983230072969 + 3 ^ 40 * 1592305 * 2
def baseEnd_1592305 : Nat := 13458729441275684494891

theorem tailTrace_1592305 : CollatzResearch.WordTrace tailWord_1592305 prefixEnd_1592305 13458729441275684494891 := by
  unfold tailWord_1592305
  simp only [CollatzResearch.WordTrace]
  refine ⟨58076134496358403888538369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38717422997572269259025579 58076134496358403888538369)
  ·
    refine ⟨43557100872268802916403777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58076134496358403888538369 43557100872268802916403777)
    ·
      refine ⟨32667825654201602187302833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43557100872268802916403777 32667825654201602187302833)
      ·
        refine ⟨24500869240651201640477125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32667825654201602187302833 24500869240651201640477125)
        ·
          refine ⟨4593912982622100307589461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24500869240651201640477125 4593912982622100307589461)
          ·
            refine ⟨13458729441275684494891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4593912982622100307589461 13458729441275684494891)
            ·
              rfl

theorem cell21_1592305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 10].length) (baseStart_1592305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592305 prefixEnd_1592305 := by exact prefixLift 1592305
  have htrace : WordTrace (prefixWord ++ tailWord_1592305) baseStart_1592305 baseEnd_1592305 := by
    simpa [prefixWord, tailWord_1592305, baseEnd_1592305] using wordTrace_append hprefix tailTrace_1592305
  have hstable : (prefixWord ++ tailWord_1592305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592305).length < 2 ^ (prefixWord ++ tailWord_1592305).sum := by decide
  have hdescent : baseEnd_1592305 < baseStart_1592305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592384 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_1592384 : Nat := 118140960795 + 1592384 * 2 ^ 59
def prefixEnd_1592384 : Nat := 4983230072969 + 3 ^ 40 * 1592384 * 2
def baseEnd_1592384 : Nat := 363403723790756899545229

theorem tailTrace_1592384 : CollatzResearch.WordTrace tailWord_1592384 prefixEnd_1592384 363403723790756899545229 := by
  unfold tailWord_1592384
  simp only [CollatzResearch.WordTrace]
  refine ⟨29039507931536100190332103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38719343908714800253776137 29039507931536100190332103)
  ·
    refine ⟨43559261897304150285498155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29039507931536100190332103 43559261897304150285498155)
    ·
      refine ⟨65338892845956225428247233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43559261897304150285498155 65338892845956225428247233)
      ·
        refine ⟨49004169634467169071185425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65338892845956225428247233 49004169634467169071185425)
        ·
          refine ⟨36753127225850376803389069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49004169634467169071185425 36753127225850376803389069)
          ·
            refine ⟨13782422709693891301270901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36753127225850376803389069 13782422709693891301270901)
            ·
              refine ⟨1292102129033802309494147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13782422709693891301270901 1292102129033802309494147)
              ·
                refine ⟨1938153193550703464241221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292102129033802309494147 1938153193550703464241221)
                ·
                  refine ⟨363403723790756899545229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1938153193550703464241221 363403723790756899545229)
                  ·
                    rfl

theorem cell21_1592384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_1592384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592384 prefixEnd_1592384 := by exact prefixLift 1592384
  have htrace : WordTrace (prefixWord ++ tailWord_1592384) baseStart_1592384 baseEnd_1592384 := by
    simpa [prefixWord, tailWord_1592384, baseEnd_1592384] using wordTrace_append hprefix tailTrace_1592384
  have hstable : (prefixWord ++ tailWord_1592384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592384).length < 2 ^ (prefixWord ++ tailWord_1592384).sum := by decide
  have hdescent : baseEnd_1592384 < baseStart_1592384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592429 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1592429 : Nat := 118140960795 + 1592429 * 2 ^ 59
def prefixEnd_1592429 : Nat := 4983230072969 + 3 ^ 40 * 1592429 * 2
def baseEnd_1592429 : Nat := 363413993403846821295137

theorem tailTrace_1592429 : CollatzResearch.WordTrace tailWord_1592429 prefixEnd_1592429 363413993403846821295137 := by
  unfold tailWord_1592429
  simp only [CollatzResearch.WordTrace]
  refine ⟨58080657147909173066052341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38720438098606115377368227 58080657147909173066052341)
  ·
    refine ⟨5445061607616484974942407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58080657147909173066052341 5445061607616484974942407)
    ·
      refine ⟨8167592411424727462413611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5445061607616484974942407 8167592411424727462413611)
      ·
        refine ⟨12251388617137091193620417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8167592411424727462413611 12251388617137091193620417)
        ·
          refine ⟨9188541462852818395215313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12251388617137091193620417 9188541462852818395215313)
          ·
            refine ⟨6891406097139613796411485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9188541462852818395215313 6891406097139613796411485)
            ·
              refine ⟨2584277286427355173654307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6891406097139613796411485 2584277286427355173654307)
              ·
                refine ⟨3876415929641032760481461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584277286427355173654307 3876415929641032760481461)
                ·
                  refine ⟨363413993403846821295137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3876415929641032760481461 363413993403846821295137)
                  ·
                    rfl

theorem cell21_1592429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1592429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592429 prefixEnd_1592429 := by exact prefixLift 1592429
  have htrace : WordTrace (prefixWord ++ tailWord_1592429) baseStart_1592429 baseEnd_1592429 := by
    simpa [prefixWord, tailWord_1592429, baseEnd_1592429] using wordTrace_append hprefix tailTrace_1592429
  have hstable : (prefixWord ++ tailWord_1592429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592429).length < 2 ^ (prefixWord ++ tailWord_1592429).sum := by decide
  have hdescent : baseEnd_1592429 < baseStart_1592429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592457 : List Nat := [1, 2, 1, 1, 4, 3, 2, 7]
def baseStart_1592457 : Nat := 118140960795 + 1592457 * 2 ^ 59
def prefixEnd_1592457 : Nat := 4983230072969 + 3 ^ 40 * 1592457 * 2
def baseEnd_1592457 : Nat := 121140127795108331609471

theorem tailTrace_1592457 : CollatzResearch.WordTrace tailWord_1592457 prefixEnd_1592457 121140127795108331609471 := by
  unfold tailWord_1592457
  simp only [CollatzResearch.WordTrace]
  refine ⟨58081678391807733848071625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38721118927871822565381083 58081678391807733848071625)
  ·
    refine ⟨43561258793855800386053719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58081678391807733848071625 43561258793855800386053719)
    ·
      refine ⟨65341888190783700579080579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43561258793855800386053719 65341888190783700579080579)
      ·
        refine ⟨98012832286175550868620869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65341888190783700579080579 98012832286175550868620869)
        ·
          refine ⟨18377406053657915787866413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98012832286175550868620869 18377406053657915787866413)
          ·
            refine ⟨6891527270121718420449905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18377406053657915787866413 6891527270121718420449905)
            ·
              refine ⟨5168645452591288815337429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6891527270121718420449905 5168645452591288815337429)
              ·
                refine ⟨121140127795108331609471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5168645452591288815337429 121140127795108331609471)
                ·
                  rfl

theorem cell21_1592457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 7].length) (baseStart_1592457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592457 prefixEnd_1592457 := by exact prefixLift 1592457
  have htrace : WordTrace (prefixWord ++ tailWord_1592457) baseStart_1592457 baseEnd_1592457 := by
    simpa [prefixWord, tailWord_1592457, baseEnd_1592457] using wordTrace_append hprefix tailTrace_1592457
  have hstable : (prefixWord ++ tailWord_1592457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592457).length < 2 ^ (prefixWord ++ tailWord_1592457).sum := by decide
  have hdescent : baseEnd_1592457 < baseStart_1592457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592522 : List Nat := [3, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_1592522 : Nat := 118140960795 + 1592522 * 2 ^ 59
def prefixEnd_1592522 : Nat := 4983230072969 + 3 ^ 40 * 1592522 * 2
def baseEnd_1592522 : Nat := 363435217270899326244947

theorem tailTrace_1592522 : CollatzResearch.WordTrace tailWord_1592522 prefixEnd_1592522 363435217270899326244947 := by
  unfold tailWord_1592522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14521012284143062487296955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38722699424381499966125213 14521012284143062487296955)
  ·
    refine ⟨21781518426214593730945433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14521012284143062487296955 21781518426214593730945433)
    ·
      refine ⟨16336138819660945298209075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21781518426214593730945433 16336138819660945298209075)
      ·
        refine ⟨24504208229491417947313613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16336138819660945298209075 24504208229491417947313613)
        ·
          refine ⟨9189078086059281730242605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24504208229491417947313613 9189078086059281730242605)
          ·
            refine ⟨3445904282272230648840977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9189078086059281730242605 3445904282272230648840977)
            ·
              refine ⟨2584428211704172986630733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3445904282272230648840977 2584428211704172986630733)
              ·
                refine ⟨969160579389064869986525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2584428211704172986630733 969160579389064869986525)
                ·
                  refine ⟨363435217270899326244947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969160579389064869986525 363435217270899326244947)
                  ·
                    rfl

theorem cell21_1592522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_1592522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592522 prefixEnd_1592522 := by exact prefixLift 1592522
  have htrace : WordTrace (prefixWord ++ tailWord_1592522) baseStart_1592522 baseEnd_1592522 := by
    simpa [prefixWord, tailWord_1592522, baseEnd_1592522] using wordTrace_append hprefix tailTrace_1592522
  have hstable : (prefixWord ++ tailWord_1592522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592522).length < 2 ^ (prefixWord ++ tailWord_1592522).sum := by decide
  have hdescent : baseEnd_1592522 < baseStart_1592522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592623 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 7]
def baseStart_1592623 : Nat := 118140960795 + 1592623 * 2 ^ 59
def prefixEnd_1592623 : Nat := 4983230072969 + 3 ^ 40 * 1592623 * 2
def baseEnd_1592623 : Nat := 363458266846945595061407

theorem tailTrace_1592623 : CollatzResearch.WordTrace tailWord_1592623 prefixEnd_1592623 363458266846945595061407 := by
  unfold tailWord_1592623
  simp only [CollatzResearch.WordTrace]
  refine ⟨58087732909206344198614523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38725155272804229465743015 58087732909206344198614523)
  ·
    refine ⟨87131599363809516297921785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58087732909206344198614523 87131599363809516297921785)
    ·
      refine ⟨65348699522857137223441339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87131599363809516297921785 65348699522857137223441339)
      ·
        refine ⟨98023049284285705835162009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65348699522857137223441339 98023049284285705835162009)
        ·
          refine ⟨73517286963214279376371507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98023049284285705835162009 73517286963214279376371507)
          ·
            refine ⟨110275930444821419064557261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73517286963214279376371507 110275930444821419064557261)
            ·
              refine ⟨41353473916808032149208973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110275930444821419064557261 41353473916808032149208973)
              ·
                refine ⟨15507552718803012055953365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41353473916808032149208973 15507552718803012055953365)
                ·
                  refine ⟨363458266846945595061407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15507552718803012055953365 363458266846945595061407)
                  ·
                    rfl

theorem cell21_1592623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_1592623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592623 prefixEnd_1592623 := by exact prefixLift 1592623
  have htrace : WordTrace (prefixWord ++ tailWord_1592623) baseStart_1592623 baseEnd_1592623 := by
    simpa [prefixWord, tailWord_1592623, baseEnd_1592623] using wordTrace_append hprefix tailTrace_1592623
  have hstable : (prefixWord ++ tailWord_1592623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592623).length < 2 ^ (prefixWord ++ tailWord_1592623).sum := by decide
  have hdescent : baseEnd_1592623 < baseStart_1592623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592657 : List Nat := [1, 2, 2, 1, 4, 1, 3, 4, 3]
def baseStart_1592657 : Nat := 118140960795 + 1592657 * 2 ^ 59
def prefixEnd_1592657 : Nat := 4983230072969 + 3 ^ 40 * 1592657 * 2
def baseEnd_1592657 : Nat := 363466026110169091494671

theorem tailTrace_1592657 : CollatzResearch.WordTrace tailWord_1592657 prefixEnd_1592657 363466026110169091494671 := by
  unfold tailWord_1592657
  simp only [CollatzResearch.WordTrace]
  refine ⟨58088972991083168005352225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38725981994055445336901483 58088972991083168005352225)
  ·
    refine ⟨43566729743312376004014169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58088972991083168005352225 43566729743312376004014169)
    ·
      refine ⟨32675047307484282003010627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43566729743312376004014169 32675047307484282003010627)
      ·
        refine ⟨49012570961226423004515941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32675047307484282003010627 49012570961226423004515941)
        ·
          refine ⟨9189857055229954313346739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49012570961226423004515941 9189857055229954313346739)
          ·
            refine ⟨13784785582844931470020109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9189857055229954313346739 13784785582844931470020109)
            ·
              refine ⟨5169294593566849301257541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13784785582844931470020109 5169294593566849301257541)
              ·
                refine ⟨969242736293784243985789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5169294593566849301257541 969242736293784243985789)
                ·
                  refine ⟨363466026110169091494671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969242736293784243985789 363466026110169091494671)
                  ·
                    rfl

theorem cell21_1592657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_1592657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592657 prefixEnd_1592657 := by exact prefixLift 1592657
  have htrace : WordTrace (prefixWord ++ tailWord_1592657) baseStart_1592657 baseEnd_1592657 := by
    simpa [prefixWord, tailWord_1592657, baseEnd_1592657] using wordTrace_append hprefix tailTrace_1592657
  have hstable : (prefixWord ++ tailWord_1592657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592657).length < 2 ^ (prefixWord ++ tailWord_1592657).sum := by decide
  have hdescent : baseEnd_1592657 < baseStart_1592657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592699 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 7]
def baseStart_1592699 : Nat := 118140960795 + 1592699 * 2 ^ 59
def prefixEnd_1592699 : Nat := 4983230072969 + 3 ^ 40 * 1592699 * 2
def baseEnd_1592699 : Nat := 363475611082386351794585

theorem tailTrace_1592699 : CollatzResearch.WordTrace tailWord_1592699 prefixEnd_1592699 363475611082386351794585 := by
  unfold tailWord_1592699
  simp only [CollatzResearch.WordTrace]
  refine ⟨58090504856931009178381151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38727003237954006118920767 58090504856931009178381151)
  ·
    refine ⟨87135757285396513767571727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58090504856931009178381151 87135757285396513767571727)
    ·
      refine ⟨130703635928094770651357591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87135757285396513767571727 130703635928094770651357591)
      ·
        refine ⟨196055453892142155977036387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130703635928094770651357591 196055453892142155977036387)
        ·
          refine ⟨294083180838213233965554581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196055453892142155977036387 294083180838213233965554581)
          ·
            refine ⟨13785149101791245342135371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 294083180838213233965554581 13785149101791245342135371)
            ·
              refine ⟨20677723652686868013203057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13785149101791245342135371 20677723652686868013203057)
              ·
                refine ⟨15508292739515151009902293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20677723652686868013203057 15508292739515151009902293)
                ·
                  refine ⟨363475611082386351794585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15508292739515151009902293 363475611082386351794585)
                  ·
                    rfl

theorem cell21_1592699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_1592699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592699 prefixEnd_1592699 := by exact prefixLift 1592699
  have htrace : WordTrace (prefixWord ++ tailWord_1592699) baseStart_1592699 baseEnd_1592699 := by
    simpa [prefixWord, tailWord_1592699, baseEnd_1592699] using wordTrace_append hprefix tailTrace_1592699
  have hstable : (prefixWord ++ tailWord_1592699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592699).length < 2 ^ (prefixWord ++ tailWord_1592699).sum := by decide
  have hdescent : baseEnd_1592699 < baseStart_1592699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592705 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 4]
def baseStart_1592705 : Nat := 118140960795 + 1592705 * 2 ^ 59
def prefixEnd_1592705 : Nat := 4983230072969 + 3 ^ 40 * 1592705 * 2
def baseEnd_1592705 : Nat := 363476980364131674694573

theorem tailTrace_1592705 : CollatzResearch.WordTrace tailWord_1592705 prefixEnd_1592705 363476980364131674694573 := by
  unfold tailWord_1592705
  simp only [CollatzResearch.WordTrace]
  refine ⟨58090723694909272203099569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38727149129939514802066379 58090723694909272203099569)
  ·
    refine ⟨43568042771181954152324677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58090723694909272203099569 43568042771181954152324677)
    ·
      refine ⟨8169008019596616403560877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43568042771181954152324677 8169008019596616403560877)
      ·
        refine ⟨3063378007348731151335329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8169008019596616403560877 3063378007348731151335329)
        ·
          refine ⟨2297533505511548363501497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3063378007348731151335329 2297533505511548363501497)
          ·
            refine ⟨1723150129133661272626123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297533505511548363501497 1723150129133661272626123)
            ·
              refine ⟨2584725193700491908939185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723150129133661272626123 2584725193700491908939185)
              ·
                refine ⟨1938543895275368931704389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584725193700491908939185 1938543895275368931704389)
                ·
                  refine ⟨363476980364131674694573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1938543895275368931704389 363476980364131674694573)
                  ·
                    rfl

theorem cell21_1592705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_1592705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592705 prefixEnd_1592705 := by exact prefixLift 1592705
  have htrace : WordTrace (prefixWord ++ tailWord_1592705) baseStart_1592705 baseEnd_1592705 := by
    simpa [prefixWord, tailWord_1592705, baseEnd_1592705] using wordTrace_append hprefix tailTrace_1592705
  have hstable : (prefixWord ++ tailWord_1592705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592705).length < 2 ^ (prefixWord ++ tailWord_1592705).sum := by decide
  have hdescent : baseEnd_1592705 < baseStart_1592705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592716 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_1592716 : Nat := 118140960795 + 1592716 * 2 ^ 59
def prefixEnd_1592716 : Nat := 4983230072969 + 3 ^ 40 * 1592716 * 2
def baseEnd_1592716 : Nat := 363479490713998100011217

theorem tailTrace_1592716 : CollatzResearch.WordTrace tailWord_1592716 prefixEnd_1592716 363479490713998100011217 := by
  unfold tailWord_1592716
  simp only [CollatzResearch.WordTrace]
  refine ⟨29045562448934710540875001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38727416598579614054500001 29045562448934710540875001)
  ·
    refine ⟨21784171836701032905656251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29045562448934710540875001 21784171836701032905656251)
    ·
      refine ⟨32676257755051549358484377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21784171836701032905656251 32676257755051549358484377)
      ·
        refine ⟨24507193316288662018863283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32676257755051549358484377 24507193316288662018863283)
        ·
          refine ⟨36760789974432993028294925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24507193316288662018863283 36760789974432993028294925)
          ·
            refine ⟨13785296240412372385610597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36760789974432993028294925 13785296240412372385610597)
            ·
              refine ⟨2584743045077319822301987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13785296240412372385610597 2584743045077319822301987)
              ·
                refine ⟨3877114567615979733452981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584743045077319822301987 3877114567615979733452981)
                ·
                  refine ⟨363479490713998100011217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877114567615979733452981 363479490713998100011217)
                  ·
                    rfl

theorem cell21_1592716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_1592716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592716 prefixEnd_1592716 := by exact prefixLift 1592716
  have htrace : WordTrace (prefixWord ++ tailWord_1592716) baseStart_1592716 baseEnd_1592716 := by
    simpa [prefixWord, tailWord_1592716, baseEnd_1592716] using wordTrace_append hprefix tailTrace_1592716
  have hstable : (prefixWord ++ tailWord_1592716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592716).length < 2 ^ (prefixWord ++ tailWord_1592716).sum := by decide
  have hdescent : baseEnd_1592716 < baseStart_1592716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592722 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_1592722 : Nat := 118140960795 + 1592722 * 2 ^ 59
def prefixEnd_1592722 : Nat := 4983230072969 + 3 ^ 40 * 1592722 * 2
def baseEnd_1592722 : Nat := 363480859995743422911205

theorem tailTrace_1592722 : CollatzResearch.WordTrace tailWord_1592722 prefixEnd_1592722 363480859995743422911205 := by
  unfold tailWord_1592722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14522835933961921026617105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38727562490565122737645613 14522835933961921026617105)
  ·
    refine ⟨10892126950471440769962829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14522835933961921026617105 10892126950471440769962829)
    ·
      refine ⟨4084547606426790288736061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10892126950471440769962829 4084547606426790288736061)
      ·
        refine ⟨1531705352410046358276023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4084547606426790288736061 1531705352410046358276023)
        ·
          refine ⟨2297558028615069537414035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531705352410046358276023 2297558028615069537414035)
          ·
            refine ⟨3446337042922604306121053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2297558028615069537414035 3446337042922604306121053)
            ·
              refine ⟨1292376391095976614795395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3446337042922604306121053 1292376391095976614795395)
              ·
                refine ⟨1938564586643964922193093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292376391095976614795395 1938564586643964922193093)
                ·
                  refine ⟨363480859995743422911205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1938564586643964922193093 363480859995743422911205)
                  ·
                    rfl

theorem cell21_1592722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_1592722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592722 prefixEnd_1592722 := by exact prefixLift 1592722
  have htrace : WordTrace (prefixWord ++ tailWord_1592722) baseStart_1592722 baseEnd_1592722 := by
    simpa [prefixWord, tailWord_1592722, baseEnd_1592722] using wordTrace_append hprefix tailTrace_1592722
  have hstable : (prefixWord ++ tailWord_1592722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592722).length < 2 ^ (prefixWord ++ tailWord_1592722).sum := by decide
  have hdescent : baseEnd_1592722 < baseStart_1592722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592851 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 7]
def baseStart_1592851 : Nat := 118140960795 + 1592851 * 2 ^ 59
def prefixEnd_1592851 : Nat := 4983230072969 + 3 ^ 40 * 1592851 * 2
def baseEnd_1592851 : Nat := 363510299553267865260941

theorem tailTrace_1592851 : CollatzResearch.WordTrace tailWord_1592851 prefixEnd_1592851 363510299553267865260941 := by
  unfold tailWord_1592851
  simp only [CollatzResearch.WordTrace]
  refine ⟨58096048752380339137914407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38730699168253559425276271 58096048752380339137914407)
  ·
    refine ⟨87144073128570508706871611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58096048752380339137914407 87144073128570508706871611)
    ·
      refine ⟨130716109692855763060307417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87144073128570508706871611 130716109692855763060307417)
      ·
        refine ⟨98037082269641822295230563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130716109692855763060307417 98037082269641822295230563)
        ·
          refine ⟨147055623404462733442845845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98037082269641822295230563 147055623404462733442845845)
          ·
            refine ⟨6893232347084190630133399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147055623404462733442845845 6893232347084190630133399)
            ·
              refine ⟨10339848520626285945200099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893232347084190630133399 10339848520626285945200099)
              ·
                refine ⟨15509772780939428917800149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339848520626285945200099 15509772780939428917800149)
                ·
                  refine ⟨363510299553267865260941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15509772780939428917800149 363510299553267865260941)
                  ·
                    rfl

theorem cell21_1592851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_1592851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592851 prefixEnd_1592851 := by exact prefixLift 1592851
  have htrace : WordTrace (prefixWord ++ tailWord_1592851) baseStart_1592851 baseEnd_1592851 := by
    simpa [prefixWord, tailWord_1592851, baseEnd_1592851] using wordTrace_append hprefix tailTrace_1592851
  have hstable : (prefixWord ++ tailWord_1592851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592851).length < 2 ^ (prefixWord ++ tailWord_1592851).sum := by decide
  have hdescent : baseEnd_1592851 < baseStart_1592851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592885 : List Nat := [1, 3, 3, 1, 1, 3, 2, 4, 3]
def baseStart_1592885 : Nat := 118140960795 + 1592885 * 2 ^ 59
def prefixEnd_1592885 : Nat := 4983230072969 + 3 ^ 40 * 1592885 * 2
def baseEnd_1592885 : Nat := 363518058816491361694205

theorem tailTrace_1592885 : CollatzResearch.WordTrace tailWord_1592885 prefixEnd_1592885 363518058816491361694205 := by
  unfold tailWord_1592885
  simp only [CollatzResearch.WordTrace]
  refine ⟨58097288834257162944652109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38731525889504775296434739 58097288834257162944652109)
  ·
    refine ⟨21786483312846436104244541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58097288834257162944652109 21786483312846436104244541)
    ·
      refine ⟨8169931242317413539091703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21786483312846436104244541 8169931242317413539091703)
      ·
        refine ⟨12254896863476120308637555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8169931242317413539091703 12254896863476120308637555)
        ·
          refine ⟨18382345295214180462956333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12254896863476120308637555 18382345295214180462956333)
          ·
            refine ⟨6893379485705317673608625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18382345295214180462956333 6893379485705317673608625)
            ·
              refine ⟨5170034614278988255206469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6893379485705317673608625 5170034614278988255206469)
              ·
                refine ⟨969381490177310297851213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5170034614278988255206469 969381490177310297851213)
                ·
                  refine ⟨363518058816491361694205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969381490177310297851213 363518058816491361694205)
                  ·
                    rfl

theorem cell21_1592885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_1592885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592885 prefixEnd_1592885 := by exact prefixLift 1592885
  have htrace : WordTrace (prefixWord ++ tailWord_1592885) baseStart_1592885 baseEnd_1592885 := by
    simpa [prefixWord, tailWord_1592885, baseEnd_1592885] using wordTrace_append hprefix tailTrace_1592885
  have hstable : (prefixWord ++ tailWord_1592885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592885).length < 2 ^ (prefixWord ++ tailWord_1592885).sum := by decide
  have hdescent : baseEnd_1592885 < baseStart_1592885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592896 : List Nat := [2, 1, 1, 2, 2, 2, 1, 10]
def baseStart_1592896 : Nat := 118140960795 + 1592896 * 2 ^ 59
def prefixEnd_1592896 : Nat := 4983230072969 + 3 ^ 40 * 1592896 * 2
def baseEnd_1592896 : Nat := 121173523055452595670283

theorem tailTrace_1592896 : CollatzResearch.WordTrace tailWord_1592896 prefixEnd_1592896 121173523055452595670283 := by
  unfold tailWord_1592896
  simp only [CollatzResearch.WordTrace]
  refine ⟨29048845018608655911651271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38731793358144874548868361 29048845018608655911651271)
  ·
    refine ⟨43573267527912983867476907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29048845018608655911651271 43573267527912983867476907)
    ·
      refine ⟨65359901291869475801215361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43573267527912983867476907 65359901291869475801215361)
      ·
        refine ⟨49019925968902106850911521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65359901291869475801215361 49019925968902106850911521)
        ·
          refine ⟨36764944476676580138183641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49019925968902106850911521 36764944476676580138183641)
          ·
            refine ⟨27573708357507435103637731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36764944476676580138183641 27573708357507435103637731)
            ·
              refine ⟨41360562536261152655456597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27573708357507435103637731 41360562536261152655456597)
              ·
                refine ⟨121173523055452595670283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41360562536261152655456597 121173523055452595670283)
                ·
                  rfl

theorem cell21_1592896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_1592896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592896 prefixEnd_1592896 := by exact prefixLift 1592896
  have htrace : WordTrace (prefixWord ++ tailWord_1592896) baseStart_1592896 baseEnd_1592896 := by
    simpa [prefixWord, tailWord_1592896, baseEnd_1592896] using wordTrace_append hprefix tailTrace_1592896
  have hstable : (prefixWord ++ tailWord_1592896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592896).length < 2 ^ (prefixWord ++ tailWord_1592896).sum := by decide
  have hdescent : baseEnd_1592896 < baseStart_1592896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592944 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_1592944 : Nat := 118140960795 + 1592944 * 2 ^ 59
def prefixEnd_1592944 : Nat := 4983230072969 + 3 ^ 40 * 1592944 * 2
def baseEnd_1592944 : Nat := 363531523420320370210751

theorem tailTrace_1592944 : CollatzResearch.WordTrace tailWord_1592944 prefixEnd_1592944 363531523420320370210751 := by
  unfold tailWord_1592944
  simp only [CollatzResearch.WordTrace]
  refine ⟨29049720370521708010524943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38732960494028944014033257 29049720370521708010524943)
  ·
    refine ⟨43574580555782562015787415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29049720370521708010524943 43574580555782562015787415)
    ·
      refine ⟨65361870833673843023681123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43574580555782562015787415 65361870833673843023681123)
      ·
        refine ⟨98042806250510764535521685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65361870833673843023681123 98042806250510764535521685)
        ·
          refine ⟨4595756542992692087602579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98042806250510764535521685 4595756542992692087602579)
          ·
            refine ⟨6893634814489038131403869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595756542992692087602579 6893634814489038131403869)
            ·
              refine ⟨2585113055433389299276451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6893634814489038131403869 2585113055433389299276451)
              ·
                refine ⟨3877669583150083948914677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585113055433389299276451 3877669583150083948914677)
                ·
                  refine ⟨363531523420320370210751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877669583150083948914677 363531523420320370210751)
                  ·
                    rfl

theorem cell21_1592944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_1592944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592944 prefixEnd_1592944 := by exact prefixLift 1592944
  have htrace : WordTrace (prefixWord ++ tailWord_1592944) baseStart_1592944 baseEnd_1592944 := by
    simpa [prefixWord, tailWord_1592944, baseEnd_1592944] using wordTrace_append hprefix tailTrace_1592944
  have hstable : (prefixWord ++ tailWord_1592944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592944).length < 2 ^ (prefixWord ++ tailWord_1592944).sum := by decide
  have hdescent : baseEnd_1592944 < baseStart_1592944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592972 : List Nat := [2, 2, 1, 2, 1, 1, 3, 9]
def baseStart_1592972 : Nat := 118140960795 + 1592972 * 2 ^ 59
def prefixEnd_1592972 : Nat := 4983230072969 + 3 ^ 40 * 1592972 * 2
def baseEnd_1592972 : Nat := 121179304467266181248009

theorem tailTrace_1592972 : CollatzResearch.WordTrace tailWord_1592972 prefixEnd_1592972 121179304467266181248009 := by
  unfold tailWord_1592972
  simp only [CollatzResearch.WordTrace]
  refine ⟨29050230992470988401534585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38733641323294651202046113 29050230992470988401534585)
  ·
    refine ⟨21787673244353241301150939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29050230992470988401534585 21787673244353241301150939)
    ·
      refine ⟨32681509866529861951726409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21787673244353241301150939 32681509866529861951726409)
      ·
        refine ⟨24511132399897396463794807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32681509866529861951726409 24511132399897396463794807)
        ·
          refine ⟨36766698599846094695692211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24511132399897396463794807 36766698599846094695692211)
          ·
            refine ⟨55150047899769142043538317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36766698599846094695692211 55150047899769142043538317)
            ·
              refine ⟨20681267962413428266326869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55150047899769142043538317 20681267962413428266326869)
              ·
                refine ⟨121179304467266181248009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20681267962413428266326869 121179304467266181248009)
                ·
                  rfl

theorem cell21_1592972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_1592972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1592972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1592972 prefixEnd_1592972 := by exact prefixLift 1592972
  have htrace : WordTrace (prefixWord ++ tailWord_1592972) baseStart_1592972 baseEnd_1592972 := by
    simpa [prefixWord, tailWord_1592972, baseEnd_1592972] using wordTrace_append hprefix tailTrace_1592972
  have hstable : (prefixWord ++ tailWord_1592972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592972).length < 2 ^ (prefixWord ++ tailWord_1592972).sum := by decide
  have hdescent : baseEnd_1592972 < baseStart_1592972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593020 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_1593020 : Nat := 118140960795 + 1593020 * 2 ^ 59
def prefixEnd_1593020 : Nat := 4983230072969 + 3 ^ 40 * 1593020 * 2
def baseEnd_1593020 : Nat := 363548867655761126943929

theorem tailTrace_1593020 : CollatzResearch.WordTrace tailWord_1593020 prefixEnd_1593020 363548867655761126943929 := by
  unfold tailWord_1593020
  simp only [CollatzResearch.WordTrace]
  refine ⟨29051106344384040500408257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38734808459178720667211009 29051106344384040500408257)
  ·
    refine ⟨21788329758288030375306193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29051106344384040500408257 21788329758288030375306193)
    ·
      refine ⟨16341247318716022781479645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21788329758288030375306193 16341247318716022781479645)
      ·
        refine ⟨6127967744518508543054867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16341247318716022781479645 6127967744518508543054867)
        ·
          refine ⟨9191951616777762814582301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127967744518508543054867 9191951616777762814582301)
          ·
            refine ⟨3446981856291661055468363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9191951616777762814582301 3446981856291661055468363)
            ·
              refine ⟨5170472784437491583202545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446981856291661055468363 5170472784437491583202545)
              ·
                refine ⟨3877854588328118687401909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5170472784437491583202545 3877854588328118687401909)
                ·
                  refine ⟨363548867655761126943929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877854588328118687401909 363548867655761126943929)
                  ·
                    rfl

theorem cell21_1593020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_1593020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593020 prefixEnd_1593020 := by exact prefixLift 1593020
  have htrace : WordTrace (prefixWord ++ tailWord_1593020) baseStart_1593020 baseEnd_1593020 := by
    simpa [prefixWord, tailWord_1593020, baseEnd_1593020] using wordTrace_append hprefix tailTrace_1593020
  have hstable : (prefixWord ++ tailWord_1593020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593020).length < 2 ^ (prefixWord ++ tailWord_1593020).sum := by decide
  have hdescent : baseEnd_1593020 < baseStart_1593020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593048 : List Nat := [2, 1, 2, 2, 3, 1, 10]
def baseStart_1593048 : Nat := 118140960795 + 1593048 * 2 ^ 59
def prefixEnd_1593048 : Nat := 4983230072969 + 3 ^ 40 * 1593048 * 2
def baseEnd_1593048 : Nat := 40395028626359922275245

theorem tailTrace_1593048 : CollatzResearch.WordTrace tailWord_1593048 prefixEnd_1593048 40395028626359922275245 := by
  unfold tailWord_1593048
  simp only [CollatzResearch.WordTrace]
  refine ⟨29051616966333320891417899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38735489288444427855223865 29051616966333320891417899)
  ·
    refine ⟨43577425449499981337126849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29051616966333320891417899 43577425449499981337126849)
    ·
      refine ⟨32683069087124986002845137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43577425449499981337126849 32683069087124986002845137)
      ·
        refine ⟨24512301815343739502133853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32683069087124986002845137 24512301815343739502133853)
        ·
          refine ⟨9192113180753902313300195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24512301815343739502133853 9192113180753902313300195)
          ·
            refine ⟨13788169771130853469950293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9192113180753902313300195 13788169771130853469950293)
            ·
              refine ⟨40395028626359922275245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13788169771130853469950293 40395028626359922275245)
              ·
                rfl

theorem cell21_1593048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 10].length) (baseStart_1593048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593048 prefixEnd_1593048 := by exact prefixLift 1593048
  have htrace : WordTrace (prefixWord ++ tailWord_1593048) baseStart_1593048 baseEnd_1593048 := by
    simpa [prefixWord, tailWord_1593048, baseEnd_1593048] using wordTrace_append hprefix tailTrace_1593048
  have hstable : (prefixWord ++ tailWord_1593048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593048).length < 2 ^ (prefixWord ++ tailWord_1593048).sum := by decide
  have hdescent : baseEnd_1593048 < baseStart_1593048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593079 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 5]
def baseStart_1593079 : Nat := 118140960795 + 1593079 * 2 ^ 59
def prefixEnd_1593079 : Nat := 4983230072969 + 3 ^ 40 * 1593079 * 2
def baseEnd_1593079 : Nat := 363562332259590135460475

theorem tailTrace_1593079 : CollatzResearch.WordTrace tailWord_1593079 prefixEnd_1593079 363562332259590135460475 := by
  unfold tailWord_1593079
  simp only [CollatzResearch.WordTrace]
  refine ⟨58104364595554334077214291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38736243063702889384809527 58104364595554334077214291)
  ·
    refine ⟨87156546893331501115821437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58104364595554334077214291 87156546893331501115821437)
    ·
      refine ⟨32683705084999312918433039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87156546893331501115821437 32683705084999312918433039)
      ·
        refine ⟨49025557627498969377649559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32683705084999312918433039 49025557627498969377649559)
        ·
          refine ⟨73538336441248454066474339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49025557627498969377649559 73538336441248454066474339)
          ·
            refine ⟨110307504661872681099711509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73538336441248454066474339 110307504661872681099711509)
            ·
              refine ⟨5170664281025281926548977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110307504661872681099711509 5170664281025281926548977)
              ·
                refine ⟨3877998210768961444911733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5170664281025281926548977 3877998210768961444911733)
                ·
                  refine ⟨363562332259590135460475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877998210768961444911733 363562332259590135460475)
                  ·
                    rfl

theorem cell21_1593079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_1593079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593079 prefixEnd_1593079 := by exact prefixLift 1593079
  have htrace : WordTrace (prefixWord ++ tailWord_1593079) baseStart_1593079 baseEnd_1593079 := by
    simpa [prefixWord, tailWord_1593079, baseEnd_1593079] using wordTrace_append hprefix tailTrace_1593079
  have hstable : (prefixWord ++ tailWord_1593079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593079).length < 2 ^ (prefixWord ++ tailWord_1593079).sum := by decide
  have hdescent : baseEnd_1593079 < baseStart_1593079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593158 : List Nat := [6, 1, 1, 2, 1, 10]
def baseStart_1593158 : Nat := 118140960795 + 1593158 * 2 ^ 59
def prefixEnd_1593158 : Nat := 4983230072969 + 3 ^ 40 * 1593158 * 2
def baseEnd_1593158 : Nat := 13465939301329761246061

theorem tailTrace_1593158 : CollatzResearch.WordTrace tailWord_1593158 prefixEnd_1593158 13465939301329761246061 := by
  unfold tailWord_1593158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815851436320879080291879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38738163974845420379560085 1815851436320879080291879)
  ·
    refine ⟨2723777154481318620437819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1815851436320879080291879 2723777154481318620437819)
    ·
      refine ⟨4085665731721977930656729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723777154481318620437819 4085665731721977930656729)
      ·
        refine ⟨3064249298791483447992547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4085665731721977930656729 3064249298791483447992547)
        ·
          refine ⟨4596373948187225171988821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064249298791483447992547 4596373948187225171988821)
          ·
            refine ⟨13465939301329761246061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4596373948187225171988821 13465939301329761246061)
            ·
              rfl

theorem cell21_1593158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 10].length) (baseStart_1593158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593158 prefixEnd_1593158 := by exact prefixLift 1593158
  have htrace : WordTrace (prefixWord ++ tailWord_1593158) baseStart_1593158 baseEnd_1593158 := by
    simpa [prefixWord, tailWord_1593158, baseEnd_1593158] using wordTrace_append hprefix tailTrace_1593158
  have hstable : (prefixWord ++ tailWord_1593158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593158).length < 2 ^ (prefixWord ++ tailWord_1593158).sum := by decide
  have hdescent : baseEnd_1593158 < baseStart_1593158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593265 : List Nat := [1, 2, 2, 4, 2, 1, 3, 3, 3]
def baseStart_1593265 : Nat := 118140960795 + 1593265 * 2 ^ 59
def prefixEnd_1593265 : Nat := 4983230072969 + 3 ^ 40 * 1593265 * 2
def baseEnd_1593265 : Nat := 363604779993695145360095

theorem tailTrace_1593265 : CollatzResearch.WordTrace tailWord_1593265 prefixEnd_1593265 363604779993695145360095 := by
  unfold tailWord_1593265
  simp only [CollatzResearch.WordTrace]
  refine ⟨58111148572880487843485249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38740765715253658562323499 58111148572880487843485249)
  ·
    refine ⟨43583361429660365882613937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58111148572880487843485249 43583361429660365882613937)
    ·
      refine ⟨32687521072245274411960453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43583361429660365882613937 32687521072245274411960453)
      ·
        refine ⟨6128910201045988952242585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32687521072245274411960453 6128910201045988952242585)
        ·
          refine ⟨4596682650784491714181939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6128910201045988952242585 4596682650784491714181939)
          ·
            refine ⟨6895023976176737571272909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596682650784491714181939 6895023976176737571272909)
            ·
              refine ⟨2585633991066276589227341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6895023976176737571272909 2585633991066276589227341)
              ·
                refine ⟨969612746649853720960253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2585633991066276589227341 969612746649853720960253)
                ·
                  refine ⟨363604779993695145360095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969612746649853720960253 363604779993695145360095)
                  ·
                    rfl

theorem cell21_1593265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_1593265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593265 prefixEnd_1593265 := by exact prefixLift 1593265
  have htrace : WordTrace (prefixWord ++ tailWord_1593265) baseStart_1593265 baseEnd_1593265 := by
    simpa [prefixWord, tailWord_1593265, baseEnd_1593265] using wordTrace_append hprefix tailTrace_1593265
  have hstable : (prefixWord ++ tailWord_1593265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593265).length < 2 ^ (prefixWord ++ tailWord_1593265).sum := by decide
  have hdescent : baseEnd_1593265 < baseStart_1593265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593341 : List Nat := [1, 4, 1, 1, 1, 2, 6, 2, 3]
def baseStart_1593341 : Nat := 118140960795 + 1593341 * 2 ^ 59
def prefixEnd_1593341 : Nat := 4983230072969 + 3 ^ 40 * 1593341 * 2
def baseEnd_1593341 : Nat := 363622124229135902093273

theorem tailTrace_1593341 : CollatzResearch.WordTrace tailWord_1593341 prefixEnd_1593341 363622124229135902093273 := by
  unfold tailWord_1593341
  simp only [CollatzResearch.WordTrace]
  refine ⟨58113920520605152823251877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38742613680403435215501251 58113920520605152823251877)
  ·
    refine ⟨10896360097613466154359727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58113920520605152823251877 10896360097613466154359727)
    ·
      refine ⟨16344540146420199231539591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10896360097613466154359727 16344540146420199231539591)
      ·
        refine ⟨24516810219630298847309387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16344540146420199231539591 24516810219630298847309387)
        ·
          refine ⟨36775215329445448270964081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24516810219630298847309387 36775215329445448270964081)
          ·
            refine ⟨27581411497084086203223061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36775215329445448270964081 27581411497084086203223061)
            ·
              refine ⟨1292878663925816540776081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27581411497084086203223061 1292878663925816540776081)
              ·
                refine ⟨969658997944362405582061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292878663925816540776081 969658997944362405582061)
                ·
                  refine ⟨363622124229135902093273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969658997944362405582061 363622124229135902093273)
                  ·
                    rfl

theorem cell21_1593341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_1593341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593341 prefixEnd_1593341 := by exact prefixLift 1593341
  have htrace : WordTrace (prefixWord ++ tailWord_1593341) baseStart_1593341 baseEnd_1593341 := by
    simpa [prefixWord, tailWord_1593341, baseEnd_1593341] using wordTrace_append hprefix tailTrace_1593341
  have hstable : (prefixWord ++ tailWord_1593341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593341).length < 2 ^ (prefixWord ++ tailWord_1593341).sum := by decide
  have hdescent : baseEnd_1593341 < baseStart_1593341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593400 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_1593400 : Nat := 118140960795 + 1593400 * 2 ^ 59
def prefixEnd_1593400 : Nat := 4983230072969 + 3 ^ 40 * 1593400 * 2
def baseEnd_1593400 : Nat := 363635588832964910609819

theorem tailTrace_1593400 : CollatzResearch.WordTrace tailWord_1593400 prefixEnd_1593400 363635588832964910609819 := by
  unfold tailWord_1593400
  simp only [CollatzResearch.WordTrace]
  refine ⟨29058036213695702949824827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38744048284927603933099769 29058036213695702949824827)
  ·
    refine ⟨43587054320543554424737241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29058036213695702949824827 43587054320543554424737241)
    ·
      refine ⟨32690290740407665818552931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43587054320543554424737241 32690290740407665818552931)
      ·
        refine ⟨49035436110611498727829397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32690290740407665818552931 49035436110611498727829397)
        ·
          refine ⟨2298536067684914002867003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49035436110611498727829397 2298536067684914002867003)
          ·
            refine ⟨3447804101527371004300505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298536067684914002867003 3447804101527371004300505)
            ·
              refine ⟨2585853076145528253225379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3447804101527371004300505 2585853076145528253225379)
              ·
                refine ⟨3878779614218292379838069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585853076145528253225379 3878779614218292379838069)
                ·
                  refine ⟨363635588832964910609819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3878779614218292379838069 363635588832964910609819)
                  ·
                    rfl

theorem cell21_1593400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_1593400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593400 prefixEnd_1593400 := by exact prefixLift 1593400
  have htrace : WordTrace (prefixWord ++ tailWord_1593400) baseStart_1593400 baseEnd_1593400 := by
    simpa [prefixWord, tailWord_1593400, baseEnd_1593400] using wordTrace_append hprefix tailTrace_1593400
  have hstable : (prefixWord ++ tailWord_1593400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593400).length < 2 ^ (prefixWord ++ tailWord_1593400).sum := by decide
  have hdescent : baseEnd_1593400 < baseStart_1593400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593583 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 4]
def baseStart_1593583 : Nat := 118140960795 + 1593583 * 2 ^ 59
def prefixEnd_1593583 : Nat := 4983230072969 + 3 ^ 40 * 1593583 * 2
def baseEnd_1593583 : Nat := 363677351926197259059445

theorem tailTrace_1593583 : CollatzResearch.WordTrace tailWord_1593583 prefixEnd_1593583 363677351926197259059445 := by
  unfold tailWord_1593583
  simp only [CollatzResearch.WordTrace]
  refine ⟨58122746985728428153561403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38748497990485618769040935 58122746985728428153561403)
  ·
    refine ⟨87184120478592642230342105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58122746985728428153561403 87184120478592642230342105)
    ·
      refine ⟨65388090358944481672756579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87184120478592642230342105 65388090358944481672756579)
      ·
        refine ⟨98082135538416722509134869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65388090358944481672756579 98082135538416722509134869)
        ·
          refine ⟨4597600103363283867615697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98082135538416722509134869 4597600103363283867615697)
          ·
            refine ⟨3448200077522462900711773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597600103363283867615697 3448200077522462900711773)
            ·
              refine ⟨1293075029070923587766915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3448200077522462900711773 1293075029070923587766915)
              ·
                refine ⟨1939612543606385381650373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293075029070923587766915 1939612543606385381650373)
                ·
                  refine ⟨363677351926197259059445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939612543606385381650373 363677351926197259059445)
                  ·
                    rfl

theorem cell21_1593583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 4].length) (baseStart_1593583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593583 prefixEnd_1593583 := by exact prefixLift 1593583
  have htrace : WordTrace (prefixWord ++ tailWord_1593583) baseStart_1593583 baseEnd_1593583 := by
    simpa [prefixWord, tailWord_1593583, baseEnd_1593583] using wordTrace_append hprefix tailTrace_1593583
  have hstable : (prefixWord ++ tailWord_1593583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593583).length < 2 ^ (prefixWord ++ tailWord_1593583).sum := by decide
  have hdescent : baseEnd_1593583 < baseStart_1593583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593777 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 6]
def baseStart_1593777 : Nat := 118140960795 + 1593777 * 2 ^ 59
def prefixEnd_1593777 : Nat := 4983230072969 + 3 ^ 40 * 1593777 * 2
def baseEnd_1593777 : Nat := 363721625369296032825715

theorem tailTrace_1593777 : CollatzResearch.WordTrace tailWord_1593777 prefixEnd_1593777 363721625369296032825715 := by
  unfold tailWord_1593777
  simp only [CollatzResearch.WordTrace]
  refine ⟨58129822747025599286123585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38753215164683732857415723 58129822747025599286123585)
  ·
    refine ⟨43597367060269199464592689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58129822747025599286123585 43597367060269199464592689)
    ·
      refine ⟨32698025295201899598444517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43597367060269199464592689 32698025295201899598444517)
      ·
        refine ⟨6130879742850356174708347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32698025295201899598444517 6130879742850356174708347)
        ·
          refine ⟨9196319614275534262062521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130879742850356174708347 9196319614275534262062521)
          ·
            refine ⟨6897239710706650696546891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9196319614275534262062521 6897239710706650696546891)
            ·
              refine ⟨10345859566059976044820337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6897239710706650696546891 10345859566059976044820337)
              ·
                refine ⟨7759394674544982033615253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10345859566059976044820337 7759394674544982033615253)
                ·
                  refine ⟨363721625369296032825715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7759394674544982033615253 363721625369296032825715)
                  ·
                    rfl

theorem cell21_1593777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_1593777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593777 prefixEnd_1593777 := by exact prefixLift 1593777
  have htrace : WordTrace (prefixWord ++ tailWord_1593777) baseStart_1593777 baseEnd_1593777 := by
    simpa [prefixWord, tailWord_1593777, baseEnd_1593777] using wordTrace_append hprefix tailTrace_1593777
  have hstable : (prefixWord ++ tailWord_1593777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593777).length < 2 ^ (prefixWord ++ tailWord_1593777).sum := by decide
  have hdescent : baseEnd_1593777 < baseStart_1593777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593839 : List Nat := [1, 1, 2, 1, 4, 1, 1, 7, 3]
def baseStart_1593839 : Nat := 118140960795 + 1593839 * 2 ^ 59
def prefixEnd_1593839 : Nat := 4983230072969 + 3 ^ 40 * 1593839 * 2
def baseEnd_1593839 : Nat := 363735774613997702792255

theorem tailTrace_1593839 : CollatzResearch.WordTrace tailWord_1593839 prefixEnd_1593839 363735774613997702792255 := by
  unfold tailWord_1593839
  simp only [CollatzResearch.WordTrace]
  refine ⟨58132084072800983874880571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38754722715200655916587047 58132084072800983874880571)
  ·
    refine ⟨87198126109201475812320857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58132084072800983874880571 87198126109201475812320857)
    ·
      refine ⟨65398594581901106859240643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87198126109201475812320857 65398594581901106859240643)
      ·
        refine ⟨98097891872851660288860965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65398594581901106859240643 98097891872851660288860965)
        ·
          refine ⟨18393354726159686304161431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98097891872851660288860965 18393354726159686304161431)
          ·
            refine ⟨27590032089239529456242147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18393354726159686304161431 27590032089239529456242147)
            ·
              refine ⟨41385048133859294184363221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27590032089239529456242147 41385048133859294184363221)
              ·
                refine ⟨969962065637327207446013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41385048133859294184363221 969962065637327207446013)
                ·
                  refine ⟨363735774613997702792255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969962065637327207446013 363735774613997702792255)
                  ·
                    rfl

theorem cell21_1593839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 3].length) (baseStart_1593839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593839 prefixEnd_1593839 := by exact prefixLift 1593839
  have htrace : WordTrace (prefixWord ++ tailWord_1593839) baseStart_1593839 baseEnd_1593839 := by
    simpa [prefixWord, tailWord_1593839, baseEnd_1593839] using wordTrace_append hprefix tailTrace_1593839
  have hstable : (prefixWord ++ tailWord_1593839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593839).length < 2 ^ (prefixWord ++ tailWord_1593839).sum := by decide
  have hdescent : baseEnd_1593839 < baseStart_1593839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593870 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_1593870 : Nat := 118140960795 + 1593870 * 2 ^ 59
def prefixEnd_1593870 : Nat := 4983230072969 + 3 ^ 40 * 1593870 * 2
def baseEnd_1593870 : Nat := 363742849236348537775525

theorem tailTrace_1593870 : CollatzResearch.WordTrace tailWord_1593870 prefixEnd_1593870 363742849236348537775525 := by
  unfold tailWord_1593870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7266651841961084521157383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38755476490459117446172709 7266651841961084521157383)
  ·
    refine ⟨10899977762941626781736075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7266651841961084521157383 10899977762941626781736075)
    ·
      refine ⟨16349966644412440172604113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10899977762941626781736075 16349966644412440172604113)
      ·
        refine ⟨12262474983309330129453085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16349966644412440172604113 12262474983309330129453085)
        ·
          refine ⟨4598428118740998798544907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12262474983309330129453085 4598428118740998798544907)
          ·
            refine ⟨6897642178111498197817361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598428118740998798544907 6897642178111498197817361)
            ·
              refine ⟨5173231633583623648363021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6897642178111498197817361 5173231633583623648363021)
              ·
                refine ⟨1939961862593858868136133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5173231633583623648363021 1939961862593858868136133)
                ·
                  refine ⟨363742849236348537775525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939961862593858868136133 363742849236348537775525)
                  ·
                    rfl

theorem cell21_1593870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_1593870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593870 prefixEnd_1593870 := by exact prefixLift 1593870
  have htrace : WordTrace (prefixWord ++ tailWord_1593870) baseStart_1593870 baseEnd_1593870 := by
    simpa [prefixWord, tailWord_1593870, baseEnd_1593870] using wordTrace_append hprefix tailTrace_1593870
  have hstable : (prefixWord ++ tailWord_1593870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593870).length < 2 ^ (prefixWord ++ tailWord_1593870).sum := by decide
  have hdescent : baseEnd_1593870 < baseStart_1593870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593943 : List Nat := [1, 1, 3, 2, 2, 2, 3, 7]
def baseStart_1593943 : Nat := 118140960795 + 1593943 * 2 ^ 59
def prefixEnd_1593943 : Nat := 4983230072969 + 3 ^ 40 * 1593943 * 2
def baseEnd_1593943 : Nat := 121253169610305544352903

theorem tailTrace_1593943 : CollatzResearch.WordTrace tailWord_1593943 prefixEnd_1593943 121253169610305544352903 := by
  unfold tailWord_1593943
  simp only [CollatzResearch.WordTrace]
  refine ⟨58135877264424209636666483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38757251509616139757777655 58135877264424209636666483)
  ·
    refine ⟨87203815896636314454999725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58135877264424209636666483 87203815896636314454999725)
    ·
      refine ⟨32701430961238617920624897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87203815896636314454999725 32701430961238617920624897)
      ·
        refine ⟨24526073220928963440468673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32701430961238617920624897 24526073220928963440468673)
        ·
          refine ⟨18394554915696722580351505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24526073220928963440468673 18394554915696722580351505)
          ·
            refine ⟨13795916186772541935263629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18394554915696722580351505 13795916186772541935263629)
            ·
              refine ⟨5173468570039703225723861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13795916186772541935263629 5173468570039703225723861)
              ·
                refine ⟨121253169610305544352903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5173468570039703225723861 121253169610305544352903)
                ·
                  rfl

theorem cell21_1593943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 7].length) (baseStart_1593943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1593943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1593943 prefixEnd_1593943 := by exact prefixLift 1593943
  have htrace : WordTrace (prefixWord ++ tailWord_1593943) baseStart_1593943 baseEnd_1593943 := by
    simpa [prefixWord, tailWord_1593943, baseEnd_1593943] using wordTrace_append hprefix tailTrace_1593943
  have hstable : (prefixWord ++ tailWord_1593943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593943).length < 2 ^ (prefixWord ++ tailWord_1593943).sum := by decide
  have hdescent : baseEnd_1593943 < baseStart_1593943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594081 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 6]
def baseStart_1594081 : Nat := 118140960795 + 1594081 * 2 ^ 59
def prefixEnd_1594081 : Nat := 4983230072969 + 3 ^ 40 * 1594081 * 2
def baseEnd_1594081 : Nat := 363791002311059059758427

theorem tailTrace_1594081 : CollatzResearch.WordTrace tailWord_1594081 prefixEnd_1594081 363791002311059059758427 := by
  unfold tailWord_1594081
  simp only [CollatzResearch.WordTrace]
  refine ⟨58140910537924259205190097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38760607025282839470126731 58140910537924259205190097)
  ·
    refine ⟨43605682903443194403892573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58140910537924259205190097 43605682903443194403892573)
    ·
      refine ⟨16352131088791197901459715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43605682903443194403892573 16352131088791197901459715)
      ·
        refine ⟨24528196633186796852189573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16352131088791197901459715 24528196633186796852189573)
        ·
          refine ⟨4599036868722524409785545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24528196633186796852189573 4599036868722524409785545)
          ·
            refine ⟨3449277651541893307339159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4599036868722524409785545 3449277651541893307339159)
            ·
              refine ⟨5173916477312839961008739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449277651541893307339159 5173916477312839961008739)
              ·
                refine ⟨7760874715969259941513109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173916477312839961008739 7760874715969259941513109)
                ·
                  refine ⟨363791002311059059758427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7760874715969259941513109 363791002311059059758427)
                  ·
                    rfl

theorem cell21_1594081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_1594081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594081 prefixEnd_1594081 := by exact prefixLift 1594081
  have htrace : WordTrace (prefixWord ++ tailWord_1594081) baseStart_1594081 baseEnd_1594081 := by
    simpa [prefixWord, tailWord_1594081, baseEnd_1594081] using wordTrace_append hprefix tailTrace_1594081
  have hstable : (prefixWord ++ tailWord_1594081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594081).length < 2 ^ (prefixWord ++ tailWord_1594081).sum := by decide
  have hdescent : baseEnd_1594081 < baseStart_1594081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594143 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 5]
def baseStart_1594143 : Nat := 118140960795 + 1594143 * 2 ^ 59
def prefixEnd_1594143 : Nat := 4983230072969 + 3 ^ 40 * 1594143 * 2
def baseEnd_1594143 : Nat := 363805151555760729724967

theorem tailTrace_1594143 : CollatzResearch.WordTrace tailWord_1594143 prefixEnd_1594143 363805151555760729724967 := by
  unfold tailWord_1594143
  simp only [CollatzResearch.WordTrace]
  refine ⟨58143171863699643793947083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38762114575799762529298055 58143171863699643793947083)
  ·
    refine ⟨87214757795549465690920625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58143171863699643793947083 87214757795549465690920625)
    ·
      refine ⟨65411068346662099268190469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87214757795549465690920625 65411068346662099268190469)
      ·
        refine ⟨12264575314999143612785713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65411068346662099268190469 12264575314999143612785713)
        ·
          refine ⟨9198431486249357709589285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12264575314999143612785713 9198431486249357709589285)
          ·
            refine ⟨1724705903671754570547991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9198431486249357709589285 1724705903671754570547991)
            ·
              refine ⟨2587058855507631855821987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724705903671754570547991 2587058855507631855821987)
              ·
                refine ⟨3880588283261447783732981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587058855507631855821987 3880588283261447783732981)
                ·
                  refine ⟨363805151555760729724967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3880588283261447783732981 363805151555760729724967)
                  ·
                    rfl

theorem cell21_1594143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 5].length) (baseStart_1594143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594143 prefixEnd_1594143 := by exact prefixLift 1594143
  have htrace : WordTrace (prefixWord ++ tailWord_1594143) baseStart_1594143 baseEnd_1594143 := by
    simpa [prefixWord, tailWord_1594143, baseEnd_1594143] using wordTrace_append hprefix tailTrace_1594143
  have hstable : (prefixWord ++ tailWord_1594143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594143).length < 2 ^ (prefixWord ++ tailWord_1594143).sum := by decide
  have hdescent : baseEnd_1594143 < baseStart_1594143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594247 : List Nat := [1, 1, 4, 2, 3, 2, 8]
def baseStart_1594247 : Nat := 118140960795 + 1594247 * 2 ^ 59
def prefixEnd_1594247 : Nat := 4983230072969 + 3 ^ 40 * 1594247 * 2
def baseEnd_1594247 : Nat := 40425431752519962221269

theorem tailTrace_1594247 : CollatzResearch.WordTrace tailWord_1594247 prefixEnd_1594247 40425431752519962221269 := by
  unfold tailWord_1594247
  simp only [CollatzResearch.WordTrace]
  refine ⟨58146965055322869555732995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38764643370215246370488663 58146965055322869555732995)
  ·
    refine ⟨87220447582984304333599493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58146965055322869555732995 87220447582984304333599493)
    ·
      refine ⟨16353833921809557062549905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87220447582984304333599493 16353833921809557062549905)
      ·
        refine ⟨12265375441357167796912429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16353833921809557062549905 12265375441357167796912429)
        ·
          refine ⟨4599515790508937923842161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12265375441357167796912429 4599515790508937923842161)
          ·
            refine ⟨3449636842881703442881621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4599515790508937923842161 3449636842881703442881621)
            ·
              refine ⟨40425431752519962221269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3449636842881703442881621 40425431752519962221269)
              ·
                rfl

theorem cell21_1594247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 8].length) (baseStart_1594247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594247 prefixEnd_1594247 := by exact prefixLift 1594247
  have htrace : WordTrace (prefixWord ++ tailWord_1594247) baseStart_1594247 baseEnd_1594247 := by
    simpa [prefixWord, tailWord_1594247, baseEnd_1594247] using wordTrace_append hprefix tailTrace_1594247
  have hstable : (prefixWord ++ tailWord_1594247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594247).length < 2 ^ (prefixWord ++ tailWord_1594247).sum := by decide
  have hdescent : baseEnd_1594247 < baseStart_1594247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594250 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_1594250 : Nat := 118140960795 + 1594250 * 2 ^ 59
def prefixEnd_1594250 : Nat := 4983230072969 + 3 ^ 40 * 1594250 * 2
def baseEnd_1594250 : Nat := 363829570413552321441415

theorem tailTrace_1594250 : CollatzResearch.WordTrace tailWord_1594250 prefixEnd_1594250 363829570413552321441415 := by
  unfold tailWord_1594250
  simp only [CollatzResearch.WordTrace]
  refine ⟨14536768618578000267023051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38764716316208000712061469 14536768618578000267023051)
  ·
    refine ⟨21805152927867000400534577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14536768618578000267023051 21805152927867000400534577)
    ·
      refine ⟨16353864695900250300400933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21805152927867000400534577 16353864695900250300400933)
      ·
        refine ⟨3066349630481296931325175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16353864695900250300400933 3066349630481296931325175)
        ·
          refine ⟨4599524445721945396987763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066349630481296931325175 4599524445721945396987763)
          ·
            refine ⟨6899286668582918095481645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599524445721945396987763 6899286668582918095481645)
            ·
              refine ⟨2587232500718594285805617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6899286668582918095481645 2587232500718594285805617)
              ·
                refine ⟨1940424375538945714354213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2587232500718594285805617 1940424375538945714354213)
                ·
                  refine ⟨363829570413552321441415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1940424375538945714354213 363829570413552321441415)
                  ·
                    rfl

theorem cell21_1594250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_1594250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594250 prefixEnd_1594250 := by exact prefixLift 1594250
  have htrace : WordTrace (prefixWord ++ tailWord_1594250) baseStart_1594250 baseEnd_1594250 := by
    simpa [prefixWord, tailWord_1594250, baseEnd_1594250] using wordTrace_append hprefix tailTrace_1594250
  have hstable : (prefixWord ++ tailWord_1594250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594250).length < 2 ^ (prefixWord ++ tailWord_1594250).sum := by decide
  have hdescent : baseEnd_1594250 < baseStart_1594250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594295 : List Nat := [1, 1, 3, 1, 3, 1, 5, 3, 3]
def baseStart_1594295 : Nat := 118140960795 + 1594295 * 2 ^ 59
def prefixEnd_1594295 : Nat := 4983230072969 + 3 ^ 40 * 1594295 * 2
def baseEnd_1594295 : Nat := 363839840026642243191323

theorem tailTrace_1594295 : CollatzResearch.WordTrace tailWord_1594295 prefixEnd_1594295 363839840026642243191323 := by
  unfold tailWord_1594295
  simp only [CollatzResearch.WordTrace]
  refine ⟨58148715759148973753480339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38765810506099315835653559 58148715759148973753480339)
  ·
    refine ⟨87223073638723460630220509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58148715759148973753480339 87223073638723460630220509)
    ·
      refine ⟨32708652614521297736332691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87223073638723460630220509 32708652614521297736332691)
      ·
        refine ⟨49062978921781946604499037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32708652614521297736332691 49062978921781946604499037)
        ·
          refine ⟨18398617095668229976687139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49062978921781946604499037 18398617095668229976687139)
          ·
            refine ⟨27597925643502344965030709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18398617095668229976687139 27597925643502344965030709)
            ·
              refine ⟨2587305529078344840471629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27597925643502344965030709 2587305529078344840471629)
              ·
                refine ⟨970239573404379315176861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2587305529078344840471629 970239573404379315176861)
                ·
                  refine ⟨363839840026642243191323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970239573404379315176861 363839840026642243191323)
                  ·
                    rfl

theorem cell21_1594295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 3].length) (baseStart_1594295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594295 prefixEnd_1594295 := by exact prefixLift 1594295
  have htrace : WordTrace (prefixWord ++ tailWord_1594295) baseStart_1594295 baseEnd_1594295 := by
    simpa [prefixWord, tailWord_1594295, baseEnd_1594295] using wordTrace_append hprefix tailTrace_1594295
  have hstable : (prefixWord ++ tailWord_1594295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594295).length < 2 ^ (prefixWord ++ tailWord_1594295).sum := by decide
  have hdescent : baseEnd_1594295 < baseStart_1594295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594312 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 5]
def baseStart_1594312 : Nat := 118140960795 + 1594312 * 2 ^ 59
def prefixEnd_1594312 : Nat := 4983230072969 + 3 ^ 40 * 1594312 * 2
def baseEnd_1594312 : Nat := 363843719658253991407955

theorem tailTrace_1594312 : CollatzResearch.WordTrace tailWord_1594312 prefixEnd_1594312 363843719658253991407955 := by
  unfold tailWord_1594312
  simp only [CollatzResearch.WordTrace]
  refine ⟨29074667900043692828424595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38766223866724923771232793 29074667900043692828424595)
  ·
    refine ⟨43612001850065539242636893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29074667900043692828424595 43612001850065539242636893)
    ·
      refine ⟨16354500693774577215988835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43612001850065539242636893 16354500693774577215988835)
      ·
        refine ⟨24531751040661865823983253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16354500693774577215988835 24531751040661865823983253)
        ·
          refine ⟨1149925830031024960499215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24531751040661865823983253 1149925830031024960499215)
          ·
            refine ⟨1724888745046537440748823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149925830031024960499215 1724888745046537440748823)
            ·
              refine ⟨2587333117569806161123235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724888745046537440748823 2587333117569806161123235)
              ·
                refine ⟨3880999676354709241684853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587333117569806161123235 3880999676354709241684853)
                ·
                  refine ⟨363843719658253991407955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3880999676354709241684853 363843719658253991407955)
                  ·
                    rfl

theorem cell21_1594312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_1594312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594312 prefixEnd_1594312 := by exact prefixLift 1594312
  have htrace : WordTrace (prefixWord ++ tailWord_1594312) baseStart_1594312 baseEnd_1594312 := by
    simpa [prefixWord, tailWord_1594312, baseEnd_1594312] using wordTrace_append hprefix tailTrace_1594312
  have hstable : (prefixWord ++ tailWord_1594312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594312).length < 2 ^ (prefixWord ++ tailWord_1594312).sum := by decide
  have hdescent : baseEnd_1594312 < baseStart_1594312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594337 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 7]
def baseStart_1594337 : Nat := 118140960795 + 1594337 * 2 ^ 59
def prefixEnd_1594337 : Nat := 4983230072969 + 3 ^ 40 * 1594337 * 2
def baseEnd_1594337 : Nat := 363849424998859503491237

theorem tailTrace_1594337 : CollatzResearch.WordTrace tailWord_1594337 prefixEnd_1594337 363849424998859503491237 := by
  unfold tailWord_1594337
  simp only [CollatzResearch.WordTrace]
  refine ⟨58150247624996814926509265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38766831749997876617672843 58150247624996814926509265)
  ·
    refine ⟨43612685718747611194881949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58150247624996814926509265 43612685718747611194881949)
    ·
      refine ⟨16354757144530354198080731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43612685718747611194881949 16354757144530354198080731)
      ·
        refine ⟨24532135716795531297121097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16354757144530354198080731 24532135716795531297121097)
        ·
          refine ⟨18399101787596648472840823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24532135716795531297121097 18399101787596648472840823)
          ·
            refine ⟨27598652681394972709261235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18399101787596648472840823 27598652681394972709261235)
            ·
              refine ⟨41397979022092459063891853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27598652681394972709261235 41397979022092459063891853)
              ·
                refine ⟨15524242133284672148959445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41397979022092459063891853 15524242133284672148959445)
                ·
                  refine ⟨363849424998859503491237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15524242133284672148959445 363849424998859503491237)
                  ·
                    rfl

theorem cell21_1594337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_1594337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594337 prefixEnd_1594337 := by exact prefixLift 1594337
  have htrace : WordTrace (prefixWord ++ tailWord_1594337) baseStart_1594337 baseEnd_1594337 := by
    simpa [prefixWord, tailWord_1594337, baseEnd_1594337] using wordTrace_append hprefix tailTrace_1594337
  have hstable : (prefixWord ++ tailWord_1594337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594337).length < 2 ^ (prefixWord ++ tailWord_1594337).sum := by decide
  have hdescent : baseEnd_1594337 < baseStart_1594337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594357 : List Nat := [1, 3, 5, 2, 2, 8]
def baseStart_1594357 : Nat := 118140960795 + 1594357 * 2 ^ 59
def prefixEnd_1594357 : Nat := 4983230072969 + 3 ^ 40 * 1594357 * 2
def baseEnd_1594357 : Nat := 13476073676716441228069

theorem tailTrace_1594357 : CollatzResearch.WordTrace tailWord_1594357 prefixEnd_1594357 13476073676716441228069 := by
  unfold tailWord_1594357
  simp only [CollatzResearch.WordTrace]
  refine ⟨58150977084924358342237325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38767318056616238894824883 58150977084924358342237325)
  ·
    refine ⟨21806616406846634378338997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58150977084924358342237325 21806616406846634378338997)
    ·
      refine ⟨2044370288141871972969281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21806616406846634378338997 2044370288141871972969281)
      ·
        refine ⟨1533277716106403979726961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2044370288141871972969281 1533277716106403979726961)
        ·
          refine ⟨1149958287079802984795221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1533277716106403979726961 1149958287079802984795221)
          ·
            refine ⟨13476073676716441228069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1149958287079802984795221 13476073676716441228069)
            ·
              rfl

theorem cell21_1594357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 8].length) (baseStart_1594357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594357 prefixEnd_1594357 := by exact prefixLift 1594357
  have htrace : WordTrace (prefixWord ++ tailWord_1594357) baseStart_1594357 baseEnd_1594357 := by
    simpa [prefixWord, tailWord_1594357, baseEnd_1594357] using wordTrace_append hprefix tailTrace_1594357
  have hstable : (prefixWord ++ tailWord_1594357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594357).length < 2 ^ (prefixWord ++ tailWord_1594357).sum := by decide
  have hdescent : baseEnd_1594357 < baseStart_1594357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594579 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 8]
def baseStart_1594579 : Nat := 118140960795 + 1594579 * 2 ^ 59
def prefixEnd_1594579 : Nat := 4983230072969 + 3 ^ 40 * 1594579 * 2
def baseEnd_1594579 : Nat := 363904652695920860457409

theorem tailTrace_1594579 : CollatzResearch.WordTrace tailWord_1594579 prefixEnd_1594579 363904652695920860457409 := by
  unfold tailWord_1594579
  simp only [CollatzResearch.WordTrace]
  refine ⟨58159074090120090256818791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38772716060080060171212527 58159074090120090256818791)
  ·
    refine ⟨87238611135180135385228187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58159074090120090256818791 87238611135180135385228187)
    ·
      refine ⟨130857916702770203077842281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87238611135180135385228187 130857916702770203077842281)
      ·
        refine ⟨98143437527077652308381711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130857916702770203077842281 98143437527077652308381711)
        ·
          refine ⟨147215156290616478462572567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98143437527077652308381711 147215156290616478462572567)
          ·
            refine ⟨220822734435924717693858851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147215156290616478462572567 220822734435924717693858851)
            ·
              refine ⟨331234101653887076540788277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220822734435924717693858851 331234101653887076540788277)
              ·
                refine ⟨31053197030051913425698901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 331234101653887076540788277 31053197030051913425698901)
                ·
                  refine ⟨363904652695920860457409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31053197030051913425698901 363904652695920860457409)
                  ·
                    rfl

theorem cell21_1594579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_1594579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594579 prefixEnd_1594579 := by exact prefixLift 1594579
  have htrace : WordTrace (prefixWord ++ tailWord_1594579) baseStart_1594579 baseEnd_1594579 := by
    simpa [prefixWord, tailWord_1594579, baseEnd_1594579] using wordTrace_append hprefix tailTrace_1594579
  have hstable : (prefixWord ++ tailWord_1594579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594579).length < 2 ^ (prefixWord ++ tailWord_1594579).sum := by decide
  have hdescent : baseEnd_1594579 < baseStart_1594579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594599 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 5]
def baseStart_1594599 : Nat := 118140960795 + 1594599 * 2 ^ 59
def prefixEnd_1594599 : Nat := 4983230072969 + 3 ^ 40 * 1594599 * 2
def baseEnd_1594599 : Nat := 363909216968405270124035

theorem tailTrace_1594599 : CollatzResearch.WordTrace tailWord_1594599 prefixEnd_1594599 363909216968405270124035 := by
  unfold tailWord_1594599
  simp only [CollatzResearch.WordTrace]
  refine ⟨58159803550047633672546851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38773202366698422448364567 58159803550047633672546851)
  ·
    refine ⟨87239705325071450508820277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58159803550047633672546851 87239705325071450508820277)
    ·
      refine ⟨8178722374225448485201901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87239705325071450508820277 8178722374225448485201901)
      ·
        refine ⟨3067020890334543181950713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8178722374225448485201901 3067020890334543181950713)
        ·
          refine ⟨2300265667750907386463035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3067020890334543181950713 2300265667750907386463035)
          ·
            refine ⟨3450398501626361079694553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300265667750907386463035 3450398501626361079694553)
            ·
              refine ⟨2587798876219770809770915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3450398501626361079694553 2587798876219770809770915)
              ·
                refine ⟨3881698314329656214656373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587798876219770809770915 3881698314329656214656373)
                ·
                  refine ⟨363909216968405270124035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3881698314329656214656373 363909216968405270124035)
                  ·
                    rfl

theorem cell21_1594599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 5].length) (baseStart_1594599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594599 prefixEnd_1594599 := by exact prefixLift 1594599
  have htrace : WordTrace (prefixWord ++ tailWord_1594599) baseStart_1594599 baseEnd_1594599 := by
    simpa [prefixWord, tailWord_1594599, baseEnd_1594599] using wordTrace_append hprefix tailTrace_1594599
  have hstable : (prefixWord ++ tailWord_1594599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594599).length < 2 ^ (prefixWord ++ tailWord_1594599).sum := by decide
  have hdescent : baseEnd_1594599 < baseStart_1594599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594627 : List Nat := [1, 1, 1, 3, 2, 4, 4, 5]
def baseStart_1594627 : Nat := 118140960795 + 1594627 * 2 ^ 59
def prefixEnd_1594627 : Nat := 4983230072969 + 3 ^ 40 * 1594627 * 2
def baseEnd_1594627 : Nat := 121305202316627814552437

theorem tailTrace_1594627 : CollatzResearch.WordTrace tailWord_1594627 prefixEnd_1594627 121305202316627814552437 := by
  unfold tailWord_1594627
  simp only [CollatzResearch.WordTrace]
  refine ⟨58160824793946194454566135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38773883195964129636377423 58160824793946194454566135)
  ·
    refine ⟨87241237190919291681849203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58160824793946194454566135 87241237190919291681849203)
    ·
      refine ⟨130861855786378937522773805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87241237190919291681849203 130861855786378937522773805)
      ·
        refine ⟨49073195919892101571040177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130861855786378937522773805 49073195919892101571040177)
        ·
          refine ⟨36804896939919076178280133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49073195919892101571040177 36804896939919076178280133)
          ·
            refine ⟨6900918176234826783427525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36804896939919076178280133 6900918176234826783427525)
            ·
              refine ⟨1293922158044030021892661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6900918176234826783427525 1293922158044030021892661)
              ·
                refine ⟨121305202316627814552437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1293922158044030021892661 121305202316627814552437)
                ·
                  rfl

theorem cell21_1594627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 5].length) (baseStart_1594627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594627 prefixEnd_1594627 := by exact prefixLift 1594627
  have htrace : WordTrace (prefixWord ++ tailWord_1594627) baseStart_1594627 baseEnd_1594627 := by
    simpa [prefixWord, tailWord_1594627, baseEnd_1594627] using wordTrace_append hprefix tailTrace_1594627
  have hstable : (prefixWord ++ tailWord_1594627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594627).length < 2 ^ (prefixWord ++ tailWord_1594627).sum := by decide
  have hdescent : baseEnd_1594627 < baseStart_1594627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594672 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_1594672 : Nat := 118140960795 + 1594672 * 2 ^ 59
def prefixEnd_1594672 : Nat := 4983230072969 + 3 ^ 40 * 1594672 * 2
def baseEnd_1594672 : Nat := 363925876562973365407219

theorem tailTrace_1594672 : CollatzResearch.WordTrace tailWord_1594672 prefixEnd_1594672 363925876562973365407219 := by
  unfold tailWord_1594672
  simp only [CollatzResearch.WordTrace]
  refine ⟨29081233039391583569977135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38774977385855444759969513 29081233039391583569977135)
  ·
    refine ⟨43621849559087375354965703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29081233039391583569977135 43621849559087375354965703)
    ·
      refine ⟨65432774338631063032448555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43621849559087375354965703 65432774338631063032448555)
      ·
        refine ⟨98149161507946594548672833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65432774338631063032448555 98149161507946594548672833)
        ·
          refine ⟨73611871130959945911504625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98149161507946594548672833 73611871130959945911504625)
          ·
            refine ⟨55208903348219959433628469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73611871130959945911504625 55208903348219959433628469)
            ·
              refine ⟨5175834688895621196902669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55208903348219959433628469 5175834688895621196902669)
              ·
                refine ⟨1940938008335857948838501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5175834688895621196902669 1940938008335857948838501)
                ·
                  refine ⟨363925876562973365407219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1940938008335857948838501 363925876562973365407219)
                  ·
                    rfl

theorem cell21_1594672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_1594672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594672 prefixEnd_1594672 := by exact prefixLift 1594672
  have htrace : WordTrace (prefixWord ++ tailWord_1594672) baseStart_1594672 baseEnd_1594672 := by
    simpa [prefixWord, tailWord_1594672, baseEnd_1594672] using wordTrace_append hprefix tailTrace_1594672
  have hstable : (prefixWord ++ tailWord_1594672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594672).length < 2 ^ (prefixWord ++ tailWord_1594672).sum := by decide
  have hdescent : baseEnd_1594672 < baseStart_1594672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594807 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 8]
def baseStart_1594807 : Nat := 118140960795 + 1594807 * 2 ^ 59
def prefixEnd_1594807 : Nat := 4983230072969 + 3 ^ 40 * 1594807 * 2
def baseEnd_1594807 : Nat := 363956685402243130656943

theorem tailTrace_1594807 : CollatzResearch.WordTrace tailWord_1594807 prefixEnd_1594807 363956685402243130656943 := by
  unfold tailWord_1594807
  simp only [CollatzResearch.WordTrace]
  refine ⟨58167389933294085196118675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38778259955529390130745783 58167389933294085196118675)
  ·
    refine ⟨87251084899941127794178013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58167389933294085196118675 87251084899941127794178013)
    ·
      refine ⟨32719156837477922922816755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87251084899941127794178013 32719156837477922922816755)
      ·
        refine ⟨49078735256216884384225133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32719156837477922922816755 49078735256216884384225133)
        ·
          refine ⟨18404525721081331644084425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49078735256216884384225133 18404525721081331644084425)
          ·
            refine ⟨13803394290810998733063319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18404525721081331644084425 13803394290810998733063319)
            ·
              refine ⟨20705091436216498099594979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13803394290810998733063319 20705091436216498099594979)
              ·
                refine ⟨31057637154324747149392469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20705091436216498099594979 31057637154324747149392469)
                ·
                  refine ⟨363956685402243130656943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31057637154324747149392469 363956685402243130656943)
                  ·
                    rfl

theorem cell21_1594807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_1594807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594807 prefixEnd_1594807 := by exact prefixLift 1594807
  have htrace : WordTrace (prefixWord ++ tailWord_1594807) baseStart_1594807 baseEnd_1594807 := by
    simpa [prefixWord, tailWord_1594807, baseEnd_1594807] using wordTrace_append hprefix tailTrace_1594807
  have hstable : (prefixWord ++ tailWord_1594807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594807).length < 2 ^ (prefixWord ++ tailWord_1594807).sum := by decide
  have hdescent : baseEnd_1594807 < baseStart_1594807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594824 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_1594824 : Nat := 118140960795 + 1594824 * 2 ^ 59
def prefixEnd_1594824 : Nat := 4983230072969 + 3 ^ 40 * 1594824 * 2
def baseEnd_1594824 : Nat := 363960565033854878873575

theorem tailTrace_1594824 : CollatzResearch.WordTrace tailWord_1594824 prefixEnd_1594824 363960565033854878873575 := by
  unfold tailWord_1594824
  simp only [CollatzResearch.WordTrace]
  refine ⟨29084004987116248549743763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38778673316154998066325017 29084004987116248549743763)
  ·
    refine ⟨43626007480674372824615645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29084004987116248549743763 43626007480674372824615645)
    ·
      refine ⟨16359752805252889809230867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43626007480674372824615645 16359752805252889809230867)
      ·
        refine ⟨24539629207879334713846301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16359752805252889809230867 24539629207879334713846301)
        ·
          refine ⟨9202360952954750517692363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24539629207879334713846301 9202360952954750517692363)
          ·
            refine ⟨13803541429432125776538545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9202360952954750517692363 13803541429432125776538545)
            ·
              refine ⟨10352656072074094332403909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13803541429432125776538545 10352656072074094332403909)
              ·
                refine ⟨1941123013513892687325733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10352656072074094332403909 1941123013513892687325733)
                ·
                  refine ⟨363960565033854878873575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941123013513892687325733 363960565033854878873575)
                  ·
                    rfl

theorem cell21_1594824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_1594824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594824 prefixEnd_1594824 := by exact prefixLift 1594824
  have htrace : WordTrace (prefixWord ++ tailWord_1594824) baseStart_1594824 baseEnd_1594824 := by
    simpa [prefixWord, tailWord_1594824, baseEnd_1594824] using wordTrace_append hprefix tailTrace_1594824
  have hstable : (prefixWord ++ tailWord_1594824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594824).length < 2 ^ (prefixWord ++ tailWord_1594824).sum := by decide
  have hdescent : baseEnd_1594824 < baseStart_1594824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594841 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 4]
def baseStart_1594841 : Nat := 118140960795 + 1594841 * 2 ^ 59
def prefixEnd_1594841 : Nat := 4983230072969 + 3 ^ 40 * 1594841 * 2
def baseEnd_1594841 : Nat := 363964444665466627090207

theorem tailTrace_1594841 : CollatzResearch.WordTrace tailWord_1594841 prefixEnd_1594841 363964444665466627090207 := by
  unfold tailWord_1594841
  simp only [CollatzResearch.WordTrace]
  refine ⟨58168630015170909002856377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38779086676780606001904251 58168630015170909002856377)
  ·
    refine ⟨43626472511378181752142283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58168630015170909002856377 43626472511378181752142283)
    ·
      refine ⟨65439708767067272628213425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43626472511378181752142283 65439708767067272628213425)
      ·
        refine ⟨49079781575300454471160069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65439708767067272628213425 49079781575300454471160069)
        ·
          refine ⟨9202459045368835213342513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49079781575300454471160069 9202459045368835213342513)
          ·
            refine ⟨6901844284026626410006885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9202459045368835213342513 6901844284026626410006885)
            ·
              refine ⟨1294095803254992451876291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6901844284026626410006885 1294095803254992451876291)
              ·
                refine ⟨1941143704882488677814437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294095803254992451876291 1941143704882488677814437)
                ·
                  refine ⟨363964444665466627090207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941143704882488677814437 363964444665466627090207)
                  ·
                    rfl

theorem cell21_1594841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_1594841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594841 prefixEnd_1594841 := by exact prefixLift 1594841
  have htrace : WordTrace (prefixWord ++ tailWord_1594841) baseStart_1594841 baseEnd_1594841 := by
    simpa [prefixWord, tailWord_1594841, baseEnd_1594841] using wordTrace_append hprefix tailTrace_1594841
  have hstable : (prefixWord ++ tailWord_1594841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594841).length < 2 ^ (prefixWord ++ tailWord_1594841).sum := by decide
  have hdescent : baseEnd_1594841 < baseStart_1594841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594878 : List Nat := [4, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1594878 : Nat := 118140960795 + 1594878 * 2 ^ 59
def prefixEnd_1594878 : Nat := 4983230072969 + 3 ^ 40 * 1594878 * 2
def baseEnd_1594878 : Nat := 363972888569562784973465

theorem tailTrace_1594878 : CollatzResearch.WordTrace tailWord_1594878 prefixEnd_1594878 363972888569562784973465 := by
  unfold tailWord_1594878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271247439504608040244161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38779986344024576214635525 7271247439504608040244161)
  ·
    refine ⟨5453435579628456030183121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7271247439504608040244161 5453435579628456030183121)
    ·
      refine ⟨4090076684721342022637341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5453435579628456030183121 4090076684721342022637341)
      ·
        refine ⟨1533778756770503258489003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4090076684721342022637341 1533778756770503258489003)
        ·
          refine ⟨2300668135155754887733505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533778756770503258489003 2300668135155754887733505)
          ·
            refine ⟨1725501101366816165800129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2300668135155754887733505 1725501101366816165800129)
            ·
              refine ⟨1294125826025112124350097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725501101366816165800129 1294125826025112124350097)
              ·
                refine ⟨970594369518834093262573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294125826025112124350097 970594369518834093262573)
                ·
                  refine ⟨363972888569562784973465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970594369518834093262573 363972888569562784973465)
                  ·
                    rfl

theorem cell21_1594878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1594878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594878 prefixEnd_1594878 := by exact prefixLift 1594878
  have htrace : WordTrace (prefixWord ++ tailWord_1594878) baseStart_1594878 baseEnd_1594878 := by
    simpa [prefixWord, tailWord_1594878, baseEnd_1594878] using wordTrace_append hprefix tailTrace_1594878
  have hstable : (prefixWord ++ tailWord_1594878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594878).length < 2 ^ (prefixWord ++ tailWord_1594878).sum := by decide
  have hdescent : baseEnd_1594878 < baseStart_1594878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594914 : List Nat := [3, 3, 1, 1, 1, 1, 2, 9]
def baseStart_1594914 : Nat := 118140960795 + 1594914 * 2 ^ 59
def prefixEnd_1594914 : Nat := 4983230072969 + 3 ^ 40 * 1594914 * 2
def baseEnd_1594914 : Nat := 121327034753344907457797

theorem tailTrace_1594914 : CollatzResearch.WordTrace tailWord_1594914 prefixEnd_1594914 121327034753344907457797 := by
  unfold tailWord_1594914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542823135976610617565949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38780861695937628313509197 14542823135976610617565949)
  ·
    refine ⟨5453558675991228981587231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14542823135976610617565949 5453558675991228981587231)
    ·
      refine ⟨8180338013986843472380847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5453558675991228981587231 8180338013986843472380847)
      ·
        refine ⟨12270507020980265208571271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8180338013986843472380847 12270507020980265208571271)
        ·
          refine ⟨18405760531470397812856907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12270507020980265208571271 18405760531470397812856907)
          ·
            refine ⟨27608640797205596719285361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18405760531470397812856907 27608640797205596719285361)
            ·
              refine ⟨20706480597904197539464021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27608640797205596719285361 20706480597904197539464021)
              ·
                refine ⟨121327034753344907457797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20706480597904197539464021 121327034753344907457797)
                ·
                  rfl

theorem cell21_1594914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_1594914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594914 prefixEnd_1594914 := by exact prefixLift 1594914
  have htrace : WordTrace (prefixWord ++ tailWord_1594914) baseStart_1594914 baseEnd_1594914 := by
    simpa [prefixWord, tailWord_1594914, baseEnd_1594914] using wordTrace_append hprefix tailTrace_1594914
  have hstable : (prefixWord ++ tailWord_1594914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594914).length < 2 ^ (prefixWord ++ tailWord_1594914).sum := by decide
  have hdescent : baseEnd_1594914 < baseStart_1594914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594920 : List Nat := [2, 1, 5, 2, 2, 1, 2, 3, 3]
def baseStart_1594920 : Nat := 118140960795 + 1594920 * 2 ^ 59
def prefixEnd_1594920 : Nat := 4983230072969 + 3 ^ 40 * 1594920 * 2
def baseEnd_1594920 : Nat := 363982473541780045273379

theorem tailTrace_1594920 : CollatzResearch.WordTrace tailWord_1594920 prefixEnd_1594920 363982473541780045273379 := by
  unfold tailWord_1594920
  simp only [CollatzResearch.WordTrace]
  refine ⟨29085755690942352747491107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38781007587923136996654809 29085755690942352747491107)
  ·
    refine ⟨43628633536413529121236661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29085755690942352747491107 43628633536413529121236661)
    ·
      refine ⟨4090184394038768355115937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43628633536413529121236661 4090184394038768355115937)
      ·
        refine ⟨3067638295529076266336953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4090184394038768355115937 3067638295529076266336953)
        ·
          refine ⟨2300728721646807199752715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3067638295529076266336953 2300728721646807199752715)
          ·
            refine ⟨3451093082470210799629073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300728721646807199752715 3451093082470210799629073)
            ·
              refine ⟨2588319811852658099721805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451093082470210799629073 2588319811852658099721805)
              ·
                refine ⟨970619929444746787395677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2588319811852658099721805 970619929444746787395677)
                ·
                  refine ⟨363982473541780045273379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970619929444746787395677 363982473541780045273379)
                  ·
                    rfl

theorem cell21_1594920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_1594920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594920 prefixEnd_1594920 := by exact prefixLift 1594920
  have htrace : WordTrace (prefixWord ++ tailWord_1594920) baseStart_1594920 baseEnd_1594920 := by
    simpa [prefixWord, tailWord_1594920, baseEnd_1594920] using wordTrace_append hprefix tailTrace_1594920
  have hstable : (prefixWord ++ tailWord_1594920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594920).length < 2 ^ (prefixWord ++ tailWord_1594920).sum := by decide
  have hdescent : baseEnd_1594920 < baseStart_1594920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594928 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_1594928 : Nat := 118140960795 + 1594928 * 2 ^ 59
def prefixEnd_1594928 : Nat := 4983230072969 + 3 ^ 40 * 1594928 * 2
def baseEnd_1594928 : Nat := 363984299250773809140029

theorem tailTrace_1594928 : CollatzResearch.WordTrace tailWord_1594928 prefixEnd_1594928 363984299250773809140029 := by
  unfold tailWord_1594928
  simp only [CollatzResearch.WordTrace]
  refine ⟨29085901582927861430636719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38781202110570481907515625 29085901582927861430636719)
  ·
    refine ⟨43628852374391792145955079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29085901582927861430636719 43628852374391792145955079)
    ·
      refine ⟨65443278561587688218932619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43628852374391792145955079 65443278561587688218932619)
      ·
        refine ⟨98164917842381532328398929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65443278561587688218932619 98164917842381532328398929)
        ·
          refine ⟨73623688381786149246299197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98164917842381532328398929 73623688381786149246299197)
          ·
            refine ⟨27608883143169805967362199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73623688381786149246299197 27608883143169805967362199)
            ·
              refine ⟨41413324714754708951043299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27608883143169805967362199 41413324714754708951043299)
              ·
                refine ⟨62119987072132063426564949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41413324714754708951043299 62119987072132063426564949)
                ·
                  refine ⟨363984299250773809140029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62119987072132063426564949 363984299250773809140029)
                  ·
                    rfl

theorem cell21_1594928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_1594928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594928 prefixEnd_1594928 := by exact prefixLift 1594928
  have htrace : WordTrace (prefixWord ++ tailWord_1594928) baseStart_1594928 baseEnd_1594928 := by
    simpa [prefixWord, tailWord_1594928, baseEnd_1594928] using wordTrace_append hprefix tailTrace_1594928
  have hstable : (prefixWord ++ tailWord_1594928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594928).length < 2 ^ (prefixWord ++ tailWord_1594928).sum := by decide
  have hdescent : baseEnd_1594928 < baseStart_1594928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594979 : List Nat := [1, 1, 1, 5, 1, 5, 1, 3, 3]
def baseStart_1594979 : Nat := 118140960795 + 1594979 * 2 ^ 59
def prefixEnd_1594979 : Nat := 4983230072969 + 3 ^ 40 * 1594979 * 2
def baseEnd_1594979 : Nat := 363995938145609053789925

theorem tailTrace_1594979 : CollatzResearch.WordTrace tailWord_1594979 prefixEnd_1594979 363995938145609053789925 := by
  unfold tailWord_1594979
  simp only [CollatzResearch.WordTrace]
  refine ⟨58173663288670958571379991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38782442192447305714253327 58173663288670958571379991)
  ·
    refine ⟨87260494933006437857069987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58173663288670958571379991 87260494933006437857069987)
    ·
      refine ⟨130890742399509656785604981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87260494933006437857069987 130890742399509656785604981)
      ·
        refine ⟨12271007099954030323650467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130890742399509656785604981 12271007099954030323650467)
        ·
          refine ⟨18406510649931045485475701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12271007099954030323650467 18406510649931045485475701)
          ·
            refine ⟨1725610373431035514263347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18406510649931045485475701 1725610373431035514263347)
            ·
              refine ⟨2588415560146553271395021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725610373431035514263347 2588415560146553271395021)
              ·
                refine ⟨970655835054957476773133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2588415560146553271395021 970655835054957476773133)
                ·
                  refine ⟨363995938145609053789925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970655835054957476773133 363995938145609053789925)
                  ·
                    rfl

theorem cell21_1594979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 3].length) (baseStart_1594979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1594979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1594979 prefixEnd_1594979 := by exact prefixLift 1594979
  have htrace : WordTrace (prefixWord ++ tailWord_1594979) baseStart_1594979 baseEnd_1594979 := by
    simpa [prefixWord, tailWord_1594979, baseEnd_1594979] using wordTrace_append hprefix tailTrace_1594979
  have hstable : (prefixWord ++ tailWord_1594979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594979).length < 2 ^ (prefixWord ++ tailWord_1594979).sum := by decide
  have hdescent : baseEnd_1594979 < baseStart_1594979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595066 : List Nat := [3, 1, 1, 1, 2, 4, 3, 6]
def baseStart_1595066 : Nat := 118140960795 + 1595066 * 2 ^ 59
def prefixEnd_1595066 : Nat := 4983230072969 + 3 ^ 40 * 1595066 * 2
def baseEnd_1595066 : Nat := 121338597576972078613249

theorem tailTrace_1595066 : CollatzResearch.WordTrace tailWord_1595066 prefixEnd_1595066 121338597576972078613249 := by
  unfold tailWord_1595066
  simp only [CollatzResearch.WordTrace]
  refine ⟨14544209109838943107449263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38784557626237181619864701 14544209109838943107449263)
  ·
    refine ⟨21816313664758414661173895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14544209109838943107449263 21816313664758414661173895)
    ·
      refine ⟨32724470497137621991760843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21816313664758414661173895 32724470497137621991760843)
      ·
        refine ⟨49086705745706432987641265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32724470497137621991760843 49086705745706432987641265)
        ·
          refine ⟨36815029309279824740730949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49086705745706432987641265 36815029309279824740730949)
          ·
            refine ⟨6902817995489967138887053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36815029309279824740730949 6902817995489967138887053)
            ·
              refine ⟨2588556748308737677082645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6902817995489967138887053 2588556748308737677082645)
              ·
                refine ⟨121338597576972078613249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2588556748308737677082645 121338597576972078613249)
                ·
                  rfl

theorem cell21_1595066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_1595066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595066 prefixEnd_1595066 := by exact prefixLift 1595066
  have htrace : WordTrace (prefixWord ++ tailWord_1595066) baseStart_1595066 baseEnd_1595066 := by
    simpa [prefixWord, tailWord_1595066, baseEnd_1595066] using wordTrace_append hprefix tailTrace_1595066
  have hstable : (prefixWord ++ tailWord_1595066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595066).length < 2 ^ (prefixWord ++ tailWord_1595066).sum := by decide
  have hdescent : baseEnd_1595066 < baseStart_1595066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595114 : List Nat := [3, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_1595114 : Nat := 118140960795 + 1595114 * 2 ^ 59
def prefixEnd_1595114 : Nat := 4983230072969 + 3 ^ 40 * 1595114 * 2
def baseEnd_1595114 : Nat := 364026746984878819039649

theorem tailTrace_1595114 : CollatzResearch.WordTrace tailWord_1595114 prefixEnd_1595114 364026746984878819039649 := by
  unfold tailWord_1595114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14544646785795469156886099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38785724762121251085029597 14544646785795469156886099)
  ·
    refine ⟨21816970178693203735329149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14544646785795469156886099 21816970178693203735329149)
    ·
      refine ⟨8181363817009951400748431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21816970178693203735329149 8181363817009951400748431)
      ·
        refine ⟨12272045725514927101122647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8181363817009951400748431 12272045725514927101122647)
        ·
          refine ⟨18408068588272390651683971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12272045725514927101122647 18408068588272390651683971)
          ·
            refine ⟨27612102882408585977525957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18408068588272390651683971 27612102882408585977525957)
            ·
              refine ⟨5177269290451609870786117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27612102882408585977525957 5177269290451609870786117)
              ·
                refine ⟨970737991959676850772397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5177269290451609870786117 970737991959676850772397)
                ·
                  refine ⟨364026746984878819039649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970737991959676850772397 364026746984878819039649)
                  ·
                    rfl

theorem cell21_1595114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_1595114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595114 prefixEnd_1595114 := by exact prefixLift 1595114
  have htrace : WordTrace (prefixWord ++ tailWord_1595114) baseStart_1595114 baseEnd_1595114 := by
    simpa [prefixWord, tailWord_1595114, baseEnd_1595114] using wordTrace_append hprefix tailTrace_1595114
  have hstable : (prefixWord ++ tailWord_1595114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595114).length < 2 ^ (prefixWord ++ tailWord_1595114).sum := by decide
  have hdescent : baseEnd_1595114 < baseStart_1595114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595173 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 5]
def baseStart_1595173 : Nat := 118140960795 + 1595173 * 2 ^ 59
def prefixEnd_1595173 : Nat := 4983230072969 + 3 ^ 40 * 1595173 * 2
def baseEnd_1595173 : Nat := 364040211588707827556195

theorem tailTrace_1595173 : CollatzResearch.WordTrace tailWord_1595173 prefixEnd_1595173 364040211588707827556195 := by
  unfold tailWord_1595173
  simp only [CollatzResearch.WordTrace]
  refine ⟨58180739049968129703942173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38787159366645419802628115 58180739049968129703942173)
  ·
    refine ⟨21817777143738048638978315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58180739049968129703942173 21817777143738048638978315)
    ·
      refine ⟨32726665715607072958467473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21817777143738048638978315 32726665715607072958467473)
      ·
        refine ⟨24544999286705304718850605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32726665715607072958467473 24544999286705304718850605)
        ·
          refine ⟨9204374732514489269568977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24544999286705304718850605 9204374732514489269568977)
          ·
            refine ⟨6903281049385866952176733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9204374732514489269568977 6903281049385866952176733)
            ·
              refine ⟨2588730393519700107066275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6903281049385866952176733 2588730393519700107066275)
              ·
                refine ⟨3883095590279550160599413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588730393519700107066275 3883095590279550160599413)
                ·
                  refine ⟨364040211588707827556195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3883095590279550160599413 364040211588707827556195)
                  ·
                    rfl

theorem cell21_1595173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_1595173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595173 prefixEnd_1595173 := by exact prefixLift 1595173
  have htrace : WordTrace (prefixWord ++ tailWord_1595173) baseStart_1595173 baseEnd_1595173 := by
    simpa [prefixWord, tailWord_1595173, baseEnd_1595173] using wordTrace_append hprefix tailTrace_1595173
  have hstable : (prefixWord ++ tailWord_1595173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595173).length < 2 ^ (prefixWord ++ tailWord_1595173).sum := by decide
  have hdescent : baseEnd_1595173 < baseStart_1595173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595235 : List Nat := [1, 1, 1, 5, 4, 2, 1, 6]
def baseStart_1595235 : Nat := 118140960795 + 1595235 * 2 ^ 59
def prefixEnd_1595235 : Nat := 4983230072969 + 3 ^ 40 * 1595235 * 2
def baseEnd_1595235 : Nat := 121351453611136499174245

theorem tailTrace_1595235 : CollatzResearch.WordTrace tailWord_1595235 prefixEnd_1595235 121351453611136499174245 := by
  unfold tailWord_1595235
  simp only [CollatzResearch.WordTrace]
  refine ⟨58183000375743514292699159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38788666917162342861799439 58183000375743514292699159)
  ·
    refine ⟨87274500563615271439048739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58183000375743514292699159 87274500563615271439048739)
    ·
      refine ⟨130911750845422907158573109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87274500563615271439048739 130911750845422907158573109)
      ·
        refine ⟨12272976641758397546116229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130911750845422907158573109 12272976641758397546116229)
        ·
          refine ⟨2301183120329699539896793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12272976641758397546116229 2301183120329699539896793)
          ·
            refine ⟨1725887340247274654922595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301183120329699539896793 1725887340247274654922595)
            ·
              refine ⟨2588831010370911982383893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725887340247274654922595 2588831010370911982383893)
              ·
                refine ⟨121351453611136499174245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2588831010370911982383893 121351453611136499174245)
                ·
                  rfl

theorem cell21_1595235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 6].length) (baseStart_1595235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595235 prefixEnd_1595235 := by exact prefixLift 1595235
  have htrace : WordTrace (prefixWord ++ tailWord_1595235) baseStart_1595235 baseEnd_1595235 := by
    simpa [prefixWord, tailWord_1595235, baseEnd_1595235] using wordTrace_append hprefix tailTrace_1595235
  have hstable : (prefixWord ++ tailWord_1595235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595235).length < 2 ^ (prefixWord ++ tailWord_1595235).sum := by decide
  have hdescent : baseEnd_1595235 < baseStart_1595235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595339 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 4]
def baseStart_1595339 : Nat := 118140960795 + 1595339 * 2 ^ 59
def prefixEnd_1595339 : Nat := 4983230072969 + 3 ^ 40 * 1595339 * 2
def baseEnd_1595339 : Nat := 364078095050328427789189

theorem tailTrace_1595339 : CollatzResearch.WordTrace tailWord_1595339 prefixEnd_1595339 364078095050328427789189 := by
  unfold tailWord_1595339
  simp only [CollatzResearch.WordTrace]
  refine ⟨58186793567366740054485071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38791195711577826702990047 58186793567366740054485071)
  ·
    refine ⟨87280190351050110081727607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58186793567366740054485071 87280190351050110081727607)
    ·
      refine ⟨130920285526575165122591411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87280190351050110081727607 130920285526575165122591411)
      ·
        refine ⟨196380428289862747683887117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130920285526575165122591411 196380428289862747683887117)
        ·
          refine ⟨73642660608698530381457669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196380428289862747683887117 73642660608698530381457669)
          ·
            refine ⟨13807998864130974446523313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73642660608698530381457669 13807998864130974446523313)
            ·
              refine ⟨10355999148098230834892485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13807998864130974446523313 10355999148098230834892485)
              ·
                refine ⟨1941749840268418281542341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10355999148098230834892485 1941749840268418281542341)
                ·
                  refine ⟨364078095050328427789189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941749840268418281542341 364078095050328427789189)
                  ·
                    rfl

theorem cell21_1595339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 4].length) (baseStart_1595339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595339 prefixEnd_1595339 := by exact prefixLift 1595339
  have htrace : WordTrace (prefixWord ++ tailWord_1595339) baseStart_1595339 baseEnd_1595339 := by
    simpa [prefixWord, tailWord_1595339, baseEnd_1595339] using wordTrace_append hprefix tailTrace_1595339
  have hstable : (prefixWord ++ tailWord_1595339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595339).length < 2 ^ (prefixWord ++ tailWord_1595339).sum := by decide
  have hdescent : baseEnd_1595339 < baseStart_1595339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595446 : List Nat := [5, 1, 2, 1, 1, 1, 10]
def baseStart_1595446 : Nat := 118140960795 + 1595446 * 2 ^ 59
def prefixEnd_1595446 : Nat := 4983230072969 + 3 ^ 40 * 1595446 * 2
def baseEnd_1595446 : Nat := 40455834878680002167293

theorem tailTrace_1595446 : CollatzResearch.WordTrace tailWord_1595446 prefixEnd_1595446 40455834878680002167293 := by
  unfold tailWord_1595446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636918511123693583039387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38793797451986064885753461 3636918511123693583039387)
  ·
    refine ⟨5455377766685540374559081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3636918511123693583039387 5455377766685540374559081)
    ·
      refine ⟨4091533325014155280919311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5455377766685540374559081 4091533325014155280919311)
      ·
        refine ⟨6137299987521232921378967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091533325014155280919311 6137299987521232921378967)
        ·
          refine ⟨9205949981281849382068451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6137299987521232921378967 9205949981281849382068451)
          ·
            refine ⟨13808924971922774073102677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9205949981281849382068451 13808924971922774073102677)
            ·
              refine ⟨40455834878680002167293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13808924971922774073102677 40455834878680002167293)
              ·
                rfl

theorem cell21_1595446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 10].length) (baseStart_1595446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595446 prefixEnd_1595446 := by exact prefixLift 1595446
  have htrace : WordTrace (prefixWord ++ tailWord_1595446) baseStart_1595446 baseEnd_1595446 := by
    simpa [prefixWord, tailWord_1595446, baseEnd_1595446] using wordTrace_append hprefix tailTrace_1595446
  have hstable : (prefixWord ++ tailWord_1595446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595446).length < 2 ^ (prefixWord ++ tailWord_1595446).sum := by decide
  have hdescent : baseEnd_1595446 < baseStart_1595446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595449 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 4]
def baseStart_1595449 : Nat := 118140960795 + 1595449 * 2 ^ 59
def prefixEnd_1595449 : Nat := 4983230072969 + 3 ^ 40 * 1595449 * 2
def baseEnd_1595449 : Nat := 364103198548992680955631

theorem tailTrace_1595449 : CollatzResearch.WordTrace tailWord_1595449 prefixEnd_1595449 364103198548992680955631 := by
  unfold tailWord_1595449
  simp only [CollatzResearch.WordTrace]
  refine ⟨58190805596968228840989401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38793870397978819227326267 58190805596968228840989401)
  ·
    refine ⟨43643104197726171630742051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58190805596968228840989401 43643104197726171630742051)
    ·
      refine ⟨65464656296589257446113077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43643104197726171630742051 65464656296589257446113077)
      ·
        refine ⟨6137311527805242885573101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65464656296589257446113077 6137311527805242885573101)
        ·
          refine ⟨2301491822926966082089913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6137311527805242885573101 2301491822926966082089913)
          ·
            refine ⟨1726118867195224561567435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301491822926966082089913 1726118867195224561567435)
            ·
              refine ⟨2589178300792836842351153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726118867195224561567435 2589178300792836842351153)
              ·
                refine ⟨1941883725594627631763365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2589178300792836842351153 1941883725594627631763365)
                ·
                  refine ⟨364103198548992680955631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941883725594627631763365 364103198548992680955631)
                  ·
                    rfl

theorem cell21_1595449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_1595449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595449 prefixEnd_1595449 := by exact prefixLift 1595449
  have htrace : WordTrace (prefixWord ++ tailWord_1595449) baseStart_1595449 baseEnd_1595449 := by
    simpa [prefixWord, tailWord_1595449, baseEnd_1595449] using wordTrace_append hprefix tailTrace_1595449
  have hstable : (prefixWord ++ tailWord_1595449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595449).length < 2 ^ (prefixWord ++ tailWord_1595449).sum := by decide
  have hdescent : baseEnd_1595449 < baseStart_1595449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595486 : List Nat := [4, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1595486 : Nat := 118140960795 + 1595486 * 2 ^ 59
def prefixEnd_1595486 : Nat := 4983230072969 + 3 ^ 40 * 1595486 * 2
def baseEnd_1595486 : Nat := 364111642453088838838889

theorem tailTrace_1595486 : CollatzResearch.WordTrace tailWord_1595486 prefixEnd_1595486 364111642453088838838889 := by
  unfold tailWord_1595486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7274019387229273020010789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38794770065222789440057541 7274019387229273020010789)
  ·
    refine ⟨1363878635105488691252023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7274019387229273020010789 1363878635105488691252023)
    ·
      refine ⟨2045817952658233036878035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363878635105488691252023 2045817952658233036878035)
      ·
        refine ⟨3068726928987349555317053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045817952658233036878035 3068726928987349555317053)
        ·
          refine ⟨1150772598370256083243895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3068726928987349555317053 1150772598370256083243895)
          ·
            refine ⟨1726158897555384124865843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150772598370256083243895 1726158897555384124865843)
            ·
              refine ⟨2589238346333076187298765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726158897555384124865843 2589238346333076187298765)
              ·
                refine ⟨970964379874903570237037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2589238346333076187298765 970964379874903570237037)
                ·
                  refine ⟨364111642453088838838889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970964379874903570237037 364111642453088838838889)
                  ·
                    rfl

theorem cell21_1595486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1595486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595486 prefixEnd_1595486 := by exact prefixLift 1595486
  have htrace : WordTrace (prefixWord ++ tailWord_1595486) baseStart_1595486 baseEnd_1595486 := by
    simpa [prefixWord, tailWord_1595486, baseEnd_1595486] using wordTrace_append hprefix tailTrace_1595486
  have hstable : (prefixWord ++ tailWord_1595486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595486).length < 2 ^ (prefixWord ++ tailWord_1595486).sum := by decide
  have hdescent : baseEnd_1595486 < baseStart_1595486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595525 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 4]
def baseStart_1595525 : Nat := 118140960795 + 1595525 * 2 ^ 59
def prefixEnd_1595525 : Nat := 4983230072969 + 3 ^ 40 * 1595525 * 2
def baseEnd_1595525 : Nat := 364120542784433437688809

theorem tailTrace_1595525 : CollatzResearch.WordTrace tailWord_1595525 prefixEnd_1595525 364120542784433437688809 := by
  unfold tailWord_1595525
  simp only [CollatzResearch.WordTrace]
  refine ⟨58193577544692893820756029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38795718363128595880504019 58193577544692893820756029)
  ·
    refine ⟨21822591579259835182783511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58193577544692893820756029 21822591579259835182783511)
    ·
      refine ⟨32733887368889752774175267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21822591579259835182783511 32733887368889752774175267)
      ·
        refine ⟨49100831053334629161262901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32733887368889752774175267 49100831053334629161262901)
        ·
          refine ⟨4603202911250121483868397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49100831053334629161262901 4603202911250121483868397)
          ·
            refine ⟨1726201091718795556450649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4603202911250121483868397 1726201091718795556450649)
            ·
              refine ⟨1294650818789096667337987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726201091718795556450649 1294650818789096667337987)
              ·
                refine ⟨1941976228183645001006981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294650818789096667337987 1941976228183645001006981)
                ·
                  refine ⟨364120542784433437688809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941976228183645001006981 364120542784433437688809)
                  ·
                    rfl

theorem cell21_1595525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_1595525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595525 prefixEnd_1595525 := by exact prefixLift 1595525
  have htrace : WordTrace (prefixWord ++ tailWord_1595525) baseStart_1595525 baseEnd_1595525 := by
    simpa [prefixWord, tailWord_1595525, baseEnd_1595525] using wordTrace_append hprefix tailTrace_1595525
  have hstable : (prefixWord ++ tailWord_1595525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595525).length < 2 ^ (prefixWord ++ tailWord_1595525).sum := by decide
  have hdescent : baseEnd_1595525 < baseStart_1595525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595618 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1595618 : Nat := 118140960795 + 1595618 * 2 ^ 59
def prefixEnd_1595618 : Nat := 4983230072969 + 3 ^ 40 * 1595618 * 2
def baseEnd_1595618 : Nat := 364141766651485942638619

theorem tailTrace_1595618 : CollatzResearch.WordTrace tailWord_1595618 prefixEnd_1595618 364141766651485942638619 := by
  unfold tailWord_1595618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14549242383338992675972877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38797979688903980469261005 14549242383338992675972877)
  ·
    refine ⟨5455965893752122253489829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14549242383338992675972877 5455965893752122253489829)
    ·
      refine ⟨1022993605078522922529343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5455965893752122253489829 1022993605078522922529343)
      ·
        refine ⟨1534490407617784383794015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022993605078522922529343 1534490407617784383794015)
        ·
          refine ⟨2301735611426676575691023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534490407617784383794015 2301735611426676575691023)
          ·
            refine ⟨3452603417140014863536535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301735611426676575691023 3452603417140014863536535)
            ·
              refine ⟨5178905125710022295304803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452603417140014863536535 5178905125710022295304803)
              ·
                refine ⟨7768357688565033442957205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178905125710022295304803 7768357688565033442957205)
                ·
                  refine ⟨364141766651485942638619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7768357688565033442957205 364141766651485942638619)
                  ·
                    rfl

theorem cell21_1595618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1595618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595618 prefixEnd_1595618 := by exact prefixLift 1595618
  have htrace : WordTrace (prefixWord ++ tailWord_1595618) baseStart_1595618 baseEnd_1595618 := by
    simpa [prefixWord, tailWord_1595618, baseEnd_1595618] using wordTrace_append hprefix tailTrace_1595618
  have hstable : (prefixWord ++ tailWord_1595618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595618).length < 2 ^ (prefixWord ++ tailWord_1595618).sum := by decide
  have hdescent : baseEnd_1595618 < baseStart_1595618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595657 : List Nat := [1, 2, 1, 1, 3, 5, 1, 7]
def baseStart_1595657 : Nat := 118140960795 + 1595657 * 2 ^ 59
def prefixEnd_1595657 : Nat := 4983230072969 + 3 ^ 40 * 1595657 * 2
def baseEnd_1595657 : Nat := 121383555660943513829513

theorem tailTrace_1595657 : CollatzResearch.WordTrace tailWord_1595657 prefixEnd_1595657 121383555660943513829513 := by
  unfold tailWord_1595657
  simp only [CollatzResearch.WordTrace]
  refine ⟨58198391980214680364561225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38798927986809786909707483 58198391980214680364561225)
  ·
    refine ⟨43648793985161010273420919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58198391980214680364561225 43648793985161010273420919)
    ·
      refine ⟨65473190977741515410131379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43648793985161010273420919 65473190977741515410131379)
      ·
        refine ⟨98209786466612273115197069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65473190977741515410131379 98209786466612273115197069)
        ·
          refine ⟨36828669924979602418198901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98209786466612273115197069 36828669924979602418198901)
          ·
            refine ⟨3452687805466837726706147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36828669924979602418198901 3452687805466837726706147)
            ·
              refine ⟨5179031708200256590059221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452687805466837726706147 5179031708200256590059221)
              ·
                refine ⟨121383555660943513829513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5179031708200256590059221 121383555660943513829513)
                ·
                  rfl

theorem cell21_1595657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 7].length) (baseStart_1595657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595657 prefixEnd_1595657 := by exact prefixLift 1595657
  have htrace : WordTrace (prefixWord ++ tailWord_1595657) baseStart_1595657 baseEnd_1595657 := by
    simpa [prefixWord, tailWord_1595657, baseEnd_1595657] using wordTrace_append hprefix tailTrace_1595657
  have hstable : (prefixWord ++ tailWord_1595657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595657).length < 2 ^ (prefixWord ++ tailWord_1595657).sum := by decide
  have hdescent : baseEnd_1595657 < baseStart_1595657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595674 : List Nat := [3, 1, 1, 3, 4, 2, 7]
def baseStart_1595674 : Nat := 118140960795 + 1595674 * 2 ^ 59
def prefixEnd_1595674 : Nat := 4983230072969 + 3 ^ 40 * 1595674 * 2
def baseEnd_1595674 : Nat := 40461616290493587745019

theorem tailTrace_1595674 : CollatzResearch.WordTrace tailWord_1595674 prefixEnd_1595674 40461616290493587745019 := by
  unfold tailWord_1595674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14549753005288273066982519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38799341347435394845286717 14549753005288273066982519)
  ·
    refine ⟨21824629507932409600473779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14549753005288273066982519 21824629507932409600473779)
    ·
      refine ⟨32736944261898614400710669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21824629507932409600473779 32736944261898614400710669)
      ·
        refine ⟨12276354098211980400266501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32736944261898614400710669 12276354098211980400266501)
        ·
          refine ⟨2301816393414746325049969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12276354098211980400266501 2301816393414746325049969)
          ·
            refine ⟨1726362295061059743787477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301816393414746325049969 1726362295061059743787477)
            ·
              refine ⟨40461616290493587745019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1726362295061059743787477 40461616290493587745019)
              ·
                rfl

theorem cell21_1595674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 7].length) (baseStart_1595674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595674 prefixEnd_1595674 := by exact prefixLift 1595674
  have htrace : WordTrace (prefixWord ++ tailWord_1595674) baseStart_1595674 baseEnd_1595674 := by
    simpa [prefixWord, tailWord_1595674, baseEnd_1595674] using wordTrace_append hprefix tailTrace_1595674
  have hstable : (prefixWord ++ tailWord_1595674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595674).length < 2 ^ (prefixWord ++ tailWord_1595674).sum := by decide
  have hdescent : baseEnd_1595674 < baseStart_1595674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595733 : List Nat := [1, 3, 2, 2, 4, 9]
def baseStart_1595733 : Nat := 118140960795 + 1595733 * 2 ^ 59
def prefixEnd_1595733 : Nat := 4983230072969 + 3 ^ 40 * 1595733 * 2
def baseEnd_1595733 : Nat := 13487704119195233267471

theorem tailTrace_1595733 : CollatzResearch.WordTrace tailWord_1595733 prefixEnd_1595733 13487704119195233267471 := by
  unfold tailWord_1595733
  simp only [CollatzResearch.WordTrace]
  refine ⟨58201163927939345344327853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38800775951959563562885235 58201163927939345344327853)
  ·
    refine ⟨21825436472977254504122945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58201163927939345344327853 21825436472977254504122945)
    ·
      refine ⟨16369077354732940878092209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21825436472977254504122945 16369077354732940878092209)
      ·
        refine ⟨12276808016049705658569157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16369077354732940878092209 12276808016049705658569157)
        ·
          refine ⟨2301901503009319810981717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12276808016049705658569157 2301901503009319810981717)
          ·
            refine ⟨13487704119195233267471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2301901503009319810981717 13487704119195233267471)
            ·
              rfl

theorem cell21_1595733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 9].length) (baseStart_1595733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595733 prefixEnd_1595733 := by exact prefixLift 1595733
  have htrace : WordTrace (prefixWord ++ tailWord_1595733) baseStart_1595733 baseEnd_1595733 := by
    simpa [prefixWord, tailWord_1595733, baseEnd_1595733] using wordTrace_append hprefix tailTrace_1595733
  have hstable : (prefixWord ++ tailWord_1595733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595733).length < 2 ^ (prefixWord ++ tailWord_1595733).sum := by decide
  have hdescent : baseEnd_1595733 < baseStart_1595733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595742 : List Nat := [4, 4, 2, 1, 1, 2, 1, 6]
def baseStart_1595742 : Nat := 118140960795 + 1595742 * 2 ^ 59
def prefixEnd_1595742 : Nat := 4983230072969 + 3 ^ 40 * 1595742 * 2
def baseEnd_1595742 : Nat := 121390021713629760857233

theorem tailTrace_1595742 : CollatzResearch.WordTrace tailWord_1595742 prefixEnd_1595742 121390021713629760857233 := by
  unfold tailWord_1595742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7275186523113342485175685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38800994789937826587603653 7275186523113342485175685)
  ·
    refine ⟨1364097473083751715970441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7275186523113342485175685 1364097473083751715970441)
    ·
      refine ⟨1023073104812813786977831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1364097473083751715970441 1023073104812813786977831)
      ·
        refine ⟨1534609657219220680466747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023073104812813786977831 1534609657219220680466747)
        ·
          refine ⟨2301914485828831020700121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534609657219220680466747 2301914485828831020700121)
          ·
            refine ⟨1726435864371623265525091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301914485828831020700121 1726435864371623265525091)
            ·
              refine ⟨2589653796557434898287637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726435864371623265525091 2589653796557434898287637)
              ·
                refine ⟨121390021713629760857233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2589653796557434898287637 121390021713629760857233)
                ·
                  rfl

theorem cell21_1595742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_1595742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595742 prefixEnd_1595742 := by exact prefixLift 1595742
  have htrace : WordTrace (prefixWord ++ tailWord_1595742) baseStart_1595742 baseEnd_1595742 := by
    simpa [prefixWord, tailWord_1595742, baseEnd_1595742] using wordTrace_append hprefix tailTrace_1595742
  have hstable : (prefixWord ++ tailWord_1595742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595742).length < 2 ^ (prefixWord ++ tailWord_1595742).sum := by decide
  have hdescent : baseEnd_1595742 < baseStart_1595742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
