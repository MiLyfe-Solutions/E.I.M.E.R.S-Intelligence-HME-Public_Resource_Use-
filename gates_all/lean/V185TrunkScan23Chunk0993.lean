import V185TrunkScan23Chunk0992

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5878690 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_5878690 : Nat := 118140960795 + 5878690 * 2 ^ 59
def prefixEnd_5878690 : Nat := 4983230072969 + 3 ^ 40 * 5878690 * 2
def baseEnd_5878690 : Nat := 3018593588779709832039403

theorem tailTrace_5878690 : CollatzResearch.WordTrace tailWord_5878690 prefixEnd_5878690 3018593588779709832039403 := by
  unfold tailWord_5878690
  simp only [CollatzResearch.WordTrace]
  refine ⟨53603359768129401291140381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142942292715011736776374349 53603359768129401291140381)
  ·
    refine ⟨20101259913048525484177643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53603359768129401291140381 20101259913048525484177643)
    ·
      refine ⟨30151889869572788226266465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20101259913048525484177643 30151889869572788226266465)
      ·
        refine ⟨22613917402179591169699849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30151889869572788226266465 22613917402179591169699849)
        ·
          refine ⟨16960438051634693377274887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22613917402179591169699849 16960438051634693377274887)
          ·
            refine ⟨25440657077452040065912331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16960438051634693377274887 25440657077452040065912331)
            ·
              refine ⟨38160985616178060098868497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25440657077452040065912331 38160985616178060098868497)
              ·
                refine ⟨28620739212133545074151373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38160985616178060098868497 28620739212133545074151373)
                ·
                  refine ⟨10732777204550079402806765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28620739212133545074151373 10732777204550079402806765)
                  ·
                    refine ⟨4024791451706279776052537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10732777204550079402806765 4024791451706279776052537)
                    ·
                      refine ⟨3018593588779709832039403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024791451706279776052537 3018593588779709832039403)
                      ·
                        rfl

theorem cell23_5878690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_5878690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878690 prefixEnd_5878690 := by exact prefixLift 5878690
  have htrace : WordTrace (prefixWord ++ tailWord_5878690) baseStart_5878690 baseEnd_5878690 := by
    simpa [prefixWord, tailWord_5878690, baseEnd_5878690] using wordTrace_append hprefix tailTrace_5878690
  have hstable : (prefixWord ++ tailWord_5878690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878690).length < 2 ^ (prefixWord ++ tailWord_5878690).sum := by decide
  have hdescent : baseEnd_5878690 < baseStart_5878690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878699 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 6]
def baseStart_5878699 : Nat := 118140960795 + 5878699 * 2 ^ 59
def prefixEnd_5878699 : Nat := 4983230072969 + 3 ^ 40 * 5878699 * 2
def baseEnd_5878699 : Nat := 3018598210105600296826861

theorem tailTrace_5878699 : CollatzResearch.WordTrace tailWord_5878699 prefixEnd_5878699 3018598210105600296826861 := by
  unfold tailWord_5878699
  simp only [CollatzResearch.WordTrace]
  refine ⟨214413767329484999701639151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142942511552989999801092767 214413767329484999701639151)
  ·
    refine ⟨321620650994227499552458727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214413767329484999701639151 321620650994227499552458727)
    ·
      refine ⟨482430976491341249328688091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321620650994227499552458727 482430976491341249328688091)
      ·
        refine ⟨723646464737011873993032137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482430976491341249328688091 723646464737011873993032137)
        ·
          refine ⟨542734848552758905494774103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723646464737011873993032137 542734848552758905494774103)
          ·
            refine ⟨814102272829138358242161155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542734848552758905494774103 814102272829138358242161155)
            ·
              refine ⟨1221153409243707537363241733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814102272829138358242161155 1221153409243707537363241733)
              ·
                refine ⟨228966264233195163255607825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1221153409243707537363241733 228966264233195163255607825)
                ·
                  refine ⟨171724698174896372441705869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228966264233195163255607825 171724698174896372441705869)
                  ·
                    refine ⟨64396761815586139665639701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171724698174896372441705869 64396761815586139665639701)
                    ·
                      refine ⟨3018598210105600296826861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64396761815586139665639701 3018598210105600296826861)
                      ·
                        rfl

theorem cell23_5878699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_5878699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878699 prefixEnd_5878699 := by exact prefixLift 5878699
  have htrace : WordTrace (prefixWord ++ tailWord_5878699) baseStart_5878699 baseEnd_5878699 := by
    simpa [prefixWord, tailWord_5878699, baseEnd_5878699] using wordTrace_append hprefix tailTrace_5878699
  have hstable : (prefixWord ++ tailWord_5878699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878699).length < 2 ^ (prefixWord ++ tailWord_5878699).sum := by decide
  have hdescent : baseEnd_5878699 < baseStart_5878699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878724 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5878724 : Nat := 118140960795 + 5878724 * 2 ^ 59
def prefixEnd_5878724 : Nat := 4983230072969 + 3 ^ 40 * 5878724 * 2
def baseEnd_5878724 : Nat := 3018611047121962699014247

theorem tailTrace_5878724 : CollatzResearch.WordTrace tailWord_5878724 prefixEnd_5878724 3018611047121962699014247 := by
  unfold tailWord_5878724
  simp only [CollatzResearch.WordTrace]
  refine ⟨107207339577197214485649613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142943119436262952647532817 107207339577197214485649613)
  ·
    refine ⟨40202752341448955432118605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107207339577197214485649613 40202752341448955432118605)
    ·
      refine ⟨15076032128043358287044477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40202752341448955432118605 15076032128043358287044477)
      ·
        refine ⟨5653512048016259357641679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15076032128043358287044477 5653512048016259357641679)
        ·
          refine ⟨8480268072024389036462519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5653512048016259357641679 8480268072024389036462519)
          ·
            refine ⟨12720402108036583554693779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8480268072024389036462519 12720402108036583554693779)
            ·
              refine ⟨19080603162054875332040669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12720402108036583554693779 19080603162054875332040669)
              ·
                refine ⟨7155226185770578249515251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19080603162054875332040669 7155226185770578249515251)
                ·
                  refine ⟨10732839278655867374272877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7155226185770578249515251 10732839278655867374272877)
                  ·
                    refine ⟨4024814729495950265352329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10732839278655867374272877 4024814729495950265352329)
                    ·
                      refine ⟨3018611047121962699014247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024814729495950265352329 3018611047121962699014247)
                      ·
                        rfl

theorem cell23_5878724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5878724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878724 prefixEnd_5878724 := by exact prefixLift 5878724
  have htrace : WordTrace (prefixWord ++ tailWord_5878724) baseStart_5878724 baseEnd_5878724 := by
    simpa [prefixWord, tailWord_5878724, baseEnd_5878724] using wordTrace_append hprefix tailTrace_5878724
  have hstable : (prefixWord ++ tailWord_5878724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878724).length < 2 ^ (prefixWord ++ tailWord_5878724).sum := by decide
  have hdescent : baseEnd_5878724 < baseStart_5878724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878754 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_5878754 : Nat := 118140960795 + 5878754 * 2 ^ 59
def prefixEnd_5878754 : Nat := 4983230072969 + 3 ^ 40 * 5878754 * 2
def baseEnd_5878754 : Nat := 3018626451541597581639109

theorem tailTrace_5878754 : CollatzResearch.WordTrace tailWord_5878754 prefixEnd_5878754 3018626451541597581639109 := by
  unfold tailWord_5878754
  simp only [CollatzResearch.WordTrace]
  refine ⟨53603943336071436023722829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142943848896190496063260877 53603943336071436023722829)
  ·
    refine ⟨20101478751026788508896061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53603943336071436023722829 20101478751026788508896061)
    ·
      refine ⟨7538054531635045690836023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20101478751026788508896061 7538054531635045690836023)
      ·
        refine ⟨11307081797452568536254035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7538054531635045690836023 11307081797452568536254035)
        ·
          refine ⟨16960622696178852804381053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11307081797452568536254035 16960622696178852804381053)
          ·
            refine ⟨6360233511067069801642895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16960622696178852804381053 6360233511067069801642895)
            ·
              refine ⟨9540350266600604702464343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6360233511067069801642895 9540350266600604702464343)
              ·
                refine ⟨14310525399900907053696515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9540350266600604702464343 14310525399900907053696515)
                ·
                  refine ⟨21465788099851360580544773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14310525399900907053696515 21465788099851360580544773)
                  ·
                    refine ⟨4024835268722130108852145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21465788099851360580544773 4024835268722130108852145)
                    ·
                      refine ⟨3018626451541597581639109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024835268722130108852145 3018626451541597581639109)
                      ·
                        rfl

theorem cell23_5878754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_5878754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878754 prefixEnd_5878754 := by exact prefixLift 5878754
  have htrace : WordTrace (prefixWord ++ tailWord_5878754) baseStart_5878754 baseEnd_5878754 := by
    simpa [prefixWord, tailWord_5878754, baseEnd_5878754] using wordTrace_append hprefix tailTrace_5878754
  have hstable : (prefixWord ++ tailWord_5878754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878754).length < 2 ^ (prefixWord ++ tailWord_5878754).sum := by decide
  have hdescent : baseEnd_5878754 < baseStart_5878754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878756 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_5878756 : Nat := 118140960795 + 5878756 * 2 ^ 59
def prefixEnd_5878756 : Nat := 4983230072969 + 3 ^ 40 * 5878756 * 2
def baseEnd_5878756 : Nat := 1006209159500968857938033

theorem tailTrace_5878756 : CollatzResearch.WordTrace tailWord_5878756 prefixEnd_5878756 1006209159500968857938033 := by
  unfold tailWord_5878756
  simp only [CollatzResearch.WordTrace]
  refine ⟨107207923145139249218232061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142943897526852332290976081 107207923145139249218232061)
  ·
    refine ⟨40202971179427218456837023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107207923145139249218232061 40202971179427218456837023)
    ·
      refine ⟨60304456769140827685255535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40202971179427218456837023 60304456769140827685255535)
      ·
        refine ⟨90456685153711241527883303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60304456769140827685255535 90456685153711241527883303)
        ·
          refine ⟨135685027730566862291824955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90456685153711241527883303 135685027730566862291824955)
          ·
            refine ⟨203527541595850293437737433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135685027730566862291824955 203527541595850293437737433)
            ·
              refine ⟨152645656196887720078303075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203527541595850293437737433 152645656196887720078303075)
              ·
                refine ⟨228968484295331580117454613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152645656196887720078303075 228968484295331580117454613)
                ·
                  refine ⟨10732897701343667818005685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 228968484295331580117454613 10732897701343667818005685)
                  ·
                    refine ⟨1006209159500968857938033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10732897701343667818005685 1006209159500968857938033)
                    ·
                      rfl

theorem cell23_5878756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_5878756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878756 prefixEnd_5878756 := by exact prefixLift 5878756
  have htrace : WordTrace (prefixWord ++ tailWord_5878756) baseStart_5878756 baseEnd_5878756 := by
    simpa [prefixWord, tailWord_5878756, baseEnd_5878756] using wordTrace_append hprefix tailTrace_5878756
  have hstable : (prefixWord ++ tailWord_5878756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878756).length < 2 ^ (prefixWord ++ tailWord_5878756).sum := by decide
  have hdescent : baseEnd_5878756 < baseStart_5878756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878793 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 4, 4, 2]
def baseStart_5878793 : Nat := 118140960795 + 5878793 * 2 ^ 59
def prefixEnd_5878793 : Nat := 4983230072969 + 3 ^ 40 * 5878793 * 2
def baseEnd_5878793 : Nat := 3018646477287122929051429

theorem tailTrace_5878793 : CollatzResearch.WordTrace tailWord_5878793 prefixEnd_5878793 3018646477287122929051429 := by
  unfold tailWord_5878793
  simp only [CollatzResearch.WordTrace]
  refine ⟨214417195791144453755561033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142944797194096302503707355 214417195791144453755561033)
  ·
    refine ⟨160812896843358340316670775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214417195791144453755561033 160812896843358340316670775)
    ·
      refine ⟨241219345265037510475006163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160812896843358340316670775 241219345265037510475006163)
      ·
        refine ⟨361829017897556265712509245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241219345265037510475006163 361829017897556265712509245)
        ·
          refine ⟨135685881711583599642190967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361829017897556265712509245 135685881711583599642190967)
          ·
            refine ⟨203528822567375399463286451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135685881711583599642190967 203528822567375399463286451)
            ·
              refine ⟨305293233851063099194929677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203528822567375399463286451 305293233851063099194929677)
              ·
                refine ⟨114484962694148662198098629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305293233851063099194929677 114484962694148662198098629)
                ·
                  refine ⟨21465930505152874162143493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114484962694148662198098629 21465930505152874162143493)
                  ·
                    refine ⟨4024861969716163905401905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21465930505152874162143493 4024861969716163905401905)
                    ·
                      refine ⟨3018646477287122929051429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024861969716163905401905 3018646477287122929051429)
                      ·
                        rfl

theorem cell23_5878793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 4, 2].length) (baseStart_5878793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878793 prefixEnd_5878793 := by exact prefixLift 5878793
  have htrace : WordTrace (prefixWord ++ tailWord_5878793) baseStart_5878793 baseEnd_5878793 := by
    simpa [prefixWord, tailWord_5878793, baseEnd_5878793] using wordTrace_append hprefix tailTrace_5878793
  have hstable : (prefixWord ++ tailWord_5878793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878793).length < 2 ^ (prefixWord ++ tailWord_5878793).sum := by decide
  have hdescent : baseEnd_5878793 < baseStart_5878793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878860 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 3, 1, 3]
def baseStart_5878860 : Nat := 118140960795 + 5878860 * 2 ^ 59
def prefixEnd_5878860 : Nat := 4983230072969 + 3 ^ 40 * 5878860 * 2
def baseEnd_5878860 : Nat := 3018680880490974166913621

theorem tailTrace_5878860 : CollatzResearch.WordTrace tailWord_5878860 prefixEnd_5878860 3018680880490974166913621 := by
  unfold tailWord_5878860
  simp only [CollatzResearch.WordTrace]
  refine ⟨107209819740950862099125017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142946426321267816132166689 107209819740950862099125017)
  ·
    refine ⟨80407364805713146574343763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107209819740950862099125017 80407364805713146574343763)
    ·
      refine ⟨120611047208569719861515645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80407364805713146574343763 120611047208569719861515645)
      ·
        refine ⟨45229142703213644948068367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120611047208569719861515645 45229142703213644948068367)
        ·
          refine ⟨67843714054820467422102551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45229142703213644948068367 67843714054820467422102551)
          ·
            refine ⟨101765571082230701133153827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67843714054820467422102551 101765571082230701133153827)
            ·
              refine ⟨152648356623346051699730741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101765571082230701133153827 152648356623346051699730741)
              ·
                refine ⟨14310783433438692346849757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152648356623346051699730741 14310783433438692346849757)
                ·
                  refine ⟨5366543787539509630068659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14310783433438692346849757 5366543787539509630068659)
                  ·
                    refine ⟨8049815681309264445102989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5366543787539509630068659 8049815681309264445102989)
                    ·
                      refine ⟨3018680880490974166913621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8049815681309264445102989 3018680880490974166913621)
                      ·
                        rfl

theorem cell23_5878860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_5878860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878860 prefixEnd_5878860 := by exact prefixLift 5878860
  have htrace : WordTrace (prefixWord ++ tailWord_5878860) baseStart_5878860 baseEnd_5878860 := by
    simpa [prefixWord, tailWord_5878860, baseEnd_5878860] using wordTrace_append hprefix tailTrace_5878860
  have hstable : (prefixWord ++ tailWord_5878860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878860).length < 2 ^ (prefixWord ++ tailWord_5878860).sum := by decide
  have hdescent : baseEnd_5878860 < baseStart_5878860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878887 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_5878887 : Nat := 118140960795 + 5878887 * 2 ^ 59
def prefixEnd_5878887 : Nat := 4983230072969 + 3 ^ 40 * 5878887 * 2
def baseEnd_5878887 : Nat := 3018694744468645561275997

theorem tailTrace_5878887 : CollatzResearch.WordTrace tailWord_5878887 prefixEnd_5878887 3018694744468645561275997 := by
  unfold tailWord_5878887
  simp only [CollatzResearch.WordTrace]
  refine ⟨214420624252803907809482915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142947082835202605206321943 214420624252803907809482915)
  ·
    refine ⟨321630936379205861714224373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214420624252803907809482915 321630936379205861714224373)
    ·
      refine ⟨30152900285550549535708535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321630936379205861714224373 30152900285550549535708535)
      ·
        refine ⟨45229350428325824303562803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30152900285550549535708535 45229350428325824303562803)
        ·
          refine ⟨67844025642488736455344205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45229350428325824303562803 67844025642488736455344205)
          ·
            refine ⟨25441509615933276170754077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67844025642488736455344205 25441509615933276170754077)
            ·
              refine ⟨9540566105974978564032779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25441509615933276170754077 9540566105974978564032779)
              ·
                refine ⟨14310849158962467846049169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9540566105974978564032779 14310849158962467846049169)
                ·
                  refine ⟨10733136869221850884536877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14310849158962467846049169 10733136869221850884536877)
                  ·
                    refine ⟨4024926325958194081701329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10733136869221850884536877 4024926325958194081701329)
                    ·
                      refine ⟨3018694744468645561275997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024926325958194081701329 3018694744468645561275997)
                      ·
                        rfl

theorem cell23_5878887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_5878887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878887 prefixEnd_5878887 := by exact prefixLift 5878887
  have htrace : WordTrace (prefixWord ++ tailWord_5878887) baseStart_5878887 baseEnd_5878887 := by
    simpa [prefixWord, tailWord_5878887, baseEnd_5878887] using wordTrace_append hprefix tailTrace_5878887
  have hstable : (prefixWord ++ tailWord_5878887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878887).length < 2 ^ (prefixWord ++ tailWord_5878887).sum := by decide
  have hdescent : baseEnd_5878887 < baseStart_5878887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878894 : List Nat := [4, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_5878894 : Nat := 118140960795 + 5878894 * 2 ^ 59
def prefixEnd_5878894 : Nat := 4983230072969 + 3 ^ 40 * 5878894 * 2
def baseEnd_5878894 : Nat := 3018698338833227033888465

theorem tailTrace_5878894 : CollatzResearch.WordTrace tailWord_5878894 prefixEnd_5878894 3018698338833227033888465 := by
  unfold tailWord_5878894
  simp only [CollatzResearch.WordTrace]
  refine ⟨26802609945472318500623467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142947253042519032003325157 26802609945472318500623467)
  ·
    refine ⟨40203914918208477750935201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26802609945472318500623467 40203914918208477750935201)
    ·
      refine ⟨30152936188656358313201401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40203914918208477750935201 30152936188656358313201401)
      ·
        refine ⟨22614702141492268734901051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30152936188656358313201401 22614702141492268734901051)
        ·
          refine ⟨33922053212238403102351577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22614702141492268734901051 33922053212238403102351577)
          ·
            refine ⟨25441539909178802326763683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33922053212238403102351577 25441539909178802326763683)
            ·
              refine ⟨38162309863768203490145525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25441539909178802326763683 38162309863768203490145525)
              ·
                refine ⟨3577716549728269077201143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38162309863768203490145525 3577716549728269077201143)
                ·
                  refine ⟨5366574824592403615801715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3577716549728269077201143 5366574824592403615801715)
                  ·
                    refine ⟨8049862236888605423702573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5366574824592403615801715 8049862236888605423702573)
                    ·
                      refine ⟨3018698338833227033888465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8049862236888605423702573 3018698338833227033888465)
                      ·
                        rfl

theorem cell23_5878894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_5878894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878894 prefixEnd_5878894 := by exact prefixLift 5878894
  have htrace : WordTrace (prefixWord ++ tailWord_5878894) baseStart_5878894 baseEnd_5878894 := by
    simpa [prefixWord, tailWord_5878894, baseEnd_5878894] using wordTrace_append hprefix tailTrace_5878894
  have hstable : (prefixWord ++ tailWord_5878894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878894).length < 2 ^ (prefixWord ++ tailWord_5878894).sum := by decide
  have hdescent : baseEnd_5878894 < baseStart_5878894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878903 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_5878903 : Nat := 118140960795 + 5878903 * 2 ^ 59
def prefixEnd_5878903 : Nat := 4983230072969 + 3 ^ 40 * 5878903 * 2
def baseEnd_5878903 : Nat := 3018702960159117498675923

theorem tailTrace_5878903 : CollatzResearch.WordTrace tailWord_5878903 prefixEnd_5878903 3018702960159117498675923 := by
  unfold tailWord_5878903
  simp only [CollatzResearch.WordTrace]
  refine ⟨214421207820745942542065363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142947471880497295028043575 214421207820745942542065363)
  ·
    refine ⟨321631811731118913813098045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214421207820745942542065363 321631811731118913813098045)
    ·
      refine ⟨120611929399169592679911767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321631811731118913813098045 120611929399169592679911767)
      ·
        refine ⟨180917894098754389019867651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120611929399169592679911767 180917894098754389019867651)
        ·
          refine ⟨271376841148131583529801477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180917894098754389019867651 271376841148131583529801477)
          ·
            refine ⟨50883157715274671911837777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271376841148131583529801477 50883157715274671911837777)
            ·
              refine ⟨38162368286456003933878333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50883157715274671911837777 38162368286456003933878333)
              ·
                refine ⟨14310888107421001475204375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38162368286456003933878333 14310888107421001475204375)
                ·
                  refine ⟨21466332161131502212806563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14310888107421001475204375 21466332161131502212806563)
                  ·
                    refine ⟨32199498241697253319209845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21466332161131502212806563 32199498241697253319209845)
                    ·
                      refine ⟨3018702960159117498675923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32199498241697253319209845 3018702960159117498675923)
                      ·
                        rfl

theorem cell23_5878903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_5878903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878903 prefixEnd_5878903 := by exact prefixLift 5878903
  have htrace : WordTrace (prefixWord ++ tailWord_5878903) baseStart_5878903 baseEnd_5878903 := by
    simpa [prefixWord, tailWord_5878903, baseEnd_5878903] using wordTrace_append hprefix tailTrace_5878903
  have hstable : (prefixWord ++ tailWord_5878903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878903).length < 2 ^ (prefixWord ++ tailWord_5878903).sum := by decide
  have hdescent : baseEnd_5878903 < baseStart_5878903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878930 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5878930 : Nat := 118140960795 + 5878930 * 2 ^ 59
def prefixEnd_5878930 : Nat := 4983230072969 + 3 ^ 40 * 5878930 * 2
def baseEnd_5878930 : Nat := 3018716824136788893038299

theorem tailTrace_5878930 : CollatzResearch.WordTrace tailWord_5878930 prefixEnd_5878930 3018716824136788893038299 := by
  unfold tailWord_5878930
  simp only [CollatzResearch.WordTrace]
  refine ⟨53605548147912031538324561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142948128394432084102198829 53605548147912031538324561)
  ·
    refine ⟨40204161110934023653743421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53605548147912031538324561 40204161110934023653743421)
    ·
      refine ⟨15076560416600258870153783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40204161110934023653743421 15076560416600258870153783)
      ·
        refine ⟨22614840624900388305230675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15076560416600258870153783 22614840624900388305230675)
        ·
          refine ⟨33922260937350582457846013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22614840624900388305230675 33922260937350582457846013)
          ·
            refine ⟨12720847851506468421692255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33922260937350582457846013 12720847851506468421692255)
            ·
              refine ⟨19081271777259702632538383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12720847851506468421692255 19081271777259702632538383)
              ·
                refine ⟨28621907665889553948807575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19081271777259702632538383 28621907665889553948807575)
                ·
                  refine ⟨42932861498834330923211363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28621907665889553948807575 42932861498834330923211363)
                  ·
                    refine ⟨64399292248251496384817045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42932861498834330923211363 64399292248251496384817045)
                    ·
                      refine ⟨3018716824136788893038299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64399292248251496384817045 3018716824136788893038299)
                      ·
                        rfl

theorem cell23_5878930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5878930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878930 prefixEnd_5878930 := by exact prefixLift 5878930
  have htrace : WordTrace (prefixWord ++ tailWord_5878930) baseStart_5878930 baseEnd_5878930 := by
    simpa [prefixWord, tailWord_5878930, baseEnd_5878930] using wordTrace_append hprefix tailTrace_5878930
  have hstable : (prefixWord ++ tailWord_5878930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878930).length < 2 ^ (prefixWord ++ tailWord_5878930).sum := by decide
  have hdescent : baseEnd_5878930 < baseStart_5878930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878940 : List Nat := [2, 2, 3, 2, 1, 2, 4, 7]
def baseStart_5878940 : Nat := 118140960795 + 5878940 * 2 ^ 59
def prefixEnd_5878940 : Nat := 4983230072969 + 3 ^ 40 * 5878940 * 2
def baseEnd_5878940 : Nat := 111804516997901253848639

theorem tailTrace_5878940 : CollatzResearch.WordTrace tailWord_5878940 prefixEnd_5878940 111804516997901253848639 := by
  unfold tailWord_5878940
  simp only [CollatzResearch.WordTrace]
  refine ⟨107211278660805948930581137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142948371547741265240774849 107211278660805948930581137)
  ·
    refine ⟨80408458995604461697935853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107211278660805948930581137 80408458995604461697935853)
    ·
      refine ⟨30153172123351673136725945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80408458995604461697935853 30153172123351673136725945)
      ·
        refine ⟨22614879092513754852544459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30153172123351673136725945 22614879092513754852544459)
        ·
          refine ⟨33922318638770632278816689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22614879092513754852544459 33922318638770632278816689)
          ·
            refine ⟨25441738979077974209112517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33922318638770632278816689 25441738979077974209112517)
            ·
              refine ⟨4770326058577120164208597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25441738979077974209112517 4770326058577120164208597)
              ·
                refine ⟨111804516997901253848639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4770326058577120164208597 111804516997901253848639)
                ·
                  rfl

theorem cell23_5878940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 7].length) (baseStart_5878940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878940 prefixEnd_5878940 := by exact prefixLift 5878940
  have htrace : WordTrace (prefixWord ++ tailWord_5878940) baseStart_5878940 baseEnd_5878940 := by
    simpa [prefixWord, tailWord_5878940, baseEnd_5878940] using wordTrace_append hprefix tailTrace_5878940
  have hstable : (prefixWord ++ tailWord_5878940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878940).length < 2 ^ (prefixWord ++ tailWord_5878940).sum := by decide
  have hdescent : baseEnd_5878940 < baseStart_5878940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878954 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5878954 : Nat := 118140960795 + 5878954 * 2 ^ 59
def prefixEnd_5878954 : Nat := 4983230072969 + 3 ^ 40 * 5878954 * 2
def baseEnd_5878954 : Nat := 3018729147672496799138189

theorem tailTrace_5878954 : CollatzResearch.WordTrace tailWord_5878954 prefixEnd_5878954 3018729147672496799138189 := by
  unfold tailWord_5878954
  simp only [CollatzResearch.WordTrace]
  refine ⟨53605766985890294563042979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142948711962374118834781277 53605766985890294563042979)
  ·
    refine ⟨80408650478835441844564469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53605766985890294563042979 80408650478835441844564469)
    ·
      refine ⟨7538310982390822672927919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80408650478835441844564469 7538310982390822672927919)
      ·
        refine ⟨11307466473586234009391879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7538310982390822672927919 11307466473586234009391879)
        ·
          refine ⟨16961199710379351014087819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11307466473586234009391879 16961199710379351014087819)
          ·
            refine ⟨25441799565569026521131729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16961199710379351014087819 25441799565569026521131729)
            ·
              refine ⟨19081349674176769890848797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25441799565569026521131729 19081349674176769890848797)
              ·
                refine ⟨7155506127816288709068299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19081349674176769890848797 7155506127816288709068299)
                ·
                  refine ⟨10733259191724433063602449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7155506127816288709068299 10733259191724433063602449)
                  ·
                    refine ⟨8049944393793324797701837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10733259191724433063602449 8049944393793324797701837)
                    ·
                      refine ⟨3018729147672496799138189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8049944393793324797701837 3018729147672496799138189)
                      ·
                        rfl

theorem cell23_5878954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5878954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878954 prefixEnd_5878954 := by exact prefixLift 5878954
  have htrace : WordTrace (prefixWord ++ tailWord_5878954) baseStart_5878954 baseEnd_5878954 := by
    simpa [prefixWord, tailWord_5878954, baseEnd_5878954] using wordTrace_append hprefix tailTrace_5878954
  have hstable : (prefixWord ++ tailWord_5878954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878954).length < 2 ^ (prefixWord ++ tailWord_5878954).sum := by decide
  have hdescent : baseEnd_5878954 < baseStart_5878954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878957 : List Nat := [1, 5, 2, 1, 4, 1, 9]
def baseStart_5878957 : Nat := 118140960795 + 5878957 * 2 ^ 59
def prefixEnd_5878957 : Nat := 4983230072969 + 3 ^ 40 * 5878957 * 2
def baseEnd_5878957 : Nat := 37268280100178522066675

theorem tailTrace_5878957 : CollatzResearch.WordTrace tailWord_5878957 prefixEnd_5878957 37268280100178522066675 := by
  unfold tailWord_5878957
  simp only [CollatzResearch.WordTrace]
  refine ⟨214423177362550309764531125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142948784908366873176354083 214423177362550309764531125)
  ·
    refine ⟨20102172877739091540424793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214423177362550309764531125 20102172877739091540424793)
    ·
      refine ⟨15076629658304318655318595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20102172877739091540424793 15076629658304318655318595)
      ·
        refine ⟨22614944487456477982977893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15076629658304318655318595 22614944487456477982977893)
        ·
          refine ⟨4240302091398089621808355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22614944487456477982977893 4240302091398089621808355)
          ·
            refine ⟨6360453137097134432712533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240302091398089621808355 6360453137097134432712533)
            ·
              refine ⟨37268280100178522066675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6360453137097134432712533 37268280100178522066675)
              ·
                rfl

theorem cell23_5878957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 9].length) (baseStart_5878957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878957 prefixEnd_5878957 := by exact prefixLift 5878957
  have htrace : WordTrace (prefixWord ++ tailWord_5878957) baseStart_5878957 baseEnd_5878957 := by
    simpa [prefixWord, tailWord_5878957, baseEnd_5878957] using wordTrace_append hprefix tailTrace_5878957
  have hstable : (prefixWord ++ tailWord_5878957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878957).length < 2 ^ (prefixWord ++ tailWord_5878957).sum := by decide
  have hdescent : baseEnd_5878957 < baseStart_5878957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878967 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 3]
def baseStart_5878967 : Nat := 118140960795 + 5878967 * 2 ^ 59
def prefixEnd_5878967 : Nat := 4983230072969 + 3 ^ 40 * 5878967 * 2
def baseEnd_5878967 : Nat := 3018735822921005248275629

theorem tailTrace_5878967 : CollatzResearch.WordTrace tailWord_5878967 prefixEnd_5878967 3018735822921005248275629 := by
  unfold tailWord_5878967
  simp only [CollatzResearch.WordTrace]
  refine ⟨214423542092514081472395155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142949028061676054314930103 214423542092514081472395155)
  ·
    refine ⟨321635313138771122208592733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214423542092514081472395155 321635313138771122208592733)
    ·
      refine ⟨120613242427039170828222275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321635313138771122208592733 120613242427039170828222275)
      ·
        refine ⟨180919863640558756242333413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120613242427039170828222275 180919863640558756242333413)
        ·
          refine ⟨33922474432604766795437515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180919863640558756242333413 33922474432604766795437515)
          ·
            refine ⟨50883711648907150193156273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33922474432604766795437515 50883711648907150193156273)
            ·
              refine ⟨38162783736680362644867205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50883711648907150193156273 38162783736680362644867205)
              ·
                refine ⟨7155521950627567995912601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38162783736680362644867205 7155521950627567995912601)
                ·
                  refine ⟨5366641462970675996934451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7155521950627567995912601 5366641462970675996934451)
                  ·
                    refine ⟨8049962194456013995401677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5366641462970675996934451 8049962194456013995401677)
                    ·
                      refine ⟨3018735822921005248275629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8049962194456013995401677 3018735822921005248275629)
                      ·
                        rfl

theorem cell23_5878967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_5878967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878967 prefixEnd_5878967 := by exact prefixLift 5878967
  have htrace : WordTrace (prefixWord ++ tailWord_5878967) baseStart_5878967 baseEnd_5878967 := by
    simpa [prefixWord, tailWord_5878967, baseEnd_5878967] using wordTrace_append hprefix tailTrace_5878967
  have hstable : (prefixWord ++ tailWord_5878967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878967).length < 2 ^ (prefixWord ++ tailWord_5878967).sum := by decide
  have hdescent : baseEnd_5878967 < baseStart_5878967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878983 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 2, 6]
def baseStart_5878983 : Nat := 118140960795 + 5878983 * 2 ^ 59
def prefixEnd_5878983 : Nat := 4983230072969 + 3 ^ 40 * 5878983 * 2
def baseEnd_5878983 : Nat := 1006248012870492395225185

theorem tailTrace_5878983 : CollatzResearch.WordTrace tailWord_5878983 prefixEnd_5878983 1006248012870492395225185 := by
  unfold tailWord_5878983
  simp only [CollatzResearch.WordTrace]
  refine ⟨214424125660456116204977603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142949417106970744136651735 214424125660456116204977603)
  ·
    refine ⟨321636188490684174307466405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214424125660456116204977603 321636188490684174307466405)
    ·
      refine ⟨60306785342003282682649951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321636188490684174307466405 60306785342003282682649951)
      ·
        refine ⟨90460178013004924023974927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60306785342003282682649951 90460178013004924023974927)
        ·
          refine ⟨135690267019507386035962391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90460178013004924023974927 135690267019507386035962391)
          ·
            refine ⟨203535400529261079053943587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135690267019507386035962391 203535400529261079053943587)
            ·
              refine ⟨305303100793891618580915381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203535400529261079053943587 305303100793891618580915381)
              ·
                refine ⟨28622165699427339241960817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 305303100793891618580915381 28622165699427339241960817)
                ·
                  refine ⟨21466624274570504431470613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28622165699427339241960817 21466624274570504431470613)
                  ·
                    refine ⟨1006248012870492395225185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21466624274570504431470613 1006248012870492395225185)
                    ·
                      rfl

theorem cell23_5878983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_5878983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878983 prefixEnd_5878983 := by exact prefixLift 5878983
  have htrace : WordTrace (prefixWord ++ tailWord_5878983) baseStart_5878983 baseEnd_5878983 := by
    simpa [prefixWord, tailWord_5878983, baseEnd_5878983] using wordTrace_append hprefix tailTrace_5878983
  have hstable : (prefixWord ++ tailWord_5878983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878983).length < 2 ^ (prefixWord ++ tailWord_5878983).sum := by decide
  have hdescent : baseEnd_5878983 < baseStart_5878983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878984 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_5878984 : Nat := 118140960795 + 5878984 * 2 ^ 59
def prefixEnd_5878984 : Nat := 4983230072969 + 3 ^ 40 * 5878984 * 2
def baseEnd_5878984 : Nat := 3018744552092131681763051

theorem tailTrace_5878984 : CollatzResearch.WordTrace tailWord_5878984 prefixEnd_5878984 3018744552092131681763051 := by
  unfold tailWord_5878984
  simp only [CollatzResearch.WordTrace]
  refine ⟨107212081066726246687882003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142949441422301662250509337 107212081066726246687882003)
  ·
    refine ⟨160818121600089370031823005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107212081066726246687882003 160818121600089370031823005)
    ·
      refine ⟨60306795600033513761933627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160818121600089370031823005 60306795600033513761933627)
      ·
        refine ⟨90460193400050270642900441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60306795600033513761933627 90460193400050270642900441)
        ·
          refine ⟨67845145050037702982175331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90460193400050270642900441 67845145050037702982175331)
          ·
            refine ⟨101767717575056554473262997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67845145050037702982175331 101767717575056554473262997)
            ·
              refine ⟨4770361761330775990934203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101767717575056554473262997 4770361761330775990934203)
              ·
                refine ⟨7155542641996163986401305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4770361761330775990934203 7155542641996163986401305)
                ·
                  refine ⟨5366656981497122989800979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7155542641996163986401305 5366656981497122989800979)
                  ·
                    refine ⟨8049985472245684484701469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5366656981497122989800979 8049985472245684484701469)
                    ·
                      refine ⟨3018744552092131681763051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8049985472245684484701469 3018744552092131681763051)
                      ·
                        rfl

theorem cell23_5878984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_5878984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878984 prefixEnd_5878984 := by exact prefixLift 5878984
  have htrace : WordTrace (prefixWord ++ tailWord_5878984) baseStart_5878984 baseEnd_5878984 := by
    simpa [prefixWord, tailWord_5878984, baseEnd_5878984] using wordTrace_append hprefix tailTrace_5878984
  have hstable : (prefixWord ++ tailWord_5878984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878984).length < 2 ^ (prefixWord ++ tailWord_5878984).sum := by decide
  have hdescent : baseEnd_5878984 < baseStart_5878984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879007 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 6, 2, 2]
def baseStart_5879007 : Nat := 118140960795 + 5879007 * 2 ^ 59
def prefixEnd_5879007 : Nat := 4983230072969 + 3 ^ 40 * 5879007 * 2
def baseEnd_5879007 : Nat := 3018756362147185091775445

theorem tailTrace_5879007 : CollatzResearch.WordTrace tailWord_5879007 prefixEnd_5879007 3018756362147185091775445 := by
  unfold tailWord_5879007
  simp only [CollatzResearch.WordTrace]
  refine ⟨214425001012369168303851275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142950000674912778869234183 214425001012369168303851275)
  ·
    refine ⟨321637501518553752455776913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214425001012369168303851275 321637501518553752455776913)
    ·
      refine ⟨241228126138915314341832685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321637501518553752455776913 241228126138915314341832685)
      ·
        refine ⟨90460547302093242878187257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241228126138915314341832685 90460547302093242878187257)
        ·
          refine ⟨67845410476569932158640443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90460547302093242878187257 67845410476569932158640443)
          ·
            refine ⟨101768115714854898237960665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67845410476569932158640443 101768115714854898237960665)
            ·
              refine ⟨76326086786141173678470499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101768115714854898237960665 76326086786141173678470499)
              ·
                refine ⟨114489130179211760517705749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76326086786141173678470499 114489130179211760517705749)
                ·
                  refine ⟨5366677977150551274267457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114489130179211760517705749 5366677977150551274267457)
                  ·
                    refine ⟨4025008482862913455700593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5366677977150551274267457 4025008482862913455700593)
                    ·
                      refine ⟨3018756362147185091775445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025008482862913455700593 3018756362147185091775445)
                      ·
                        rfl

theorem cell23_5879007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_5879007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879007 prefixEnd_5879007 := by exact prefixLift 5879007
  have htrace : WordTrace (prefixWord ++ tailWord_5879007) baseStart_5879007 baseEnd_5879007 := by
    simpa [prefixWord, tailWord_5879007, baseEnd_5879007] using wordTrace_append hprefix tailTrace_5879007
  have hstable : (prefixWord ++ tailWord_5879007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879007).length < 2 ^ (prefixWord ++ tailWord_5879007).sum := by decide
  have hdescent : baseEnd_5879007 < baseStart_5879007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879030 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_5879030 : Nat := 118140960795 + 5879030 * 2 ^ 59
def prefixEnd_5879030 : Nat := 4983230072969 + 3 ^ 40 * 5879030 * 2
def baseEnd_5879030 : Nat := 335418685800248722420871

theorem tailTrace_5879030 : CollatzResearch.WordTrace tailWord_5879030 prefixEnd_5879030 335418685800248722420871 := by
  unfold tailWord_5879030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13401614993205365201996159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142950559927523895487959029 13401614993205365201996159)
  ·
    refine ⟨20102422489808047802994239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13401614993205365201996159 20102422489808047802994239)
    ·
      refine ⟨30153633734712071704491359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20102422489808047802994239 30153633734712071704491359)
      ·
        refine ⟨45230450602068107556737039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30153633734712071704491359 45230450602068107556737039)
        ·
          refine ⟨67845675903102161335105559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45230450602068107556737039 67845675903102161335105559)
          ·
            refine ⟨101768513854653242002658339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67845675903102161335105559 101768513854653242002658339)
            ·
              refine ⟨152652770781979863003987509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101768513854653242002658339 152652770781979863003987509)
              ·
                refine ⟨14311197260810612156623829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152652770781979863003987509 14311197260810612156623829)
                ·
                  refine ⟨335418685800248722420871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14311197260810612156623829 335418685800248722420871)
                  ·
                    rfl

theorem cell23_5879030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_5879030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879030 prefixEnd_5879030 := by exact prefixLift 5879030
  have htrace : WordTrace (prefixWord ++ tailWord_5879030) baseStart_5879030 baseEnd_5879030 := by
    simpa [prefixWord, tailWord_5879030, baseEnd_5879030] using wordTrace_append hprefix tailTrace_5879030
  have hstable : (prefixWord ++ tailWord_5879030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879030).length < 2 ^ (prefixWord ++ tailWord_5879030).sum := by decide
  have hdescent : baseEnd_5879030 < baseStart_5879030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879141 : List Nat := [1, 3, 1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_5879141 : Nat := 118140960795 + 5879141 * 2 ^ 59
def prefixEnd_5879141 : Nat := 4983230072969 + 3 ^ 40 * 5879141 * 2
def baseEnd_5879141 : Nat := 1006275056184962522499943

theorem tailTrace_5879141 : CollatzResearch.WordTrace tailWord_5879141 prefixEnd_5879141 1006275056184962522499943 := by
  unfold tailWord_5879141
  simp only [CollatzResearch.WordTrace]
  refine ⟨214429888393883709189229277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142953258929255806126152851 214429888393883709189229277)
  ·
    refine ⟨80411208147706390945960979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214429888393883709189229277 80411208147706390945960979)
    ·
      refine ⟨120616812221559586418941469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80411208147706390945960979 120616812221559586418941469)
      ·
        refine ⟨45231304583084844907103051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120616812221559586418941469 45231304583084844907103051)
        ·
          refine ⟨67846956874627267360654577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45231304583084844907103051 67846956874627267360654577)
          ·
            refine ⟨50885217655970450520490933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67846956874627267360654577 50885217655970450520490933)
            ·
              refine ⟨4770489155247229736296025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50885217655970450520490933 4770489155247229736296025)
              ·
                refine ⟨3577866866435422302222019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770489155247229736296025 3577866866435422302222019)
                ·
                  refine ⟨5366800299653133453333029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3577866866435422302222019 5366800299653133453333029)
                  ·
                    refine ⟨1006275056184962522499943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5366800299653133453333029 1006275056184962522499943)
                    ·
                      rfl

theorem cell23_5879141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_5879141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879141 prefixEnd_5879141 := by exact prefixLift 5879141
  have htrace : WordTrace (prefixWord ++ tailWord_5879141) baseStart_5879141 baseEnd_5879141 := by
    simpa [prefixWord, tailWord_5879141, baseEnd_5879141] using wordTrace_append hprefix tailTrace_5879141
  have hstable : (prefixWord ++ tailWord_5879141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879141).length < 2 ^ (prefixWord ++ tailWord_5879141).sum := by decide
  have hdescent : baseEnd_5879141 < baseStart_5879141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879207 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_5879207 : Nat := 118140960795 + 5879207 * 2 ^ 59
def prefixEnd_5879207 : Nat := 4983230072969 + 3 ^ 40 * 5879207 * 2
def baseEnd_5879207 : Nat := 3018859058278084309274525

theorem tailTrace_5879207 : CollatzResearch.WordTrace tailWord_5879207 prefixEnd_5879207 3018859058278084309274525 := by
  unfold tailWord_5879207
  simp only [CollatzResearch.WordTrace]
  refine ⟨214432295611644602461131875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142954863741096401640754583 214432295611644602461131875)
  ·
    refine ⟨321648443417466903691697813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214432295611644602461131875 321648443417466903691697813)
    ·
      refine ⟨15077270785193761110548335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 321648443417466903691697813 15077270785193761110548335)
      ·
        refine ⟨22615906177790641665822503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15077270785193761110548335 22615906177790641665822503)
        ·
          refine ⟨33923859266685962498733755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22615906177790641665822503 33923859266685962498733755)
          ·
            refine ⟨50885788900028943748100633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33923859266685962498733755 50885788900028943748100633)
            ·
              refine ⟨38164341675021707811075475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50885788900028943748100633 38164341675021707811075475)
              ·
                refine ⟨57246512512532561716613213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38164341675021707811075475 57246512512532561716613213)
                ·
                  refine ⟨21467442192199710643729955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57246512512532561716613213 21467442192199710643729955)
                  ·
                    refine ⟨32201163288299565965594933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21467442192199710643729955 32201163288299565965594933)
                    ·
                      refine ⟨3018859058278084309274525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32201163288299565965594933 3018859058278084309274525)
                      ·
                        rfl

theorem cell23_5879207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_5879207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879207 prefixEnd_5879207 := by exact prefixLift 5879207
  have htrace : WordTrace (prefixWord ++ tailWord_5879207) baseStart_5879207 baseEnd_5879207 := by
    simpa [prefixWord, tailWord_5879207, baseEnd_5879207] using wordTrace_append hprefix tailTrace_5879207
  have hstable : (prefixWord ++ tailWord_5879207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879207).length < 2 ^ (prefixWord ++ tailWord_5879207).sum := by decide
  have hdescent : baseEnd_5879207 < baseStart_5879207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879221 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_5879221 : Nat := 118140960795 + 5879221 * 2 ^ 59
def prefixEnd_5879221 : Nat := 4983230072969 + 3 ^ 40 * 5879221 * 2
def baseEnd_5879221 : Nat := 3018866247007247254499461

theorem tailTrace_5879221 : CollatzResearch.WordTrace tailWord_5879221 prefixEnd_5879221 3018866247007247254499461 := by
  unfold tailWord_5879221
  simp only [CollatzResearch.WordTrace]
  refine ⟨214432806233593882852141517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142955204155729255234761011 214432806233593882852141517)
  ·
    refine ⟨80412302337597706069553069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214432806233593882852141517 80412302337597706069553069)
    ·
      refine ⟨30154613376599139776082401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80412302337597706069553069 30154613376599139776082401)
      ·
        refine ⟨22615960032449354832061801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30154613376599139776082401 22615960032449354832061801)
        ·
          refine ⟨16961970024337016124046351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22615960032449354832061801 16961970024337016124046351)
          ·
            refine ⟨25442955036505524186069527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16961970024337016124046351 25442955036505524186069527)
            ·
              refine ⟨38164432554758286279104291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25442955036505524186069527 38164432554758286279104291)
              ·
                refine ⟨57246648832137429418656437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38164432554758286279104291 57246648832137429418656437)
                ·
                  refine ⟨5366873328012884007999041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57246648832137429418656437 5366873328012884007999041)
                  ·
                    refine ⟨4025154996009663005999281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5366873328012884007999041 4025154996009663005999281)
                    ·
                      refine ⟨3018866247007247254499461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025154996009663005999281 3018866247007247254499461)
                      ·
                        rfl

theorem cell23_5879221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_5879221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879221 prefixEnd_5879221 := by exact prefixLift 5879221
  have htrace : WordTrace (prefixWord ++ tailWord_5879221) baseStart_5879221 baseEnd_5879221 := by
    simpa [prefixWord, tailWord_5879221, baseEnd_5879221] using wordTrace_append hprefix tailTrace_5879221
  have hstable : (prefixWord ++ tailWord_5879221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879221).length < 2 ^ (prefixWord ++ tailWord_5879221).sum := by decide
  have hdescent : baseEnd_5879221 < baseStart_5879221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879264 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 3, 3, 2]
def baseStart_5879264 : Nat := 118140960795 + 5879264 * 2 ^ 59
def prefixEnd_5879264 : Nat := 4983230072969 + 3 ^ 40 * 5879264 * 2
def baseEnd_5879264 : Nat := 3018888326675390586261763

theorem tailTrace_5879264 : CollatzResearch.WordTrace tailWord_5879264 prefixEnd_5879264 3018888326675390586261763 := by
  unfold tailWord_5879264
  simp only [CollatzResearch.WordTrace]
  refine ⟨107217187286219050597978423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142956249714958734130637897 107217187286219050597978423)
  ·
    refine ⟨160825780929328575896967635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107217187286219050597978423 160825780929328575896967635)
    ·
      refine ⟨241238671393992863845451453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160825780929328575896967635 241238671393992863845451453)
      ·
        refine ⟨90464501772747323942044295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241238671393992863845451453 90464501772747323942044295)
        ·
          refine ⟨135696752659120985913066443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90464501772747323942044295 135696752659120985913066443)
          ·
            refine ⟨203545128988681478869599665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135696752659120985913066443 203545128988681478869599665)
            ·
              refine ⟨152658846741511109152199749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203545128988681478869599665 152658846741511109152199749)
              ·
                refine ⟨28623533764033332966037453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152658846741511109152199749 28623533764033332966037453)
                ·
                  refine ⟨10733825161512499862264045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28623533764033332966037453 10733825161512499862264045)
                  ·
                    refine ⟨4025184435567187448349017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10733825161512499862264045 4025184435567187448349017)
                    ·
                      refine ⟨3018888326675390586261763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025184435567187448349017 3018888326675390586261763)
                      ·
                        rfl

theorem cell23_5879264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_5879264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879264 prefixEnd_5879264 := by exact prefixLift 5879264
  have htrace : WordTrace (prefixWord ++ tailWord_5879264) baseStart_5879264 baseEnd_5879264 := by
    simpa [prefixWord, tailWord_5879264, baseEnd_5879264] using wordTrace_append hprefix tailTrace_5879264
  have hstable : (prefixWord ++ tailWord_5879264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879264).length < 2 ^ (prefixWord ++ tailWord_5879264).sum := by decide
  have hdescent : baseEnd_5879264 < baseStart_5879264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879271 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_5879271 : Nat := 118140960795 + 5879271 * 2 ^ 59
def prefixEnd_5879271 : Nat := 4983230072969 + 3 ^ 40 * 5879271 * 2
def baseEnd_5879271 : Nat := 3018891921039972058874231

theorem tailTrace_5879271 : CollatzResearch.WordTrace tailWord_5879271 prefixEnd_5879271 3018891921039972058874231 := by
  unfold tailWord_5879271
  simp only [CollatzResearch.WordTrace]
  refine ⟨214434629883412741391461667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142956419922275160927641111 214434629883412741391461667)
  ·
    refine ⟨321651944825119112087192501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214434629883412741391461667 321651944825119112087192501)
    ·
      refine ⟨30154869827354916758174297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321651944825119112087192501 30154869827354916758174297)
      ·
        refine ⟨22616152370516187568630723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30154869827354916758174297 22616152370516187568630723)
        ·
          refine ⟨33924228555774281352946085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22616152370516187568630723 33924228555774281352946085)
          ·
            refine ⟨6360792854207677753677391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33924228555774281352946085 6360792854207677753677391)
            ·
              refine ⟨9541189281311516630516087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6360792854207677753677391 9541189281311516630516087)
              ·
                refine ⟨14311783921967274945774131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9541189281311516630516087 14311783921967274945774131)
                ·
                  refine ⟨21467675882950912418661197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14311783921967274945774131 21467675882950912418661197)
                  ·
                    refine ⟨8050378456106592156997949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21467675882950912418661197 8050378456106592156997949)
                    ·
                      refine ⟨3018891921039972058874231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8050378456106592156997949 3018891921039972058874231)
                      ·
                        rfl

theorem cell23_5879271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_5879271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879271 prefixEnd_5879271 := by exact prefixLift 5879271
  have htrace : WordTrace (prefixWord ++ tailWord_5879271) baseStart_5879271 baseEnd_5879271 := by
    simpa [prefixWord, tailWord_5879271, baseEnd_5879271] using wordTrace_append hprefix tailTrace_5879271
  have hstable : (prefixWord ++ tailWord_5879271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879271).length < 2 ^ (prefixWord ++ tailWord_5879271).sum := by decide
  have hdescent : baseEnd_5879271 < baseStart_5879271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879281 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 1, 3, 2]
def baseStart_5879281 : Nat := 118140960795 + 5879281 * 2 ^ 59
def prefixEnd_5879281 : Nat := 4983230072969 + 3 ^ 40 * 5879281 * 2
def baseEnd_5879281 : Nat := 3018897055846517019749185

theorem tailTrace_5879281 : CollatzResearch.WordTrace tailWord_5879281 prefixEnd_5879281 3018897055846517019749185 := by
  unfold tailWord_5879281
  simp only [CollatzResearch.WordTrace]
  refine ⟨214434994613376513099325697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142956663075584342066217131 214434994613376513099325697)
  ·
    refine ⟨160826245960032384824494273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214434994613376513099325697 160826245960032384824494273)
    ·
      refine ⟨120619684470024288618370705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160826245960032384824494273 120619684470024288618370705)
      ·
        refine ⟨90464763352518216463778029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120619684470024288618370705 90464763352518216463778029)
        ·
          refine ⟨33924286257194331173916761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90464763352518216463778029 33924286257194331173916761)
          ·
            refine ⟨25443214692895748380437571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33924286257194331173916761 25443214692895748380437571)
            ·
              refine ⟨38164822039343622570656357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25443214692895748380437571 38164822039343622570656357)
              ·
                refine ⟨7155904132376929231998067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38164822039343622570656357 7155904132376929231998067)
                ·
                  refine ⟨10733856198565393847997101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7155904132376929231998067 10733856198565393847997101)
                  ·
                    refine ⟨4025196074462022692998913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10733856198565393847997101 4025196074462022692998913)
                    ·
                      refine ⟨3018897055846517019749185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025196074462022692998913 3018897055846517019749185)
                      ·
                        rfl

theorem cell23_5879281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_5879281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879281 prefixEnd_5879281 := by exact prefixLift 5879281
  have htrace : WordTrace (prefixWord ++ tailWord_5879281) baseStart_5879281 baseEnd_5879281 := by
    simpa [prefixWord, tailWord_5879281, baseEnd_5879281] using wordTrace_append hprefix tailTrace_5879281
  have hstable : (prefixWord ++ tailWord_5879281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879281).length < 2 ^ (prefixWord ++ tailWord_5879281).sum := by decide
  have hdescent : baseEnd_5879281 < baseStart_5879281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879407 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 8]
def baseStart_5879407 : Nat := 118140960795 + 5879407 * 2 ^ 59
def prefixEnd_5879407 : Nat := 4983230072969 + 3 ^ 40 * 5879407 * 2
def baseEnd_5879407 : Nat := 335440194934331502974845

theorem tailTrace_5879407 : CollatzResearch.WordTrace tailWord_5879407 prefixEnd_5879407 335440194934331502974845 := by
  unfold tailWord_5879407
  simp only [CollatzResearch.WordTrace]
  refine ⟨214439590210920036618412475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142959726807280024412274983 214439590210920036618412475)
  ·
    refine ⟨321659385316380054927618713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214439590210920036618412475 321659385316380054927618713)
    ·
      refine ⟨241244538987285041195714035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321659385316380054927618713 241244538987285041195714035)
      ·
        refine ⟨361866808480927561793571053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241244538987285041195714035 361866808480927561793571053)
        ·
          refine ⟨135700053180347835672589145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361866808480927561793571053 135700053180347835672589145)
          ·
            refine ⟨101775039885260876754441859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135700053180347835672589145 101775039885260876754441859)
            ·
              refine ⟨152662559827891315131662789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101775039885260876754441859 152662559827891315131662789)
              ·
                refine ⟨28624229967729621587186773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152662559827891315131662789 28624229967729621587186773)
                ·
                  refine ⟨335440194934331502974845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28624229967729621587186773 335440194934331502974845)
                  ·
                    rfl

theorem cell23_5879407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 8].length) (baseStart_5879407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879407 prefixEnd_5879407 := by exact prefixLift 5879407
  have htrace : WordTrace (prefixWord ++ tailWord_5879407) baseStart_5879407 baseEnd_5879407 := by
    simpa [prefixWord, tailWord_5879407, baseEnd_5879407] using wordTrace_append hprefix tailTrace_5879407
  have hstable : (prefixWord ++ tailWord_5879407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879407).length < 2 ^ (prefixWord ++ tailWord_5879407).sum := by decide
  have hdescent : baseEnd_5879407 < baseStart_5879407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879428 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_5879428 : Nat := 118140960795 + 5879428 * 2 ^ 59
def prefixEnd_5879428 : Nat := 4983230072969 + 3 ^ 40 * 5879428 * 2
def baseEnd_5879428 : Nat := 1006324179167575981537003

theorem tailTrace_5879428 : CollatzResearch.WordTrace tailWord_5879428 prefixEnd_5879428 1006324179167575981537003 := by
  unfold tailWord_5879428
  simp only [CollatzResearch.WordTrace]
  refine ⟨107220178071921978602463469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142960237429229304803284625 107220178071921978602463469)
  ·
    refine ⟨40207566776970741975923801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107220178071921978602463469 40207566776970741975923801)
    ·
      refine ⟨30155675082728056481942851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40207566776970741975923801 30155675082728056481942851)
      ·
        refine ⟨45233512624092084722914277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30155675082728056481942851 45233512624092084722914277)
        ·
          refine ⟨8481283617017265885546427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45233512624092084722914277 8481283617017265885546427)
          ·
            refine ⟨12721925425525898828319641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8481283617017265885546427 12721925425525898828319641)
            ·
              refine ⟨9541444069144424121239731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12721925425525898828319641 9541444069144424121239731)
              ·
                refine ⟨14312166103716636181859597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9541444069144424121239731 14312166103716636181859597)
                ·
                  refine ⟨5367062288893738568197349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14312166103716636181859597 5367062288893738568197349)
                  ·
                    refine ⟨1006324179167575981537003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5367062288893738568197349 1006324179167575981537003)
                    ·
                      rfl

theorem cell23_5879428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_5879428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879428 prefixEnd_5879428 := by exact prefixLift 5879428
  have htrace : WordTrace (prefixWord ++ tailWord_5879428) baseStart_5879428 baseEnd_5879428 := by
    simpa [prefixWord, tailWord_5879428, baseEnd_5879428] using wordTrace_append hprefix tailTrace_5879428
  have hstable : (prefixWord ++ tailWord_5879428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879428).length < 2 ^ (prefixWord ++ tailWord_5879428).sum := by decide
  have hdescent : baseEnd_5879428 < baseStart_5879428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879461 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 1, 5, 2]
def baseStart_5879461 : Nat := 118140960795 + 5879461 * 2 ^ 59
def prefixEnd_5879461 : Nat := 4983230072969 + 3 ^ 40 * 5879461 * 2
def baseEnd_5879461 : Nat := 3018989482364326315498357

theorem tailTrace_5879461 : CollatzResearch.WordTrace tailWord_5879461 prefixEnd_5879461 3018989482364326315498357 := by
  unfold tailWord_5879461
  simp only [CollatzResearch.WordTrace]
  refine ⟨214441559752724403840878237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142961039835149602560585491 214441559752724403840878237)
  ·
    refine ⟨80415584907271651440329339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214441559752724403840878237 80415584907271651440329339)
    ·
      refine ⟨120623377360907477160494009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80415584907271651440329339 120623377360907477160494009)
      ·
        refine ⟨90467533020680607870370507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120623377360907477160494009 90467533020680607870370507)
        ·
          refine ⟨135701299531020911805555761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90467533020680607870370507 135701299531020911805555761)
          ·
            refine ⟨101775974648265683854166821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135701299531020911805555761 101775974648265683854166821)
            ·
              refine ⟨19082995246549815722656279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101775974648265683854166821 19082995246549815722656279)
              ·
                refine ⟨28624492869824723583984419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19082995246549815722656279 28624492869824723583984419)
                ·
                  refine ⟨42936739304737085375976629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28624492869824723583984419 42936739304737085375976629)
                  ·
                    refine ⟨4025319309819101753997809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42936739304737085375976629 4025319309819101753997809)
                    ·
                      refine ⟨3018989482364326315498357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025319309819101753997809 3018989482364326315498357)
                      ·
                        rfl

theorem cell23_5879461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_5879461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879461 prefixEnd_5879461 := by exact prefixLift 5879461
  have htrace : WordTrace (prefixWord ++ tailWord_5879461) baseStart_5879461 baseEnd_5879461 := by
    simpa [prefixWord, tailWord_5879461, baseEnd_5879461] using wordTrace_append hprefix tailTrace_5879461
  have hstable : (prefixWord ++ tailWord_5879461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879461).length < 2 ^ (prefixWord ++ tailWord_5879461).sum := by decide
  have hdescent : baseEnd_5879461 < baseStart_5879461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879508 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5879508 : Nat := 118140960795 + 5879508 * 2 ^ 59
def prefixEnd_5879508 : Nat := 4983230072969 + 3 ^ 40 * 5879508 * 2
def baseEnd_5879508 : Nat := 3019013615955087631610641

theorem tailTrace_5879508 : CollatzResearch.WordTrace tailWord_5879508 prefixEnd_5879508 3019013615955087631610641 := by
  unfold tailWord_5879508
  simp only [CollatzResearch.WordTrace]
  refine ⟨107221636991777065433919589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142962182655702753911892785 107221636991777065433919589)
  ·
    refine ⟨20104056935958199768859923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107221636991777065433919589 20104056935958199768859923)
    ·
      refine ⟨30156085403937299653289885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20104056935958199768859923 30156085403937299653289885)
      ·
        refine ⟨11308532026476487369983707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30156085403937299653289885 11308532026476487369983707)
        ·
          refine ⟨16962798039714731054975561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11308532026476487369983707 16962798039714731054975561)
          ·
            refine ⟨12722098529786048291231671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16962798039714731054975561 12722098529786048291231671)
            ·
              refine ⟨19083147794679072436847507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12722098529786048291231671 19083147794679072436847507)
              ·
                refine ⟨28624721692018608655271261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19083147794679072436847507 28624721692018608655271261)
                ·
                  refine ⟨10734270634506978245726723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28624721692018608655271261 10734270634506978245726723)
                  ·
                    refine ⟨16101405951760467368590085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10734270634506978245726723 16101405951760467368590085)
                    ·
                      refine ⟨3019013615955087631610641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16101405951760467368590085 3019013615955087631610641)
                      ·
                        rfl

theorem cell23_5879508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5879508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879508 prefixEnd_5879508 := by exact prefixLift 5879508
  have htrace : WordTrace (prefixWord ++ tailWord_5879508) baseStart_5879508 baseEnd_5879508 := by
    simpa [prefixWord, tailWord_5879508, baseEnd_5879508] using wordTrace_append hprefix tailTrace_5879508
  have hstable : (prefixWord ++ tailWord_5879508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879508).length < 2 ^ (prefixWord ++ tailWord_5879508).sum := by decide
  have hdescent : baseEnd_5879508 < baseStart_5879508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879511 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_5879511 : Nat := 118140960795 + 5879511 * 2 ^ 59
def prefixEnd_5879511 : Nat := 4983230072969 + 3 ^ 40 * 5879511 * 2
def baseEnd_5879511 : Nat := 3019015156397051119873127

theorem tailTrace_5879511 : CollatzResearch.WordTrace tailWord_5879511 prefixEnd_5879511 3019015156397051119873127 := by
  unfold tailWord_5879511
  simp only [CollatzResearch.WordTrace]
  refine ⟨214443383402543262380198387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142962255601695508253465591 214443383402543262380198387)
  ·
    refine ⟨321665075103814893570297581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214443383402543262380198387 321665075103814893570297581)
    ·
      refine ⟨120624403163930585088861593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321665075103814893570297581 120624403163930585088861593)
      ·
        refine ⟨90468302372947938816646195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120624403163930585088861593 90468302372947938816646195)
        ·
          refine ⟨135702453559421908224969293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90468302372947938816646195 135702453559421908224969293)
          ·
            refine ⟨50888420084783215584363485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135702453559421908224969293 50888420084783215584363485)
            ·
              refine ⟨19083157531793705844136307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50888420084783215584363485 19083157531793705844136307)
              ·
                refine ⟨28624736297690558766204461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19083157531793705844136307 28624736297690558766204461)
                ·
                  refine ⟨10734276111633959537326673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28624736297690558766204461 10734276111633959537326673)
                  ·
                    refine ⟨8050707083725469652995005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10734276111633959537326673 8050707083725469652995005)
                    ·
                      refine ⟨3019015156397051119873127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8050707083725469652995005 3019015156397051119873127)
                      ·
                        rfl

theorem cell23_5879511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_5879511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879511 prefixEnd_5879511 := by exact prefixLift 5879511
  have htrace : WordTrace (prefixWord ++ tailWord_5879511) baseStart_5879511 baseEnd_5879511 := by
    simpa [prefixWord, tailWord_5879511, baseEnd_5879511] using wordTrace_append hprefix tailTrace_5879511
  have hstable : (prefixWord ++ tailWord_5879511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879511).length < 2 ^ (prefixWord ++ tailWord_5879511).sum := by decide
  have hdescent : baseEnd_5879511 < baseStart_5879511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879514 : List Nat := [3, 1, 1, 2, 2, 3, 2, 9]
def baseStart_5879514 : Nat := 118140960795 + 5879514 * 2 ^ 59
def prefixEnd_5879514 : Nat := 4983230072969 + 3 ^ 40 * 5879514 * 2
def baseEnd_5879514 : Nat := 111815433216259800301319

theorem tailTrace_5879514 : CollatzResearch.WordTrace tailWord_5879514 prefixEnd_5879514 111815433216259800301319 := by
  unfold tailWord_5879514
  simp only [CollatzResearch.WordTrace]
  refine ⟨53610873205383098473139399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142962328547688262595038397 53610873205383098473139399)
  ·
    refine ⟨80416309808074647709709099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53610873205383098473139399 80416309808074647709709099)
    ·
      refine ⟨120624464712111971564563649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80416309808074647709709099 120624464712111971564563649)
      ·
        refine ⟨90468348534083978673422737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120624464712111971564563649 90468348534083978673422737)
        ·
          refine ⟨67851261400562984005067053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90468348534083978673422737 67851261400562984005067053)
          ·
            refine ⟨25444223025211119001900145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67851261400562984005067053 25444223025211119001900145)
            ·
              refine ⟨19083167268908339251425109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25444223025211119001900145 19083167268908339251425109)
              ·
                refine ⟨111815433216259800301319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19083167268908339251425109 111815433216259800301319)
                ·
                  rfl

theorem cell23_5879514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 9].length) (baseStart_5879514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879514 prefixEnd_5879514 := by exact prefixLift 5879514
  have htrace : WordTrace (prefixWord ++ tailWord_5879514) baseStart_5879514 baseEnd_5879514 := by
    simpa [prefixWord, tailWord_5879514, baseEnd_5879514] using wordTrace_append hprefix tailTrace_5879514
  have hstable : (prefixWord ++ tailWord_5879514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879514).length < 2 ^ (prefixWord ++ tailWord_5879514).sum := by decide
  have hdescent : baseEnd_5879514 < baseStart_5879514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879528 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_5879528 : Nat := 118140960795 + 5879528 * 2 ^ 59
def prefixEnd_5879528 : Nat := 4983230072969 + 3 ^ 40 * 5879528 * 2
def baseEnd_5879528 : Nat := 3019023885568177553360549

theorem tailTrace_5879528 : CollatzResearch.WordTrace tailWord_5879528 prefixEnd_5879528 3019023885568177553360549 := by
  unfold tailWord_5879528
  simp only [CollatzResearch.WordTrace]
  refine ⟨107222001721740837141783619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142962668962321116189044825 107222001721740837141783619)
  ·
    refine ⟨160833002582611255712675429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107222001721740837141783619 160833002582611255712675429)
    ·
      refine ⟨30156187984239610446126643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160833002582611255712675429 30156187984239610446126643)
      ·
        refine ⟨45234281976359415669189965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30156187984239610446126643 45234281976359415669189965)
        ·
          refine ⟨16962855741134780875946237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45234281976359415669189965 16962855741134780875946237)
          ·
            refine ⟨6361070902925542828479839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16962855741134780875946237 6361070902925542828479839)
            ·
              refine ⟨9541606354388314242719759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361070902925542828479839 9541606354388314242719759)
              ·
                refine ⟨14312409531582471364079639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9541606354388314242719759 14312409531582471364079639)
                ·
                  refine ⟨21468614297373707046119459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14312409531582471364079639 21468614297373707046119459)
                  ·
                    refine ⟨32202921446060560569179189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21468614297373707046119459 32202921446060560569179189)
                    ·
                      refine ⟨3019023885568177553360549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32202921446060560569179189 3019023885568177553360549)
                      ·
                        rfl

theorem cell23_5879528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_5879528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879528 prefixEnd_5879528 := by exact prefixLift 5879528
  have htrace : WordTrace (prefixWord ++ tailWord_5879528) baseStart_5879528 baseEnd_5879528 := by
    simpa [prefixWord, tailWord_5879528, baseEnd_5879528] using wordTrace_append hprefix tailTrace_5879528
  have hstable : (prefixWord ++ tailWord_5879528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879528).length < 2 ^ (prefixWord ++ tailWord_5879528).sum := by decide
  have hdescent : baseEnd_5879528 < baseStart_5879528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879585 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_5879585 : Nat := 118140960795 + 5879585 * 2 ^ 59
def prefixEnd_5879585 : Nat := 4983230072969 + 3 ^ 40 * 5879585 * 2
def baseEnd_5879585 : Nat := 3019053153965483830347787

theorem tailTrace_5879585 : CollatzResearch.WordTrace tailWord_5879585 prefixEnd_5879585 3019053153965483830347787 := by
  unfold tailWord_5879585
  simp only [CollatzResearch.WordTrace]
  refine ⟨214446082404275173018392209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142964054936183448678928139 214446082404275173018392209)
  ·
    refine ⟨160834561803206379763794157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214446082404275173018392209 160834561803206379763794157)
    ·
      refine ⟨60312960676202392411422809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160834561803206379763794157 60312960676202392411422809)
      ·
        refine ⟨45234720507151794308567107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60312960676202392411422809 45234720507151794308567107)
        ·
          refine ⟨67852080760727691462850661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45234720507151794308567107 67852080760727691462850661)
          ·
            refine ⟨12722265142636442149284499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67852080760727691462850661 12722265142636442149284499)
            ·
              refine ⟨19083397713954663223926749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12722265142636442149284499 19083397713954663223926749)
              ·
                refine ⟨7156274142732998708972531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19083397713954663223926749 7156274142732998708972531)
                ·
                  refine ⟨10734411214099498063458797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7156274142732998708972531 10734411214099498063458797)
                  ·
                    refine ⟨4025404205287311773797049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10734411214099498063458797 4025404205287311773797049)
                    ·
                      refine ⟨3019053153965483830347787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025404205287311773797049 3019053153965483830347787)
                      ·
                        rfl

theorem cell23_5879585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_5879585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879585 prefixEnd_5879585 := by exact prefixLift 5879585
  have htrace : WordTrace (prefixWord ++ tailWord_5879585) baseStart_5879585 baseEnd_5879585 := by
    simpa [prefixWord, tailWord_5879585, baseEnd_5879585] using wordTrace_append hprefix tailTrace_5879585
  have hstable : (prefixWord ++ tailWord_5879585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879585).length < 2 ^ (prefixWord ++ tailWord_5879585).sum := by decide
  have hdescent : baseEnd_5879585 < baseStart_5879585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879592 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_5879592 : Nat := 118140960795 + 5879592 * 2 ^ 59
def prefixEnd_5879592 : Nat := 4983230072969 + 3 ^ 40 * 5879592 * 2
def baseEnd_5879592 : Nat := 3019056748330065302960255

theorem tailTrace_5879592 : CollatzResearch.WordTrace tailWord_5879592 prefixEnd_5879592 3019056748330065302960255 := by
  unfold tailWord_5879592
  simp only [CollatzResearch.WordTrace]
  refine ⟨107223168857624906606948515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142964225143499875475931353 107223168857624906606948515)
  ·
    refine ⟨160834753286437359910422773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107223168857624906606948515 160834753286437359910422773)
    ·
      refine ⟨15078258120603502491602135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160834753286437359910422773 15078258120603502491602135)
      ·
        refine ⟨22617387180905253737403203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15078258120603502491602135 22617387180905253737403203)
        ·
          refine ⟨33926080771357880606104805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22617387180905253737403203 33926080771357880606104805)
          ·
            refine ⟨6361140144629602613644651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33926080771357880606104805 6361140144629602613644651)
            ·
              refine ⟨9541710216944403920466977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361140144629602613644651 9541710216944403920466977)
              ·
                refine ⟨7156282662708302940350233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9541710216944403920466977 7156282662708302940350233)
                ·
                  refine ⟨5367211997031227205262675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7156282662708302940350233 5367211997031227205262675)
                  ·
                    refine ⟨8050817995546840807894013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5367211997031227205262675 8050817995546840807894013)
                    ·
                      refine ⟨3019056748330065302960255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8050817995546840807894013 3019056748330065302960255)
                      ·
                        rfl

theorem cell23_5879592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_5879592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879592 prefixEnd_5879592 := by exact prefixLift 5879592
  have htrace : WordTrace (prefixWord ++ tailWord_5879592) baseStart_5879592 baseEnd_5879592 := by
    simpa [prefixWord, tailWord_5879592, baseEnd_5879592] using wordTrace_append hprefix tailTrace_5879592
  have hstable : (prefixWord ++ tailWord_5879592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879592).length < 2 ^ (prefixWord ++ tailWord_5879592).sum := by decide
  have hdescent : baseEnd_5879592 < baseStart_5879592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879609 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5879609 : Nat := 118140960795 + 5879609 * 2 ^ 59
def prefixEnd_5879609 : Nat := 4983230072969 + 3 ^ 40 * 5879609 * 2
def baseEnd_5879609 : Nat := 3019065477501191736447677

theorem tailTrace_5879609 : CollatzResearch.WordTrace tailWord_5879609 prefixEnd_5879609 3019065477501191736447677 := by
  unfold tailWord_5879609
  simp only [CollatzResearch.WordTrace]
  refine ⟨214446957756188225117265881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142964638504125483411510587 214446957756188225117265881)
  ·
    refine ⟨160835218317141168837949411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214446957756188225117265881 160835218317141168837949411)
    ·
      refine ⟨241252827475711753256924117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160835218317141168837949411 241252827475711753256924117)
      ·
        refine ⟨5654363143961994216959159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 241252827475711753256924117 5654363143961994216959159)
        ·
          refine ⟨8481544715942991325438739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5654363143961994216959159 8481544715942991325438739)
          ·
            refine ⟨12722317073914486988158109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8481544715942991325438739 12722317073914486988158109)
            ·
              refine ⟨4770868902717932620559291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12722317073914486988158109 4770868902717932620559291)
              ·
                refine ⟨7156303354076898930838937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4770868902717932620559291 7156303354076898930838937)
                ·
                  refine ⟨5367227515557674198129203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7156303354076898930838937 5367227515557674198129203)
                  ·
                    refine ⟨8050841273336511297193805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5367227515557674198129203 8050841273336511297193805)
                    ·
                      refine ⟨3019065477501191736447677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8050841273336511297193805 3019065477501191736447677)
                      ·
                        rfl

theorem cell23_5879609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5879609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879609 prefixEnd_5879609 := by exact prefixLift 5879609
  have htrace : WordTrace (prefixWord ++ tailWord_5879609) baseStart_5879609 baseEnd_5879609 := by
    simpa [prefixWord, tailWord_5879609, baseEnd_5879609] using wordTrace_append hprefix tailTrace_5879609
  have hstable : (prefixWord ++ tailWord_5879609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879609).length < 2 ^ (prefixWord ++ tailWord_5879609).sum := by decide
  have hdescent : baseEnd_5879609 < baseStart_5879609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879655 : List Nat := [1, 1, 5, 1, 2, 1, 5, 2, 5]
def baseStart_5879655 : Nat := 118140960795 + 5879655 * 2 ^ 59
def prefixEnd_5879655 : Nat := 4983230072969 + 3 ^ 40 * 5879655 * 2
def baseEnd_5879655 : Nat := 335454344179033172941385

theorem tailTrace_5879655 : CollatzResearch.WordTrace tailWord_5879655 prefixEnd_5879655 335454344179033172941385 := by
  unfold tailWord_5879655
  simp only [CollatzResearch.WordTrace]
  refine ⟨214448635514021574973440419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142965757009347716648960279 214448635514021574973440419)
  ·
    refine ⟨321672953271032362460160629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214448635514021574973440419 321672953271032362460160629)
    ·
      refine ⟨30156839369159283980640059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321672953271032362460160629 30156839369159283980640059)
      ·
        refine ⟨45235259053738925970960089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30156839369159283980640059 45235259053738925970960089)
        ·
          refine ⟨33926444290304194478220067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45235259053738925970960089 33926444290304194478220067)
          ·
            refine ⟨50889666435456291717330101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33926444290304194478220067 50889666435456291717330101)
            ·
              refine ⟨4770906228324027348499697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50889666435456291717330101 4770906228324027348499697)
              ·
                refine ⟨3578179671243020511374773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770906228324027348499697 3578179671243020511374773)
                ·
                  refine ⟨335454344179033172941385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3578179671243020511374773 335454344179033172941385)
                  ·
                    rfl

theorem cell23_5879655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 5].length) (baseStart_5879655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879655 prefixEnd_5879655 := by exact prefixLift 5879655
  have htrace : WordTrace (prefixWord ++ tailWord_5879655) baseStart_5879655 baseEnd_5879655 := by
    simpa [prefixWord, tailWord_5879655, baseEnd_5879655] using wordTrace_append hprefix tailTrace_5879655
  have hstable : (prefixWord ++ tailWord_5879655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879655).length < 2 ^ (prefixWord ++ tailWord_5879655).sum := by decide
  have hdescent : baseEnd_5879655 < baseStart_5879655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879661 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_5879661 : Nat := 118140960795 + 5879661 * 2 ^ 59
def prefixEnd_5879661 : Nat := 4983230072969 + 3 ^ 40 * 5879661 * 2
def baseEnd_5879661 : Nat := 3019092178495225532997437

theorem tailTrace_5879661 : CollatzResearch.WordTrace tailWord_5879661 prefixEnd_5879661 3019092178495225532997437 := by
  unfold tailWord_5879661
  simp only [CollatzResearch.WordTrace]
  refine ⟨214448854351999837998158837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142965902901333225332105891 214448854351999837998158837)
  ·
    refine ⟨20104580095499984812327391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214448854351999837998158837 20104580095499984812327391)
    ·
      refine ⟨30156870143249977218491087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20104580095499984812327391 30156870143249977218491087)
      ·
        refine ⟨45235305214874965827736631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30156870143249977218491087 45235305214874965827736631)
        ·
          refine ⟨67852957822312448741604947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45235305214874965827736631 67852957822312448741604947)
          ·
            refine ⟨101779436733468673112407421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67852957822312448741604947 101779436733468673112407421)
            ·
              refine ⟨38167288775050752417152783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101779436733468673112407421 38167288775050752417152783)
              ·
                refine ⟨57250933162576128625729175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38167288775050752417152783 57250933162576128625729175)
                ·
                  refine ⟨85876399743864192938593763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57250933162576128625729175 85876399743864192938593763)
                  ·
                    refine ⟨128814599615796289407890645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85876399743864192938593763 128814599615796289407890645)
                    ·
                      refine ⟨3019092178495225532997437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128814599615796289407890645 3019092178495225532997437)
                      ·
                        rfl

theorem cell23_5879661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_5879661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879661 prefixEnd_5879661 := by exact prefixLift 5879661
  have htrace : WordTrace (prefixWord ++ tailWord_5879661) baseStart_5879661 baseEnd_5879661 := by
    simpa [prefixWord, tailWord_5879661, baseEnd_5879661] using wordTrace_append hprefix tailTrace_5879661
  have hstable : (prefixWord ++ tailWord_5879661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879661).length < 2 ^ (prefixWord ++ tailWord_5879661).sum := by decide
  have hdescent : baseEnd_5879661 < baseStart_5879661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879701 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_5879701 : Nat := 118140960795 + 5879701 * 2 ^ 59
def prefixEnd_5879701 : Nat := 4983230072969 + 3 ^ 40 * 5879701 * 2
def baseEnd_5879701 : Nat := 3019112717721405376497253

theorem tailTrace_5879701 : CollatzResearch.WordTrace tailWord_5879701 prefixEnd_5879701 3019112717721405376497253 := by
  unfold tailWord_5879701
  simp only [CollatzResearch.WordTrace]
  refine ⟨214450313271854924829614957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142966875514569949886409971 214450313271854924829614957)
  ·
    refine ⟨80418867476945596811105609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214450313271854924829614957 80418867476945596811105609)
    ·
      refine ⟨60314150607709197608329207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80418867476945596811105609 60314150607709197608329207)
      ·
        refine ⟨90471225911563796412493811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60314150607709197608329207 90471225911563796412493811)
        ·
          refine ⟨135706838867345694618740717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90471225911563796412493811 135706838867345694618740717)
          ·
            refine ⟨50890064575254635482027769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135706838867345694618740717 50890064575254635482027769)
            ·
              refine ⟨38167548431440976611520827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50890064575254635482027769 38167548431440976611520827)
              ·
                refine ⟨57251322647161464917281241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38167548431440976611520827 57251322647161464917281241)
                ·
                  refine ⟨42938491985371098687960931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57251322647161464917281241 42938491985371098687960931)
                  ·
                    refine ⟨64407737978056648031941397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42938491985371098687960931 64407737978056648031941397)
                    ·
                      refine ⟨3019112717721405376497253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64407737978056648031941397 3019112717721405376497253)
                      ·
                        rfl

theorem cell23_5879701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_5879701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879701 prefixEnd_5879701 := by exact prefixLift 5879701
  have htrace : WordTrace (prefixWord ++ tailWord_5879701) baseStart_5879701 baseEnd_5879701 := by
    simpa [prefixWord, tailWord_5879701, baseEnd_5879701] using wordTrace_append hprefix tailTrace_5879701
  have hstable : (prefixWord ++ tailWord_5879701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879701).length < 2 ^ (prefixWord ++ tailWord_5879701).sum := by decide
  have hdescent : baseEnd_5879701 < baseStart_5879701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879742 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_5879742 : Nat := 118140960795 + 5879742 * 2 ^ 59
def prefixEnd_5879742 : Nat := 4983230072969 + 3 ^ 40 * 5879742 * 2
def baseEnd_5879742 : Nat := 3019133770428239716084565

theorem tailTrace_5879742 : CollatzResearch.WordTrace tailWord_5879742 prefixEnd_5879742 3019133770428239716084565 := by
  unfold tailWord_5879742
  simp only [CollatzResearch.WordTrace]
  refine ⟨26806476083088298603982185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142967872443137592554571653 26806476083088298603982185)
  ·
    refine ⟨20104857062316223952986639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26806476083088298603982185 20104857062316223952986639)
    ·
      refine ⟨30157285593474335929479959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20104857062316223952986639 30157285593474335929479959)
      ·
        refine ⟨45235928390211503894219939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30157285593474335929479959 45235928390211503894219939)
        ·
          refine ⟨67853892585317255841329909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45235928390211503894219939 67853892585317255841329909)
          ·
            refine ⟨6361302429873492735124679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67853892585317255841329909 6361302429873492735124679)
            ·
              refine ⟨9541953644810239102687019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361302429873492735124679 9541953644810239102687019)
              ·
                refine ⟨14312930467215358654030529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9541953644810239102687019 14312930467215358654030529)
                ·
                  refine ⟨10734697850411518990522897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14312930467215358654030529 10734697850411518990522897)
                  ·
                    refine ⟨8051023387808639242892173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10734697850411518990522897 8051023387808639242892173)
                    ·
                      refine ⟨3019133770428239716084565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8051023387808639242892173 3019133770428239716084565)
                      ·
                        rfl

theorem cell23_5879742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_5879742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879742 prefixEnd_5879742 := by exact prefixLift 5879742
  have htrace : WordTrace (prefixWord ++ tailWord_5879742) baseStart_5879742 baseEnd_5879742 := by
    simpa [prefixWord, tailWord_5879742, baseEnd_5879742] using wordTrace_append hprefix tailTrace_5879742
  have hstable : (prefixWord ++ tailWord_5879742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879742).length < 2 ^ (prefixWord ++ tailWord_5879742).sum := by decide
  have hdescent : baseEnd_5879742 < baseStart_5879742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879751 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_5879751 : Nat := 118140960795 + 5879751 * 2 ^ 59
def prefixEnd_5879751 : Nat := 4983230072969 + 3 ^ 40 * 5879751 * 2
def baseEnd_5879751 : Nat := 3019138391754130180872023

theorem tailTrace_5879751 : CollatzResearch.WordTrace tailWord_5879751 prefixEnd_5879751 3019138391754130180872023 := by
  unfold tailWord_5879751
  simp only [CollatzResearch.WordTrace]
  refine ⟨214452136921673783368935107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142968091281115855579290071 214452136921673783368935107)
  ·
    refine ⟨321678205382510675053402661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214452136921673783368935107 321678205382510675053402661)
    ·
      refine ⟨60314663509220751572512999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321678205382510675053402661 60314663509220751572512999)
      ·
        refine ⟨90471995263831127358769499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60314663509220751572512999 90471995263831127358769499)
        ·
          refine ⟨135707992895746691038154249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90471995263831127358769499 135707992895746691038154249)
          ·
            refine ⟨101780994671810018278615687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135707992895746691038154249 101780994671810018278615687)
            ·
              refine ⟨152671492007715027417923531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101780994671810018278615687 152671492007715027417923531)
              ·
                refine ⟨229007238011572541126885297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152671492007715027417923531 229007238011572541126885297)
                ·
                  refine ⟨171755428508679405845163973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229007238011572541126885297 171755428508679405845163973)
                  ·
                    refine ⟨32204142845377388595968245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171755428508679405845163973 32204142845377388595968245)
                    ·
                      refine ⟨3019138391754130180872023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32204142845377388595968245 3019138391754130180872023)
                      ·
                        rfl

theorem cell23_5879751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_5879751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879751 prefixEnd_5879751 := by exact prefixLift 5879751
  have htrace : WordTrace (prefixWord ++ tailWord_5879751) baseStart_5879751 baseEnd_5879751 := by
    simpa [prefixWord, tailWord_5879751, baseEnd_5879751] using wordTrace_append hprefix tailTrace_5879751
  have hstable : (prefixWord ++ tailWord_5879751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879751).length < 2 ^ (prefixWord ++ tailWord_5879751).sum := by decide
  have hdescent : baseEnd_5879751 < baseStart_5879751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879762 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 6]
def baseStart_5879762 : Nat := 118140960795 + 5879762 * 2 ^ 59
def prefixEnd_5879762 : Nat := 4983230072969 + 3 ^ 40 * 5879762 * 2
def baseEnd_5879762 : Nat := 335460448893481070870497

theorem tailTrace_5879762 : CollatzResearch.WordTrace tailWord_5879762 prefixEnd_5879762 335460448893481070870497 := by
  unfold tailWord_5879762
  simp only [CollatzResearch.WordTrace]
  refine ⟨53613134531158483061896385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142968358749755954831723693 53613134531158483061896385)
  ·
    refine ⟨40209850898368862296422289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53613134531158483061896385 40209850898368862296422289)
    ·
      refine ⟨30157388173776646722316717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40209850898368862296422289 30157388173776646722316717)
      ·
        refine ⟨11309020565166242520868769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30157388173776646722316717 11309020565166242520868769)
        ·
          refine ⟨8481765423874681890651577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11309020565166242520868769 8481765423874681890651577)
          ·
            refine ⟨6361324067906011417988683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8481765423874681890651577 6361324067906011417988683)
            ·
              refine ⟨9541986101859017126983025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361324067906011417988683 9541986101859017126983025)
              ·
                refine ⟨7156489576394262845237269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9541986101859017126983025 7156489576394262845237269)
                ·
                  refine ⟨335460448893481070870497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7156489576394262845237269 335460448893481070870497)
                  ·
                    rfl

theorem cell23_5879762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_5879762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879762 prefixEnd_5879762 := by exact prefixLift 5879762
  have htrace : WordTrace (prefixWord ++ tailWord_5879762) baseStart_5879762 baseEnd_5879762 := by
    simpa [prefixWord, tailWord_5879762, baseEnd_5879762] using wordTrace_append hprefix tailTrace_5879762
  have hstable : (prefixWord ++ tailWord_5879762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879762).length < 2 ^ (prefixWord ++ tailWord_5879762).sum := by decide
  have hdescent : baseEnd_5879762 < baseStart_5879762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879806 : List Nat := [4, 2, 2, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5879806 : Nat := 118140960795 + 5879806 * 2 ^ 59
def prefixEnd_5879806 : Nat := 4983230072969 + 3 ^ 40 * 5879806 * 2
def baseEnd_5879806 : Nat := 3019166633190127465684271

theorem tailTrace_5879806 : CollatzResearch.WordTrace tailWord_5879806 prefixEnd_5879806 3019166633190127465684271 := by
  unfold tailWord_5879806
  simp only [CollatzResearch.WordTrace]
  refine ⟨26806767867059315970273409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142969428624316351841458181 26806767867059315970273409)
  ·
    refine ⟨20105075900294486977705057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26806767867059315970273409 20105075900294486977705057)
    ·
      refine ⟨15078806925220865233278793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20105075900294486977705057 15078806925220865233278793)
      ·
        refine ⟨11309105193915648924959095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15078806925220865233278793 11309105193915648924959095)
        ·
          refine ⟨16963657790873473387438643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309105193915648924959095 16963657790873473387438643)
          ·
            refine ⟨25445486686310210081157965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16963657790873473387438643 25445486686310210081157965)
            ·
              refine ⟨9542057507366328780434237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25445486686310210081157965 9542057507366328780434237)
              ·
                refine ⟨3578271565262373292662839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9542057507366328780434237 3578271565262373292662839)
                ·
                  refine ⟨5367407347893559938994259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578271565262373292662839 5367407347893559938994259)
                  ·
                    refine ⟨8051111021840339908491389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5367407347893559938994259 8051111021840339908491389)
                    ·
                      refine ⟨3019166633190127465684271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8051111021840339908491389 3019166633190127465684271)
                      ·
                        rfl

theorem cell23_5879806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5879806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879806 prefixEnd_5879806 := by exact prefixLift 5879806
  have htrace : WordTrace (prefixWord ++ tailWord_5879806) baseStart_5879806 baseEnd_5879806 := by
    simpa [prefixWord, tailWord_5879806, baseEnd_5879806] using wordTrace_append hprefix tailTrace_5879806
  have hstable : (prefixWord ++ tailWord_5879806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879806).length < 2 ^ (prefixWord ++ tailWord_5879806).sum := by decide
  have hdescent : baseEnd_5879806 < baseStart_5879806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879815 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_5879815 : Nat := 118140960795 + 5879815 * 2 ^ 59
def prefixEnd_5879815 : Nat := 4983230072969 + 3 ^ 40 * 5879815 * 2
def baseEnd_5879815 : Nat := 3019171254516017930471729

theorem tailTrace_5879815 : CollatzResearch.WordTrace tailWord_5879815 prefixEnd_5879815 3019171254516017930471729 := by
  unfold tailWord_5879815
  simp only [CollatzResearch.WordTrace]
  refine ⟨214454471193441922299264899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142969647462294614866176599 214454471193441922299264899)
  ·
    refine ⟨321681706790162883448897349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214454471193441922299264899 321681706790162883448897349)
    ·
      refine ⟨60315320023155540646668253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321681706790162883448897349 60315320023155540646668253)
      ·
        refine ⟨22618245008683327742500595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60315320023155540646668253 22618245008683327742500595)
        ·
          refine ⟨33927367513024991613750893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22618245008683327742500595 33927367513024991613750893)
          ·
            refine ⟨12722762817384371855156585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33927367513024991613750893 12722762817384371855156585)
            ·
              refine ⟨9542072113038278891367439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12722762817384371855156585 9542072113038278891367439)
              ·
                refine ⟨14313108169557418337051159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9542072113038278891367439 14313108169557418337051159)
                ·
                  refine ⟨21469662254336127505576739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14313108169557418337051159 21469662254336127505576739)
                  ·
                    refine ⟨32204493381504191258365109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21469662254336127505576739 32204493381504191258365109)
                    ·
                      refine ⟨3019171254516017930471729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32204493381504191258365109 3019171254516017930471729)
                      ·
                        rfl

theorem cell23_5879815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_5879815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879815 prefixEnd_5879815 := by exact prefixLift 5879815
  have htrace : WordTrace (prefixWord ++ tailWord_5879815) baseStart_5879815 baseEnd_5879815 := by
    simpa [prefixWord, tailWord_5879815, baseEnd_5879815] using wordTrace_append hprefix tailTrace_5879815
  have hstable : (prefixWord ++ tailWord_5879815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879815).length < 2 ^ (prefixWord ++ tailWord_5879815).sum := by decide
  have hdescent : baseEnd_5879815 < baseStart_5879815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879862 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_5879862 : Nat := 118140960795 + 5879862 * 2 ^ 59
def prefixEnd_5879862 : Nat := 4983230072969 + 3 ^ 40 * 5879862 * 2
def baseEnd_5879862 : Nat := 3019195388106779246584013

theorem tailTrace_5879862 : CollatzResearch.WordTrace tailWord_5879862 prefixEnd_5879862 3019195388106779246584013 := by
  unfold tailWord_5879862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13403511589016978082889115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142970790282847766217483893 13403511589016978082889115)
  ·
    refine ⟨20105267383525467124333673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13403511589016978082889115 20105267383525467124333673)
    ·
      refine ⟨15078950537644100343250255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20105267383525467124333673 15078950537644100343250255)
      ·
        refine ⟨22618425806466150514875383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15078950537644100343250255 22618425806466150514875383)
        ·
          refine ⟨33927638709699225772313075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22618425806466150514875383 33927638709699225772313075)
          ·
            refine ⟨50891458064548838658469613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33927638709699225772313075 50891458064548838658469613)
            ·
              refine ⟨19084296774205814496926105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50891458064548838658469613 19084296774205814496926105)
              ·
                refine ⟨14313222580654360872694579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19084296774205814496926105 14313222580654360872694579)
                ·
                  refine ⟨21469833870981541309041869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14313222580654360872694579 21469833870981541309041869)
                  ·
                    refine ⟨8051187701618077990890701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21469833870981541309041869 8051187701618077990890701)
                    ·
                      refine ⟨3019195388106779246584013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8051187701618077990890701 3019195388106779246584013)
                      ·
                        rfl

theorem cell23_5879862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_5879862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879862 prefixEnd_5879862 := by exact prefixLift 5879862
  have htrace : WordTrace (prefixWord ++ tailWord_5879862) baseStart_5879862 baseEnd_5879862 := by
    simpa [prefixWord, tailWord_5879862, baseEnd_5879862] using wordTrace_append hprefix tailTrace_5879862
  have hstable : (prefixWord ++ tailWord_5879862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879862).length < 2 ^ (prefixWord ++ tailWord_5879862).sum := by decide
  have hdescent : baseEnd_5879862 < baseStart_5879862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879885 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_5879885 : Nat := 118140960795 + 5879885 * 2 ^ 59
def prefixEnd_5879885 : Nat := 4983230072969 + 3 ^ 40 * 5879885 * 2
def baseEnd_5879885 : Nat := 3019207198161832656596407

theorem tailTrace_5879885 : CollatzResearch.WordTrace tailWord_5879885 prefixEnd_5879885 3019207198161832656596407 := by
  unfold tailWord_5879885
  simp only [CollatzResearch.WordTrace]
  refine ⟨214457024303188324254313109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142971349535458882836208739 214457024303188324254313109)
  ·
    refine ⟨10052673014211952699420927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 214457024303188324254313109 10052673014211952699420927)
    ·
      refine ⟨15079009521317929049131391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10052673014211952699420927 15079009521317929049131391)
      ·
        refine ⟨22618514281976893573697087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15079009521317929049131391 22618514281976893573697087)
        ·
          refine ⟨33927771422965340360545631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22618514281976893573697087 33927771422965340360545631)
          ·
            refine ⟨50891657134448010540818447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33927771422965340360545631 50891657134448010540818447)
            ·
              refine ⟨76337485701672015811227671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50891657134448010540818447 76337485701672015811227671)
              ·
                refine ⟨114506228552508023716841507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76337485701672015811227671 114506228552508023716841507)
                ·
                  refine ⟨171759342828762035575262261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114506228552508023716841507 171759342828762035575262261)
                  ·
                    refine ⟨16102438390196440835180837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 171759342828762035575262261 16102438390196440835180837)
                    ·
                      refine ⟨3019207198161832656596407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16102438390196440835180837 3019207198161832656596407)
                      ·
                        rfl

theorem cell23_5879885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_5879885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879885 prefixEnd_5879885 := by exact prefixLift 5879885
  have htrace : WordTrace (prefixWord ++ tailWord_5879885) baseStart_5879885 baseEnd_5879885 := by
    simpa [prefixWord, tailWord_5879885, baseEnd_5879885] using wordTrace_append hprefix tailTrace_5879885
  have hstable : (prefixWord ++ tailWord_5879885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879885).length < 2 ^ (prefixWord ++ tailWord_5879885).sum := by decide
  have hdescent : baseEnd_5879885 < baseStart_5879885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879908 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 9]
def baseStart_5879908 : Nat := 118140960795 + 5879908 * 2 ^ 59
def prefixEnd_5879908 : Nat := 4983230072969 + 3 ^ 40 * 5879908 * 2
def baseEnd_5879908 : Nat := 335468778690765118512089

theorem tailTrace_5879908 : CollatzResearch.WordTrace tailWord_5879908 prefixEnd_5879908 335468778690765118512089 := by
  unfold tailWord_5879908
  simp only [CollatzResearch.WordTrace]
  refine ⟨107228931591052499591200189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142971908788069999454933585 107228931591052499591200189)
  ·
    refine ⟨40210849346644687346700071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107228931591052499591200189 40210849346644687346700071)
    ·
      refine ⟨60316274019967031020050107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40210849346644687346700071 60316274019967031020050107)
      ·
        refine ⟨90474411029950546530075161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60316274019967031020050107 90474411029950546530075161)
        ·
          refine ⟨67855808272462909897556371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90474411029950546530075161 67855808272462909897556371)
          ·
            refine ⟨101783712408694364846334557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67855808272462909897556371 101783712408694364846334557)
            ·
              refine ⟨38168892153260386817375459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101783712408694364846334557 38168892153260386817375459)
              ·
                refine ⟨57253338229890580226063189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38168892153260386817375459 57253338229890580226063189)
                ·
                  refine ⟨335468778690765118512089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57253338229890580226063189 335468778690765118512089)
                  ·
                    rfl

theorem cell23_5879908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_5879908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879908 prefixEnd_5879908 := by exact prefixLift 5879908
  have htrace : WordTrace (prefixWord ++ tailWord_5879908) baseStart_5879908 baseEnd_5879908 := by
    simpa [prefixWord, tailWord_5879908, baseEnd_5879908] using wordTrace_append hprefix tailTrace_5879908
  have hstable : (prefixWord ++ tailWord_5879908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879908).length < 2 ^ (prefixWord ++ tailWord_5879908).sum := by decide
  have hdescent : baseEnd_5879908 < baseStart_5879908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5879989 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_5879989 : Nat := 118140960795 + 5879989 * 2 ^ 59
def prefixEnd_5879989 : Nat := 4983230072969 + 3 ^ 40 * 5879989 * 2
def baseEnd_5879989 : Nat := 1006420200049966749898643

theorem tailTrace_5879989 : CollatzResearch.WordTrace tailWord_5879989 prefixEnd_5879989 1006420200049966749898643 := by
  unfold tailWord_5879989
  simp only [CollatzResearch.WordTrace]
  refine ⟨214460817494811550016099021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142973878329874366677399347 214460817494811550016099021)
  ·
    refine ⟨80422806560554331256037133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214460817494811550016099021 80422806560554331256037133)
    ·
      refine ⟨30158552460207874221013925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80422806560554331256037133 30158552460207874221013925)
      ·
        refine ⟨5654728586288976416440111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30158552460207874221013925 5654728586288976416440111)
        ·
          refine ⟨8482092879433464624660167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5654728586288976416440111 8482092879433464624660167)
          ·
            refine ⟨12723139319150196936990251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8482092879433464624660167 12723139319150196936990251)
            ·
              refine ⟨19084708978725295405485377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12723139319150196936990251 19084708978725295405485377)
              ·
                refine ⟨14313531734043971554114033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19084708978725295405485377 14313531734043971554114033)
                ·
                  refine ⟨10735148800532978665585525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14313531734043971554114033 10735148800532978665585525)
                  ·
                    refine ⟨1006420200049966749898643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10735148800532978665585525 1006420200049966749898643)
                    ·
                      rfl

theorem cell23_5879989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_5879989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5879989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5879989 prefixEnd_5879989 := by exact prefixLift 5879989
  have htrace : WordTrace (prefixWord ++ tailWord_5879989) baseStart_5879989 baseEnd_5879989 := by
    simpa [prefixWord, tailWord_5879989, baseEnd_5879989] using wordTrace_append hprefix tailTrace_5879989
  have hstable : (prefixWord ++ tailWord_5879989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5879989).length < 2 ^ (prefixWord ++ tailWord_5879989).sum := by decide
  have hdescent : baseEnd_5879989 < baseStart_5879989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5879989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880015 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 6]
def baseStart_5880015 : Nat := 118140960795 + 5880015 * 2 ^ 59
def prefixEnd_5880015 : Nat := 4983230072969 + 3 ^ 40 * 5880015 * 2
def baseEnd_5880015 : Nat := 335474883405213016441201

theorem tailTrace_5880015 : CollatzResearch.WordTrace tailWord_5880015 prefixEnd_5880015 335474883405213016441201 := by
  unfold tailWord_5880015
  simp only [CollatzResearch.WordTrace]
  refine ⟨214461765792717356456545499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142974510528478237637696999 214461765792717356456545499)
  ·
    refine ⟨321692648689076034684818249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214461765792717356456545499 321692648689076034684818249)
    ·
      refine ⟨241269486516807026013613687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321692648689076034684818249 241269486516807026013613687)
      ·
        refine ⟨361904229775210539020420531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241269486516807026013613687 361904229775210539020420531)
        ·
          refine ⟨542856344662815808530630797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361904229775210539020420531 542856344662815808530630797)
          ·
            refine ⟨203571129248555928198986549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 542856344662815808530630797 203571129248555928198986549)
            ·
              refine ⟨19084793367052118268654989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203571129248555928198986549 19084793367052118268654989)
              ·
                refine ⟨7156797512644544350745621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19084793367052118268654989 7156797512644544350745621)
                ·
                  refine ⟨335474883405213016441201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7156797512644544350745621 335474883405213016441201)
                  ·
                    rfl

theorem cell23_5880015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 6].length) (baseStart_5880015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880015 prefixEnd_5880015 := by exact prefixLift 5880015
  have htrace : WordTrace (prefixWord ++ tailWord_5880015) baseStart_5880015 baseEnd_5880015 := by
    simpa [prefixWord, tailWord_5880015, baseEnd_5880015] using wordTrace_append hprefix tailTrace_5880015
  have hstable : (prefixWord ++ tailWord_5880015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880015).length < 2 ^ (prefixWord ++ tailWord_5880015).sum := by decide
  have hdescent : baseEnd_5880015 < baseStart_5880015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880025 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 3]
def baseStart_5880025 : Nat := 118140960795 + 5880025 * 2 ^ 59
def prefixEnd_5880025 : Nat := 4983230072969 + 3 ^ 40 * 5880025 * 2
def baseEnd_5880025 : Nat := 3019279085453462108845763

theorem tailTrace_5880025 : CollatzResearch.WordTrace tailWord_5880025 prefixEnd_5880025 3019279085453462108845763 := by
  unfold tailWord_5880025
  simp only [CollatzResearch.WordTrace]
  refine ⟨214462130522681128164409529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142974753681787418776273019 214462130522681128164409529)
  ·
    refine ⟨160846597892010846123307147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214462130522681128164409529 160846597892010846123307147)
    ·
      refine ⟨241269896838016269184960721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160846597892010846123307147 241269896838016269184960721)
      ·
        refine ⟨180952422628512201888720541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241269896838016269184960721 180952422628512201888720541)
        ·
          refine ⟨67857158485692075708270203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180952422628512201888720541 67857158485692075708270203)
          ·
            refine ⟨101785737728538113562405305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67857158485692075708270203 101785737728538113562405305)
            ·
              refine ⟨76339303296403585171803979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101785737728538113562405305 76339303296403585171803979)
              ·
                refine ⟨114508954944605377757705969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76339303296403585171803979 114508954944605377757705969)
                ·
                  refine ⟨85881716208454033318279477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114508954944605377757705969 85881716208454033318279477)
                  ·
                    refine ⟨8051410894542565623588701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85881716208454033318279477 8051410894542565623588701)
                    ·
                      refine ⟨3019279085453462108845763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8051410894542565623588701 3019279085453462108845763)
                      ·
                        rfl

theorem cell23_5880025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_5880025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880025 prefixEnd_5880025 := by exact prefixLift 5880025
  have htrace : WordTrace (prefixWord ++ tailWord_5880025) baseStart_5880025 baseEnd_5880025 := by
    simpa [prefixWord, tailWord_5880025, baseEnd_5880025] using wordTrace_append hprefix tailTrace_5880025
  have hstable : (prefixWord ++ tailWord_5880025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880025).length < 2 ^ (prefixWord ++ tailWord_5880025).sum := by decide
  have hdescent : baseEnd_5880025 < baseStart_5880025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880029 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5880029 : Nat := 118140960795 + 5880029 * 2 ^ 59
def prefixEnd_5880029 : Nat := 4983230072969 + 3 ^ 40 * 5880029 * 2
def baseEnd_5880029 : Nat := 3019281139376080093195745

theorem tailTrace_5880029 : CollatzResearch.WordTrace tailWord_5880029 prefixEnd_5880029 3019281139376080093195745 := by
  unfold tailWord_5880029
  simp only [CollatzResearch.WordTrace]
  refine ⟨214462276414666636847555141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142974850943111091231703427 214462276414666636847555141)
  ·
    refine ⟨40211676827749994408916589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214462276414666636847555141 40211676827749994408916589)
    ·
      refine ⟨15079378810406247903343721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40211676827749994408916589 15079378810406247903343721)
      ·
        refine ⟨11309534107804685927507791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15079378810406247903343721 11309534107804685927507791)
        ·
          refine ⟨16964301161707028891261687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309534107804685927507791 16964301161707028891261687)
          ·
            refine ⟨25446451742560543336892531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16964301161707028891261687 25446451742560543336892531)
            ·
              refine ⟨38169677613840815005338797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25446451742560543336892531 38169677613840815005338797)
              ·
                refine ⟨14313629105190305627002049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38169677613840815005338797 14313629105190305627002049)
                ·
                  refine ⟨10735221828892729220251537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14313629105190305627002049 10735221828892729220251537)
                  ·
                    refine ⟨8051416371669546915188653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10735221828892729220251537 8051416371669546915188653)
                    ·
                      refine ⟨3019281139376080093195745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8051416371669546915188653 3019281139376080093195745)
                      ·
                        rfl

theorem cell23_5880029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5880029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880029 prefixEnd_5880029 := by exact prefixLift 5880029
  have htrace : WordTrace (prefixWord ++ tailWord_5880029) baseStart_5880029 baseEnd_5880029 := by
    simpa [prefixWord, tailWord_5880029, baseEnd_5880029] using wordTrace_append hprefix tailTrace_5880029
  have hstable : (prefixWord ++ tailWord_5880029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880029).length < 2 ^ (prefixWord ++ tailWord_5880029).sum := by decide
  have hdescent : baseEnd_5880029 < baseStart_5880029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880062 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_5880062 : Nat := 118140960795 + 5880062 * 2 ^ 59
def prefixEnd_5880062 : Nat := 4983230072969 + 3 ^ 40 * 5880062 * 2
def baseEnd_5880062 : Nat := 1006432694745892821361031

theorem tailTrace_5880062 : CollatzResearch.WordTrace tailWord_5880062 prefixEnd_5880062 1006432694745892821361031 := by
  unfold tailWord_5880062
  simp only [CollatzResearch.WordTrace]
  refine ⟨26807935002943385435438305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142975653349031388989004293 26807935002943385435438305)
  ·
    refine ⟨20105951252207539076578729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26807935002943385435438305 20105951252207539076578729)
    ·
      refine ⟨15079463439155654307434047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20105951252207539076578729 15079463439155654307434047)
      ·
        refine ⟨22619195158733481461151071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15079463439155654307434047 22619195158733481461151071)
        ·
          refine ⟨33928792738100222191726607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22619195158733481461151071 33928792738100222191726607)
          ·
            refine ⟨50893189107150333287589911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33928792738100222191726607 50893189107150333287589911)
            ·
              refine ⟨76339783660725499931384867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50893189107150333287589911 76339783660725499931384867)
              ·
                refine ⟨114509675491088249897077301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76339783660725499931384867 114509675491088249897077301)
                ·
                  refine ⟨10735282077289523427850997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114509675491088249897077301 10735282077289523427850997)
                  ·
                    refine ⟨1006432694745892821361031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10735282077289523427850997 1006432694745892821361031)
                    ·
                      rfl

theorem cell23_5880062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_5880062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880062 prefixEnd_5880062 := by exact prefixLift 5880062
  have htrace : WordTrace (prefixWord ++ tailWord_5880062) baseStart_5880062 baseEnd_5880062 := by
    simpa [prefixWord, tailWord_5880062, baseEnd_5880062] using wordTrace_append hprefix tailTrace_5880062
  have hstable : (prefixWord ++ tailWord_5880062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880062).length < 2 ^ (prefixWord ++ tailWord_5880062).sum := by decide
  have hdescent : baseEnd_5880062 < baseStart_5880062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880092 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_5880092 : Nat := 118140960795 + 5880092 * 2 ^ 59
def prefixEnd_5880092 : Nat := 4983230072969 + 3 ^ 40 * 5880092 * 2
def baseEnd_5880092 : Nat := 1006437829552437782235985

theorem tailTrace_5880092 : CollatzResearch.WordTrace tailWord_5880092 prefixEnd_5880092 1006437829552437782235985 := by
  unfold tailWord_5880092
  simp only [CollatzResearch.WordTrace]
  refine ⟨107232287106719199303549265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142976382808958932404732353 107232287106719199303549265)
  ·
    refine ⟨80424215330039399477661949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107232287106719199303549265 80424215330039399477661949)
    ·
      refine ⟨30159080748764774804123231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80424215330039399477661949 30159080748764774804123231)
      ·
        refine ⟨45238621123147162206184847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30159080748764774804123231 45238621123147162206184847)
        ·
          refine ⟨67857931684720743309277271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45238621123147162206184847 67857931684720743309277271)
          ·
            refine ⟨101786897527081114963915907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67857931684720743309277271 101786897527081114963915907)
            ·
              refine ⟨152680346290621672445873861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101786897527081114963915907 152680346290621672445873861)
              ·
                refine ⟨28627564929491563583601349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152680346290621672445873861 28627564929491563583601349)
                ·
                  refine ⟨5367668424279668171925253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28627564929491563583601349 5367668424279668171925253)
                  ·
                    refine ⟨1006437829552437782235985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5367668424279668171925253 1006437829552437782235985)
                    ·
                      rfl

theorem cell23_5880092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_5880092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880092 prefixEnd_5880092 := by exact prefixLift 5880092
  have htrace : WordTrace (prefixWord ++ tailWord_5880092) baseStart_5880092 baseEnd_5880092 := by
    simpa [prefixWord, tailWord_5880092, baseEnd_5880092] using wordTrace_append hprefix tailTrace_5880092
  have hstable : (prefixWord ++ tailWord_5880092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880092).length < 2 ^ (prefixWord ++ tailWord_5880092).sum := by decide
  have hdescent : baseEnd_5880092 < baseStart_5880092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880096 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 1, 5]
def baseStart_5880096 : Nat := 118140960795 + 5880096 * 2 ^ 59
def prefixEnd_5880096 : Nat := 4983230072969 + 3 ^ 40 * 5880096 * 2
def baseEnd_5880096 : Nat := 1006438514193310443685979

theorem tailTrace_5880096 : CollatzResearch.WordTrace tailWord_5880096 prefixEnd_5880096 1006438514193310443685979 := by
  unfold tailWord_5880096
  simp only [CollatzResearch.WordTrace]
  refine ⟨107232360052711953645122071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142976480070282604860162761 107232360052711953645122071)
  ·
    refine ⟨160848540079067930467683107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107232360052711953645122071 160848540079067930467683107)
    ·
      refine ⟨241272810118601895701524661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160848540079067930467683107 241272810118601895701524661)
      ·
        refine ⟨22619325948618927722017937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241272810118601895701524661 22619325948618927722017937)
        ·
          refine ⟨16964494461464195791513453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22619325948618927722017937 16964494461464195791513453)
          ·
            refine ⟨6361685423049073421817545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16964494461464195791513453 6361685423049073421817545)
            ·
              refine ⟨4771264067286805066363159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6361685423049073421817545 4771264067286805066363159)
              ·
                refine ⟨7156896100930207599544739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4771264067286805066363159 7156896100930207599544739)
                ·
                  refine ⟨10735344151395311399317109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7156896100930207599544739 10735344151395311399317109)
                  ·
                    refine ⟨1006438514193310443685979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10735344151395311399317109 1006438514193310443685979)
                    ·
                      rfl

theorem cell23_5880096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 5].length) (baseStart_5880096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880096 prefixEnd_5880096 := by exact prefixLift 5880096
  have htrace : WordTrace (prefixWord ++ tailWord_5880096) baseStart_5880096 baseEnd_5880096 := by
    simpa [prefixWord, tailWord_5880096, baseEnd_5880096] using wordTrace_append hprefix tailTrace_5880096
  have hstable : (prefixWord ++ tailWord_5880096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880096).length < 2 ^ (prefixWord ++ tailWord_5880096).sum := by decide
  have hdescent : baseEnd_5880096 < baseStart_5880096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880099 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 5, 2, 2]
def baseStart_5880099 : Nat := 118140960795 + 5880099 * 2 ^ 59
def prefixEnd_5880099 : Nat := 4983230072969 + 3 ^ 40 * 5880099 * 2
def baseEnd_5880099 : Nat := 3019317083021894819320423

theorem tailTrace_5880099 : CollatzResearch.WordTrace tailWord_5880099 prefixEnd_5880099 3019317083021894819320423 := by
  unfold tailWord_5880099
  simp only [CollatzResearch.WordTrace]
  refine ⟨214464829524413038802603351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142976553016275359201735567 214464829524413038802603351)
  ·
    refine ⟨321697244286619558203905027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214464829524413038802603351 321697244286619558203905027)
    ·
      refine ⟨482545866429929337305857541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321697244286619558203905027 482545866429929337305857541)
      ·
        refine ⟨90477349955611750744848289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 482545866429929337305857541 90477349955611750744848289)
        ·
          refine ⟨67858012466708813058636217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90477349955611750744848289 67858012466708813058636217)
          ·
            refine ⟨50893509350031609793977163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67858012466708813058636217 50893509350031609793977163)
            ·
              refine ⟨76340264025047414690965745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50893509350031609793977163 76340264025047414690965745)
              ·
                refine ⟨57255198018785561018224309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76340264025047414690965745 57255198018785561018224309)
                ·
                  refine ⟨5367674814261146345458529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57255198018785561018224309 5367674814261146345458529)
                  ·
                    refine ⟨4025756110695859759093897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5367674814261146345458529 4025756110695859759093897)
                    ·
                      refine ⟨3019317083021894819320423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025756110695859759093897 3019317083021894819320423)
                      ·
                        rfl

theorem cell23_5880099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_5880099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880099 prefixEnd_5880099 := by exact prefixLift 5880099
  have htrace : WordTrace (prefixWord ++ tailWord_5880099) baseStart_5880099 baseEnd_5880099 := by
    simpa [prefixWord, tailWord_5880099, baseEnd_5880099] using wordTrace_append hprefix tailTrace_5880099
  have hstable : (prefixWord ++ tailWord_5880099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880099).length < 2 ^ (prefixWord ++ tailWord_5880099).sum := by decide
  have hdescent : baseEnd_5880099 < baseStart_5880099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880129 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5880129 : Nat := 118140960795 + 5880129 * 2 ^ 59
def prefixEnd_5880129 : Nat := 4983230072969 + 3 ^ 40 * 5880129 * 2
def baseEnd_5880129 : Nat := 3019332487441529701945285

theorem tailTrace_5880129 : CollatzResearch.WordTrace tailWord_5880129 prefixEnd_5880129 3019332487441529701945285 := by
  unfold tailWord_5880129
  simp only [CollatzResearch.WordTrace]
  refine ⟨214465923714304353926195441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142977282476202902617463627 214465923714304353926195441)
  ·
    refine ⟨160849442785728265444646581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214465923714304353926195441 160849442785728265444646581)
    ·
      refine ⟨15079635261162024885435617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160849442785728265444646581 15079635261162024885435617)
      ·
        refine ⟨11309726445871518664076713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15079635261162024885435617 11309726445871518664076713)
        ·
          refine ⟨8482294834403638998057535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11309726445871518664076713 8482294834403638998057535)
          ·
            refine ⟨12723442251605458497086303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8482294834403638998057535 12723442251605458497086303)
            ·
              refine ⟨19085163377408187745629455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12723442251605458497086303 19085163377408187745629455)
              ·
                refine ⟨28627745066112281618444183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19085163377408187745629455 28627745066112281618444183)
                ·
                  refine ⟨42941617599168422427666275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28627745066112281618444183 42941617599168422427666275)
                  ·
                    refine ⟨64412426398752633641499413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42941617599168422427666275 64412426398752633641499413)
                    ·
                      refine ⟨3019332487441529701945285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64412426398752633641499413 3019332487441529701945285)
                      ·
                        rfl

theorem cell23_5880129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5880129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880129 prefixEnd_5880129 := by exact prefixLift 5880129
  have htrace : WordTrace (prefixWord ++ tailWord_5880129) baseStart_5880129 baseEnd_5880129 := by
    simpa [prefixWord, tailWord_5880129, baseEnd_5880129] using wordTrace_append hprefix tailTrace_5880129
  have hstable : (prefixWord ++ tailWord_5880129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880129).length < 2 ^ (prefixWord ++ tailWord_5880129).sum := by decide
  have hdescent : baseEnd_5880129 < baseStart_5880129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880156 : List Nat := [2, 2, 4, 3, 2, 1, 9]
def baseStart_5880156 : Nat := 118140960795 + 5880156 * 2 ^ 59
def prefixEnd_5880156 : Nat := 4983230072969 + 3 ^ 40 * 5880156 * 2
def baseEnd_5880156 : Nat := 37275880881718532053181

theorem tailTrace_5880156 : CollatzResearch.WordTrace tailWord_5880156 prefixEnd_5880156 37275880881718532053181 := by
  unfold tailWord_5880156
  simp only [CollatzResearch.WordTrace]
  refine ⟨107233454242603268768714161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142977938990137691691618881 107233454242603268768714161)
  ·
    refine ⟨80425090681952451576535621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107233454242603268768714161 80425090681952451576535621)
    ·
      refine ⟨15079704502866084670600429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80425090681952451576535621 15079704502866084670600429)
      ·
        refine ⟨5654889188574781751475161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15079704502866084670600429 5654889188574781751475161)
        ·
          refine ⟨4241166891431086313606371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5654889188574781751475161 4241166891431086313606371)
          ·
            refine ⟨6361750337146629470409557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4241166891431086313606371 6361750337146629470409557)
            ·
              refine ⟨37275880881718532053181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6361750337146629470409557 37275880881718532053181)
              ·
                rfl

theorem cell23_5880156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 9].length) (baseStart_5880156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880156 prefixEnd_5880156 := by exact prefixLift 5880156
  have htrace : WordTrace (prefixWord ++ tailWord_5880156) baseStart_5880156 baseEnd_5880156 := by
    simpa [prefixWord, tailWord_5880156, baseEnd_5880156] using wordTrace_append hprefix tailTrace_5880156
  have hstable : (prefixWord ++ tailWord_5880156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880156).length < 2 ^ (prefixWord ++ tailWord_5880156).sum := by decide
  have hdescent : baseEnd_5880156 < baseStart_5880156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880193 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_5880193 : Nat := 118140960795 + 5880193 * 2 ^ 59
def prefixEnd_5880193 : Nat := 4983230072969 + 3 ^ 40 * 5880193 * 2
def baseEnd_5880193 : Nat := 3019365350203417451544991

theorem tailTrace_5880193 : CollatzResearch.WordTrace tailWord_5880193 prefixEnd_5880193 3019365350203417451544991 := by
  unfold tailWord_5880193
  simp only [CollatzResearch.WordTrace]
  refine ⟨214468257986072492856525233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142978838657381661904350155 214468257986072492856525233)
  ·
    refine ⟨160851193489554369642393925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214468257986072492856525233 160851193489554369642393925)
    ·
      refine ⟨30159598779291444307948861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160851193489554369642393925 30159598779291444307948861)
      ·
        refine ⟨11309849542234291615480823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30159598779291444307948861 11309849542234291615480823)
        ·
          refine ⟨16964774313351437423221235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309849542234291615480823 16964774313351437423221235)
          ·
            refine ⟨25447161470027156134831853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16964774313351437423221235 25447161470027156134831853)
            ·
              refine ⟨9542685551260183550561945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25447161470027156134831853 9542685551260183550561945)
              ·
                refine ⟨7157014163445137662921459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9542685551260183550561945 7157014163445137662921459)
                ·
                  refine ⟨10735521245167706494382189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7157014163445137662921459 10735521245167706494382189)
                  ·
                    refine ⟨4025820466937889935393321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10735521245167706494382189 4025820466937889935393321)
                    ·
                      refine ⟨3019365350203417451544991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025820466937889935393321 3019365350203417451544991)
                      ·
                        rfl

theorem cell23_5880193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_5880193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880193 prefixEnd_5880193 := by exact prefixLift 5880193
  have htrace : WordTrace (prefixWord ++ tailWord_5880193) baseStart_5880193 baseEnd_5880193 := by
    simpa [prefixWord, tailWord_5880193, baseEnd_5880193] using wordTrace_append hprefix tailTrace_5880193
  have hstable : (prefixWord ++ tailWord_5880193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880193).length < 2 ^ (prefixWord ++ tailWord_5880193).sum := by decide
  have hdescent : baseEnd_5880193 < baseStart_5880193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880206 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5880206 : Nat := 118140960795 + 5880206 * 2 ^ 59
def prefixEnd_5880206 : Nat := 4983230072969 + 3 ^ 40 * 5880206 * 2
def baseEnd_5880206 : Nat := 3019372025451925900682431

theorem tailTrace_5880206 : CollatzResearch.WordTrace tailWord_5880206 prefixEnd_5880206 3019372025451925900682431 := by
  unfold tailWord_5880206
  simp only [CollatzResearch.WordTrace]
  refine ⟨26808591516878174509593559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142979154756683597384498981 26808591516878174509593559)
  ·
    refine ⟨40212887275317261764390339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26808591516878174509593559 40212887275317261764390339)
    ·
      refine ⟨60319330912975892646585509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40212887275317261764390339 60319330912975892646585509)
      ·
        refine ⟨11309874546182979871234783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60319330912975892646585509 11309874546182979871234783)
        ·
          refine ⟨16964811819274469806852175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309874546182979871234783 16964811819274469806852175)
          ·
            refine ⟨25447217728911704710278263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16964811819274469806852175 25447217728911704710278263)
            ·
              refine ⟨38170826593367557065417395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25447217728911704710278263 38170826593367557065417395)
              ·
                refine ⟨57256239890051335598126093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38170826593367557065417395 57256239890051335598126093)
                ·
                  refine ⟨21471089958769250849297285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57256239890051335598126093 21471089958769250849297285)
                  ·
                    refine ⟨4025829367269234534243241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21471089958769250849297285 4025829367269234534243241)
                    ·
                      refine ⟨3019372025451925900682431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025829367269234534243241 3019372025451925900682431)
                      ·
                        rfl

theorem cell23_5880206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5880206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880206 prefixEnd_5880206 := by exact prefixLift 5880206
  have htrace : WordTrace (prefixWord ++ tailWord_5880206) baseStart_5880206 baseEnd_5880206 := by
    simpa [prefixWord, tailWord_5880206, baseEnd_5880206] using wordTrace_append hprefix tailTrace_5880206
  have hstable : (prefixWord ++ tailWord_5880206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880206).length < 2 ^ (prefixWord ++ tailWord_5880206).sum := by decide
  have hdescent : baseEnd_5880206 < baseStart_5880206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880223 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 2, 2, 2]
def baseStart_5880223 : Nat := 118140960795 + 5880223 * 2 ^ 59
def prefixEnd_5880223 : Nat := 4983230072969 + 3 ^ 40 * 5880223 * 2
def baseEnd_5880223 : Nat := 3019380754623052334169853

theorem tailTrace_5880223 : CollatzResearch.WordTrace tailWord_5880223 prefixEnd_5880223 3019380754623052334169853 := by
  unfold tailWord_5880223
  simp only [CollatzResearch.WordTrace]
  refine ⟨214469352175963807980117323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142979568117309205320078215 214469352175963807980117323)
  ·
    refine ⟨321704028263945711970175985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214469352175963807980117323 321704028263945711970175985)
    ·
      refine ⟨241278021197959283977631989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321704028263945711970175985 241278021197959283977631989)
      ·
        refine ⟨22619814487308682872902999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241278021197959283977631989 22619814487308682872902999)
        ·
          refine ⟨33929721730963024309354499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22619814487308682872902999 33929721730963024309354499)
          ·
            refine ⟨50894582596444536464031749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33929721730963024309354499 50894582596444536464031749)
            ·
              refine ⟨9542734236833350587005953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50894582596444536464031749 9542734236833350587005953)
              ·
                refine ⟨7157050677625012940254465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9542734236833350587005953 7157050677625012940254465)
                ·
                  refine ⟨5367788008218759705190849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7157050677625012940254465 5367788008218759705190849)
                  ·
                    refine ⟨4025841006164069778893137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5367788008218759705190849 4025841006164069778893137)
                    ·
                      refine ⟨3019380754623052334169853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025841006164069778893137 3019380754623052334169853)
                      ·
                        rfl

theorem cell23_5880223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_5880223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880223 prefixEnd_5880223 := by exact prefixLift 5880223
  have htrace : WordTrace (prefixWord ++ tailWord_5880223) baseStart_5880223 baseEnd_5880223 := by
    simpa [prefixWord, tailWord_5880223, baseEnd_5880223] using wordTrace_append hprefix tailTrace_5880223
  have hstable : (prefixWord ++ tailWord_5880223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880223).length < 2 ^ (prefixWord ++ tailWord_5880223).sum := by decide
  have hdescent : baseEnd_5880223 < baseStart_5880223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880229 : List Nat := [1, 3, 1, 2, 1, 1, 5, 4, 5]
def baseStart_5880229 : Nat := 118140960795 + 5880229 * 2 ^ 59
def prefixEnd_5880229 : Nat := 4983230072969 + 3 ^ 40 * 5880229 * 2
def baseEnd_5880229 : Nat := 335487092834108812299425

theorem tailTrace_5880229 : CollatzResearch.WordTrace tailWord_5880229 prefixEnd_5880229 335487092834108812299425 := by
  unfold tailWord_5880229
  simp only [CollatzResearch.WordTrace]
  refine ⟨214469571013942071004835741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142979714009294714003223827 214469571013942071004835741)
  ·
    refine ⟨80426089130228276626813403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214469571013942071004835741 80426089130228276626813403)
    ·
      refine ⟨120639133695342414940220105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80426089130228276626813403 120639133695342414940220105)
      ·
        refine ⟨90479350271506811205165079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120639133695342414940220105 90479350271506811205165079)
        ·
          refine ⟨135719025407260216807747619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90479350271506811205165079 135719025407260216807747619)
          ·
            refine ⟨203578538110890325211621429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135719025407260216807747619 203578538110890325211621429)
            ·
              refine ⟨19085487947895967988589509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203578538110890325211621429 19085487947895967988589509)
              ·
                refine ⟨3578528990230493997860533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19085487947895967988589509 3578528990230493997860533)
                ·
                  refine ⟨335487092834108812299425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3578528990230493997860533 335487092834108812299425)
                  ·
                    rfl

theorem cell23_5880229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_5880229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880229 prefixEnd_5880229 := by exact prefixLift 5880229
  have htrace : WordTrace (prefixWord ++ tailWord_5880229) baseStart_5880229 baseEnd_5880229 := by
    simpa [prefixWord, tailWord_5880229, baseEnd_5880229] using wordTrace_append hprefix tailTrace_5880229
  have hstable : (prefixWord ++ tailWord_5880229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880229).length < 2 ^ (prefixWord ++ tailWord_5880229).sum := by decide
  have hdescent : baseEnd_5880229 < baseStart_5880229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880242 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_5880242 : Nat := 118140960795 + 5880242 * 2 ^ 59
def prefixEnd_5880242 : Nat := 4983230072969 + 3 ^ 40 * 5880242 * 2
def baseEnd_5880242 : Nat := 1006463503585162586610755

theorem tailTrace_5880242 : CollatzResearch.WordTrace tailWord_5880242 prefixEnd_5880242 1006463503585162586610755 := by
  unfold tailWord_5880242
  simp only [CollatzResearch.WordTrace]
  refine ⟨53617511290723743556264745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142980030108596649483372653 53617511290723743556264745)
  ·
    refine ⟨40213133468042807667198559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53617511290723743556264745 40213133468042807667198559)
    ·
      refine ⟨60319700202064211500797839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40213133468042807667198559 60319700202064211500797839)
      ·
        refine ⟨90479550303096317251196759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60319700202064211500797839 90479550303096317251196759)
        ·
          refine ⟨135719325454644475876795139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90479550303096317251196759 135719325454644475876795139)
          ·
            refine ⟨203578988181966713815192709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135719325454644475876795139 203578988181966713815192709)
            ·
              refine ⟨38171060284118758840348633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203578988181966713815192709 38171060284118758840348633)
              ·
                refine ⟨28628295213089069130261475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38171060284118758840348633 28628295213089069130261475)
                ·
                  refine ⟨42942442819633603695392213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28628295213089069130261475 42942442819633603695392213)
                  ·
                    refine ⟨1006463503585162586610755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42942442819633603695392213 1006463503585162586610755)
                    ·
                      rfl

theorem cell23_5880242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_5880242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880242 prefixEnd_5880242 := by exact prefixLift 5880242
  have htrace : WordTrace (prefixWord ++ tailWord_5880242) baseStart_5880242 baseEnd_5880242 := by
    simpa [prefixWord, tailWord_5880242, baseEnd_5880242] using wordTrace_append hprefix tailTrace_5880242
  have hstable : (prefixWord ++ tailWord_5880242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880242).length < 2 ^ (prefixWord ++ tailWord_5880242).sum := by decide
  have hdescent : baseEnd_5880242 < baseStart_5880242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880274 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_5880274 : Nat := 118140960795 + 5880274 * 2 ^ 59
def prefixEnd_5880274 : Nat := 4983230072969 + 3 ^ 40 * 5880274 * 2
def baseEnd_5880274 : Nat := 3019406942136431634632119

theorem tailTrace_5880274 : CollatzResearch.WordTrace tailWord_5880274 prefixEnd_5880274 3019406942136431634632119 := by
  unfold tailWord_5880274
  simp only [CollatzResearch.WordTrace]
  refine ⟨53617803074694760922555969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142980808199186029126815917 53617803074694760922555969)
  ·
    refine ⟨40213352306021070691916977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53617803074694760922555969 40213352306021070691916977)
    ·
      refine ⟨30160014229515803018937733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40213352306021070691916977 30160014229515803018937733)
      ·
        refine ⟨5655002668034213066050825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30160014229515803018937733 5655002668034213066050825)
        ·
          refine ⟨4241252001025659799538119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5655002668034213066050825 4241252001025659799538119)
          ·
            refine ⟨6361878001538489699307179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4241252001025659799538119 6361878001538489699307179)
            ·
              refine ⟨9542817002307734548960769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361878001538489699307179 9542817002307734548960769)
              ·
                refine ⟨7157112751730800911720577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9542817002307734548960769 7157112751730800911720577)
                ·
                  refine ⟨5367834563798100683790433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7157112751730800911720577 5367834563798100683790433)
                  ·
                    refine ⟨4025875922848575512842825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5367834563798100683790433 4025875922848575512842825)
                    ·
                      refine ⟨3019406942136431634632119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025875922848575512842825 3019406942136431634632119)
                      ·
                        rfl

theorem cell23_5880274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_5880274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880274 prefixEnd_5880274 := by exact prefixLift 5880274
  have htrace : WordTrace (prefixWord ++ tailWord_5880274) baseStart_5880274 baseEnd_5880274 := by
    simpa [prefixWord, tailWord_5880274, baseEnd_5880274] using wordTrace_append hprefix tailTrace_5880274
  have hstable : (prefixWord ++ tailWord_5880274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880274).length < 2 ^ (prefixWord ++ tailWord_5880274).sum := by decide
  have hdescent : baseEnd_5880274 < baseStart_5880274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880296 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_5880296 : Nat := 118140960795 + 5880296 * 2 ^ 59
def prefixEnd_5880296 : Nat := 4983230072969 + 3 ^ 40 * 5880296 * 2
def baseEnd_5880296 : Nat := 3019418238710830548557017

theorem tailTrace_5880296 : CollatzResearch.WordTrace tailWord_5880296 prefixEnd_5880296 3019418238710830548557017 := by
  unfold tailWord_5880296
  simp only [CollatzResearch.WordTrace]
  refine ⟨107236007352349670723762371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142981343136466227631683161 107236007352349670723762371)
  ·
    refine ⟨160854011028524506085643557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107236007352349670723762371 160854011028524506085643557)
    ·
      refine ⟨30160127067848344891058167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160854011028524506085643557 30160127067848344891058167)
      ·
        refine ⟨45240190601772517336587251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30160127067848344891058167 45240190601772517336587251)
        ·
          refine ⟨67860285902658776004880877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45240190601772517336587251 67860285902658776004880877)
          ·
            refine ⟨25447607213497041001830329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67860285902658776004880877 25447607213497041001830329)
            ·
              refine ⟨19085705410122780751372747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25447607213497041001830329 19085705410122780751372747)
              ·
                refine ⟨28628558115184171127059121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19085705410122780751372747 28628558115184171127059121)
                ·
                  refine ⟨21471418586388128345294341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28628558115184171127059121 21471418586388128345294341)
                  ·
                    refine ⟨4025890984947774064742689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21471418586388128345294341 4025890984947774064742689)
                    ·
                      refine ⟨3019418238710830548557017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025890984947774064742689 3019418238710830548557017)
                      ·
                        rfl

theorem cell23_5880296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_5880296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880296 prefixEnd_5880296 := by exact prefixLift 5880296
  have htrace : WordTrace (prefixWord ++ tailWord_5880296) baseStart_5880296 baseEnd_5880296 := by
    simpa [prefixWord, tailWord_5880296, baseEnd_5880296] using wordTrace_append hprefix tailTrace_5880296
  have hstable : (prefixWord ++ tailWord_5880296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880296).length < 2 ^ (prefixWord ++ tailWord_5880296).sum := by decide
  have hdescent : baseEnd_5880296 < baseStart_5880296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880340 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5880340 : Nat := 118140960795 + 5880340 * 2 ^ 59
def prefixEnd_5880340 : Nat := 4983230072969 + 3 ^ 40 * 5880340 * 2
def baseEnd_5880340 : Nat := 1006480277286542792135605

theorem tailTrace_5880340 : CollatzResearch.WordTrace tailWord_5880340 prefixEnd_5880340 1006480277286542792135605 := by
  unfold tailWord_5880340
  simp only [CollatzResearch.WordTrace]
  refine ⟨107236809758269968481063237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142982413011026624641417649 107236809758269968481063237)
  ·
    refine ⟨20106901829675619090199357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107236809758269968481063237 20106901829675619090199357)
    ·
      refine ⟨7540088186128357158824759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20106901829675619090199357 7540088186128357158824759)
      ·
        refine ⟨11310132279192535738237139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7540088186128357158824759 11310132279192535738237139)
        ·
          refine ⟨16965198418788803607355709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11310132279192535738237139 16965198418788803607355709)
          ·
            refine ⟨6361949407045801352758391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16965198418788803607355709 6361949407045801352758391)
            ·
              refine ⟨9542924110568702029137587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361949407045801352758391 9542924110568702029137587)
              ·
                refine ⟨14314386165853053043706381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9542924110568702029137587 14314386165853053043706381)
                ·
                  refine ⟨5367894812194894891389893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14314386165853053043706381 5367894812194894891389893)
                  ·
                    refine ⟨1006480277286542792135605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5367894812194894891389893 1006480277286542792135605)
                    ·
                      rfl

theorem cell23_5880340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5880340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880340 prefixEnd_5880340 := by exact prefixLift 5880340
  have htrace : WordTrace (prefixWord ++ tailWord_5880340) baseStart_5880340 baseEnd_5880340 := by
    simpa [prefixWord, tailWord_5880340, baseEnd_5880340] using wordTrace_append hprefix tailTrace_5880340
  have hstable : (prefixWord ++ tailWord_5880340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880340).length < 2 ^ (prefixWord ++ tailWord_5880340).sum := by decide
  have hdescent : baseEnd_5880340 < baseStart_5880340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880373 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_5880373 : Nat := 118140960795 + 5880373 * 2 ^ 59
def prefixEnd_5880373 : Nat := 4983230072969 + 3 ^ 40 * 5880373 * 2
def baseEnd_5880373 : Nat := 3019457776721226747294163

theorem tailTrace_5880373 : CollatzResearch.WordTrace tailWord_5880373 prefixEnd_5880373 3019457776721226747294163 := by
  unfold tailWord_5880373
  simp only [CollatzResearch.WordTrace]
  refine ⟨214474823125420383598077773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142983215416946922398718515 214474823125420383598077773)
  ·
    refine ⟨80428058672032643849279165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214474823125420383598077773 80428058672032643849279165)
    ·
      refine ⟨30160522002012241443479687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80428058672032643849279165 30160522002012241443479687)
      ·
        refine ⟨45240783003018362165219531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30160522002012241443479687 45240783003018362165219531)
        ·
          refine ⟨67861174504527543247829297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45240783003018362165219531 67861174504527543247829297)
          ·
            refine ⟨50895880878395657435871973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67861174504527543247829297 50895880878395657435871973)
            ·
              refine ⟨9542977664699185769225995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50895880878395657435871973 9542977664699185769225995)
              ·
                refine ⟨14314466497048778653838993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9542977664699185769225995 14314466497048778653838993)
                ·
                  refine ⟨10735849872786583990379245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14314466497048778653838993 10735849872786583990379245)
                  ·
                    refine ⟨4025943702294968996392217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10735849872786583990379245 4025943702294968996392217)
                    ·
                      refine ⟨3019457776721226747294163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4025943702294968996392217 3019457776721226747294163)
                      ·
                        rfl

theorem cell23_5880373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_5880373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880373 prefixEnd_5880373 := by exact prefixLift 5880373
  have htrace : WordTrace (prefixWord ++ tailWord_5880373) baseStart_5880373 baseEnd_5880373 := by
    simpa [prefixWord, tailWord_5880373, baseEnd_5880373] using wordTrace_append hprefix tailTrace_5880373
  have hstable : (prefixWord ++ tailWord_5880373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880373).length < 2 ^ (prefixWord ++ tailWord_5880373).sum := by decide
  have hdescent : baseEnd_5880373 < baseStart_5880373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880397 : List Nat := [1, 6, 1, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_5880397 : Nat := 118140960795 + 5880397 * 2 ^ 59
def prefixEnd_5880397 : Nat := 4983230072969 + 3 ^ 40 * 5880397 * 2
def baseEnd_5880397 : Nat := 3019470100256934653394053

theorem tailTrace_5880397 : CollatzResearch.WordTrace tailWord_5880397 prefixEnd_5880397 3019470100256934653394053 := by
  unfold tailWord_5880397
  simp only [CollatzResearch.WordTrace]
  refine ⟨214475698477333435696951445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142983798984888957131300963 214475698477333435696951445)
  ·
    refine ⟨10053548366125004798294599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 214475698477333435696951445 10053548366125004798294599)
    ·
      refine ⟨15080322549187507197441899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10053548366125004798294599 15080322549187507197441899)
      ·
        refine ⟨22620483823781260796162849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15080322549187507197441899 22620483823781260796162849)
        ·
          refine ⟨16965362867835945597122137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22620483823781260796162849 16965362867835945597122137)
          ·
            refine ⟨12724022150876959197841603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16965362867835945597122137 12724022150876959197841603)
            ·
              refine ⟨19086033226315438796762405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724022150876959197841603 19086033226315438796762405)
              ·
                refine ⟨3578631229934144774392951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19086033226315438796762405 3578631229934144774392951)
                ·
                  refine ⟨5367946844901217161589427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578631229934144774392951 5367946844901217161589427)
                  ·
                    refine ⟨8051920267351825742384141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5367946844901217161589427 8051920267351825742384141)
                    ·
                      refine ⟨3019470100256934653394053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8051920267351825742384141 3019470100256934653394053)
                      ·
                        rfl

theorem cell23_5880397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_5880397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880397 prefixEnd_5880397 := by exact prefixLift 5880397
  have htrace : WordTrace (prefixWord ++ tailWord_5880397) baseStart_5880397 baseEnd_5880397 := by
    simpa [prefixWord, tailWord_5880397, baseEnd_5880397] using wordTrace_append hprefix tailTrace_5880397
  have hstable : (prefixWord ++ tailWord_5880397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880397).length < 2 ^ (prefixWord ++ tailWord_5880397).sum := by decide
  have hdescent : baseEnd_5880397 < baseStart_5880397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880414 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_5880414 : Nat := 118140960795 + 5880414 * 2 ^ 59
def prefixEnd_5880414 : Nat := 4983230072969 + 3 ^ 40 * 5880414 * 2
def baseEnd_5880414 : Nat := 3019478829428061086881475

theorem tailTrace_5880414 : CollatzResearch.WordTrace tailWord_5880414 prefixEnd_5880414 3019478829428061086881475 := by
  unfold tailWord_5880414
  simp only [CollatzResearch.WordTrace]
  refine ⟨26809539814783980950040037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142984212345514565066880197 26809539814783980950040037)
  ·
    refine ⟨5026788715271996428132507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26809539814783980950040037 5026788715271996428132507)
    ·
      refine ⟨7540183072907994642198761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5026788715271996428132507 7540183072907994642198761)
      ·
        refine ⟨5655137304680995981649071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7540183072907994642198761 5655137304680995981649071)
        ·
          refine ⟨8482705957021493972473607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655137304680995981649071 8482705957021493972473607)
          ·
            refine ⟨12724058935532240958710411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8482705957021493972473607 12724058935532240958710411)
            ·
              refine ⟨19086088403298361438065617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724058935532240958710411 19086088403298361438065617)
              ·
                refine ⟨14314566302473771078549213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19086088403298361438065617 14314566302473771078549213)
                ·
                  refine ⟨5367962363427664154455955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14314566302473771078549213 5367962363427664154455955)
                  ·
                    refine ⟨8051943545141496231683933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5367962363427664154455955 8051943545141496231683933)
                    ·
                      refine ⟨3019478829428061086881475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8051943545141496231683933 3019478829428061086881475)
                      ·
                        rfl

theorem cell23_5880414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_5880414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880414 prefixEnd_5880414 := by exact prefixLift 5880414
  have htrace : WordTrace (prefixWord ++ tailWord_5880414) baseStart_5880414 baseEnd_5880414 := by
    simpa [prefixWord, tailWord_5880414, baseEnd_5880414] using wordTrace_append hprefix tailTrace_5880414
  have hstable : (prefixWord ++ tailWord_5880414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880414).length < 2 ^ (prefixWord ++ tailWord_5880414).sum := by decide
  have hdescent : baseEnd_5880414 < baseStart_5880414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880426 : List Nat := [3, 1, 3, 2, 1, 1, 5, 7]
def baseStart_5880426 : Nat := 118140960795 + 5880426 * 2 ^ 59
def prefixEnd_5880426 : Nat := 4983230072969 + 3 ^ 40 * 5880426 * 2
def baseEnd_5880426 : Nat := 111832777451700557034497

theorem tailTrace_5880426 : CollatzResearch.WordTrace tailWord_5880426 prefixEnd_5880426 111832777451700557034497 := by
  unfold tailWord_5880426
  simp only [CollatzResearch.WordTrace]
  refine ⟨53619189048557093412439283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142984504129485582433171421 53619189048557093412439283)
  ·
    refine ⟨80428783572835640118658925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53619189048557093412439283 80428783572835640118658925)
    ·
      refine ⟨30160793839813365044497097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80428783572835640118658925 30160793839813365044497097)
      ·
        refine ⟨22620595379860023783372823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30160793839813365044497097 22620595379860023783372823)
        ·
          refine ⟨33930893069790035675059235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22620595379860023783372823 33930893069790035675059235)
          ·
            refine ⟨50896339604685053512588853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33930893069790035675059235 50896339604685053512588853)
            ·
              refine ⟨4771531837939223766805205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50896339604685053512588853 4771531837939223766805205)
              ·
                refine ⟨111832777451700557034497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4771531837939223766805205 111832777451700557034497)
                ·
                  rfl

theorem cell23_5880426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 7].length) (baseStart_5880426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880426 prefixEnd_5880426 := by exact prefixLift 5880426
  have htrace : WordTrace (prefixWord ++ tailWord_5880426) baseStart_5880426 baseEnd_5880426 := by
    simpa [prefixWord, tailWord_5880426, baseEnd_5880426] using wordTrace_append hprefix tailTrace_5880426
  have hstable : (prefixWord ++ tailWord_5880426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880426).length < 2 ^ (prefixWord ++ tailWord_5880426).sum := by decide
  have hdescent : baseEnd_5880426 < baseStart_5880426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880437 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5880437 : Nat := 118140960795 + 5880437 * 2 ^ 59
def prefixEnd_5880437 : Nat := 4983230072969 + 3 ^ 40 * 5880437 * 2
def baseEnd_5880437 : Nat := 3019490639483114496893869

theorem tailTrace_5880437 : CollatzResearch.WordTrace tailWord_5880437 prefixEnd_5880437 3019490639483114496893869 := by
  unfold tailWord_5880437
  simp only [CollatzResearch.WordTrace]
  refine ⟨214477157397188522528407565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142984771598125681685605043 214477157397188522528407565)
  ·
    refine ⟨80428934023945695948152837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214477157397188522528407565 80428934023945695948152837)
    ·
      refine ⟨15080425129489817990278657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80428934023945695948152837 15080425129489817990278657)
      ·
        refine ⟨11310318847117363492708993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15080425129489817990278657 11310318847117363492708993)
        ·
          refine ⟨8482739135338022619531745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11310318847117363492708993 8482739135338022619531745)
          ·
            refine ⟨6362054351503516964648809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8482739135338022619531745 6362054351503516964648809)
            ·
              refine ⟨4771540763627637723486607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6362054351503516964648809 4771540763627637723486607)
              ·
                refine ⟨7157311145441456585229911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4771540763627637723486607 7157311145441456585229911)
                ·
                  refine ⟨10735966718162184877844867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7157311145441456585229911 10735966718162184877844867)
                  ·
                    refine ⟨16103950077243277316767301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10735966718162184877844867 16103950077243277316767301)
                    ·
                      refine ⟨3019490639483114496893869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16103950077243277316767301 3019490639483114496893869)
                      ·
                        rfl

theorem cell23_5880437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5880437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880437 prefixEnd_5880437 := by exact prefixLift 5880437
  have htrace : WordTrace (prefixWord ++ tailWord_5880437) baseStart_5880437 baseEnd_5880437 := by
    simpa [prefixWord, tailWord_5880437, baseEnd_5880437] using wordTrace_append hprefix tailTrace_5880437
  have hstable : (prefixWord ++ tailWord_5880437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880437).length < 2 ^ (prefixWord ++ tailWord_5880437).sum := by decide
  have hdescent : baseEnd_5880437 < baseStart_5880437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880453 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 3]
def baseStart_5880453 : Nat := 118140960795 + 5880453 * 2 ^ 59
def prefixEnd_5880453 : Nat := 4983230072969 + 3 ^ 40 * 5880453 * 2
def baseEnd_5880453 : Nat := 3019498855173586434293795

theorem tailTrace_5880453 : CollatzResearch.WordTrace tailWord_5880453 prefixEnd_5880453 3019498855173586434293795 := by
  unfold tailWord_5880453
  simp only [CollatzResearch.WordTrace]
  refine ⟨214477740965130557260990013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142985160643420371507326675 214477740965130557260990013)
  ·
    refine ⟨80429152861923958972871255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214477740965130557260990013 80429152861923958972871255)
    ·
      refine ⟨120643729292885938459306883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80429152861923958972871255 120643729292885938459306883)
      ·
        refine ⟨180965593939328907688960325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120643729292885938459306883 180965593939328907688960325)
        ·
          refine ⟨33931048863624170191680061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180965593939328907688960325 33931048863624170191680061)
          ·
            refine ⟨12724143323859063821880023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33931048863624170191680061 12724143323859063821880023)
            ·
              refine ⟨19086214985788595732820035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724143323859063821880023 19086214985788595732820035)
              ·
                refine ⟨28629322478682893599230053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19086214985788595732820035 28629322478682893599230053)
                ·
                  refine ⟨5367997964753042549855635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28629322478682893599230053 5367997964753042549855635)
                  ·
                    refine ⟨8051996947129563824783453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5367997964753042549855635 8051996947129563824783453)
                    ·
                      refine ⟨3019498855173586434293795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8051996947129563824783453 3019498855173586434293795)
                      ·
                        rfl

theorem cell23_5880453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_5880453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880453 prefixEnd_5880453 := by exact prefixLift 5880453
  have htrace : WordTrace (prefixWord ++ tailWord_5880453) baseStart_5880453 baseEnd_5880453 := by
    simpa [prefixWord, tailWord_5880453, baseEnd_5880453] using wordTrace_append hprefix tailTrace_5880453
  have hstable : (prefixWord ++ tailWord_5880453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880453).length < 2 ^ (prefixWord ++ tailWord_5880453).sum := by decide
  have hdescent : baseEnd_5880453 < baseStart_5880453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880459 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 4]
def baseStart_5880459 : Nat := 118140960795 + 5880459 * 2 ^ 59
def prefixEnd_5880459 : Nat := 4983230072969 + 3 ^ 40 * 5880459 * 2
def baseEnd_5880459 : Nat := 3019501936057513410818767

theorem tailTrace_5880459 : CollatzResearch.WordTrace tailWord_5880459 prefixEnd_5880459 3019501936057513410818767 := by
  unfold tailWord_5880459
  simp only [CollatzResearch.WordTrace]
  refine ⟨214477959803108820285708431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142985306535405880190472287 214477959803108820285708431)
  ·
    refine ⟨321716939704663230428562647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214477959803108820285708431 321716939704663230428562647)
    ·
      refine ⟨482575409556994845642843971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321716939704663230428562647 482575409556994845642843971)
      ·
        refine ⟨723863114335492268464265957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482575409556994845642843971 723863114335492268464265957)
        ·
          refine ⟨135724333937904800337049867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 723863114335492268464265957 135724333937904800337049867)
          ·
            refine ⟨203586500906857200505574801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135724333937904800337049867 203586500906857200505574801)
            ·
              refine ⟨152689875680142900379181101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203586500906857200505574801 152689875680142900379181101)
              ·
                refine ⟨57258703380053587642192913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152689875680142900379181101 57258703380053587642192913)
                ·
                  refine ⟨42944027535040190731644685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57258703380053587642192913 42944027535040190731644685)
                  ·
                    refine ⟨16104010325640071524366757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42944027535040190731644685 16104010325640071524366757)
                    ·
                      refine ⟨3019501936057513410818767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16104010325640071524366757 3019501936057513410818767)
                      ·
                        rfl

theorem cell23_5880459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 4].length) (baseStart_5880459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880459 prefixEnd_5880459 := by exact prefixLift 5880459
  have htrace : WordTrace (prefixWord ++ tailWord_5880459) baseStart_5880459 baseEnd_5880459 := by
    simpa [prefixWord, tailWord_5880459, baseEnd_5880459] using wordTrace_append hprefix tailTrace_5880459
  have hstable : (prefixWord ++ tailWord_5880459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880459).length < 2 ^ (prefixWord ++ tailWord_5880459).sum := by decide
  have hdescent : baseEnd_5880459 < baseStart_5880459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880489 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_5880489 : Nat := 118140960795 + 5880489 * 2 ^ 59
def prefixEnd_5880489 : Nat := 4983230072969 + 3 ^ 40 * 5880489 * 2
def baseEnd_5880489 : Nat := 3019517340477148293443629

theorem tailTrace_5880489 : CollatzResearch.WordTrace tailWord_5880489 prefixEnd_5880489 3019517340477148293443629 := by
  unfold tailWord_5880489
  simp only [CollatzResearch.WordTrace]
  refine ⟨214479053993000135409300521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142986035995333423606200347 214479053993000135409300521)
  ·
    refine ⟨160859290494750101556975391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214479053993000135409300521 160859290494750101556975391)
    ·
      refine ⟨241288935742125152335463087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160859290494750101556975391 241288935742125152335463087)
      ·
        refine ⟨361933403613187728503194631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241288935742125152335463087 361933403613187728503194631)
        ·
          refine ⟨542900105419781592754791947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361933403613187728503194631 542900105419781592754791947)
          ·
            refine ⟨814350158129672389132187921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542900105419781592754791947 814350158129672389132187921)
            ·
              refine ⟨610762618597254291849140941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814350158129672389132187921 610762618597254291849140941)
              ·
                refine ⟨229035981973970359443427853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 610762618597254291849140941 229035981973970359443427853)
                ·
                  refine ⟨85888493240238884791285445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229035981973970359443427853 85888493240238884791285445)
                  ·
                    refine ⟨16104092482544790898366021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85888493240238884791285445 16104092482544790898366021)
                    ·
                      refine ⟨3019517340477148293443629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16104092482544790898366021 3019517340477148293443629)
                      ·
                        rfl

theorem cell23_5880489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_5880489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880489 prefixEnd_5880489 := by exact prefixLift 5880489
  have htrace : WordTrace (prefixWord ++ tailWord_5880489) baseStart_5880489 baseEnd_5880489 := by
    simpa [prefixWord, tailWord_5880489, baseEnd_5880489] using wordTrace_append hprefix tailTrace_5880489
  have hstable : (prefixWord ++ tailWord_5880489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880489).length < 2 ^ (prefixWord ++ tailWord_5880489).sum := by decide
  have hdescent : baseEnd_5880489 < baseStart_5880489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880510 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_5880510 : Nat := 118140960795 + 5880510 * 2 ^ 59
def prefixEnd_5880510 : Nat := 4983230072969 + 3 ^ 40 * 5880510 * 2
def baseEnd_5880510 : Nat := 3019528123570892711281033

theorem tailTrace_5880510 : CollatzResearch.WordTrace tailWord_5880510 prefixEnd_5880510 3019528123570892711281033 := by
  unfold tailWord_5880510
  simp only [CollatzResearch.WordTrace]
  refine ⟨26809977490740506999476873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142986546617282703997209989 26809977490740506999476873)
  ·
    refine ⟨20107483118055380249607655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26809977490740506999476873 20107483118055380249607655)
    ·
      refine ⟨30161224677083070374411483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20107483118055380249607655 30161224677083070374411483)
      ·
        refine ⟨45241837015624605561617225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30161224677083070374411483 45241837015624605561617225)
        ·
          refine ⟨33931377761718454171212919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45241837015624605561617225 33931377761718454171212919)
          ·
            refine ⟨50897066642577681256819379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33931377761718454171212919 50897066642577681256819379)
            ·
              refine ⟨76345599963866521885229069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50897066642577681256819379 76345599963866521885229069)
              ·
                refine ⟨28629599986449945706960901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76345599963866521885229069 28629599986449945706960901)
                ·
                  refine ⟨5368049997459364820055169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28629599986449945706960901 5368049997459364820055169)
                  ·
                    refine ⟨4026037498094523615041377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5368049997459364820055169 4026037498094523615041377)
                    ·
                      refine ⟨3019528123570892711281033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4026037498094523615041377 3019528123570892711281033)
                      ·
                        rfl

theorem cell23_5880510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_5880510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880510 prefixEnd_5880510 := by exact prefixLift 5880510
  have htrace : WordTrace (prefixWord ++ tailWord_5880510) baseStart_5880510 baseEnd_5880510 := by
    simpa [prefixWord, tailWord_5880510, baseEnd_5880510] using wordTrace_append hprefix tailTrace_5880510
  have hstable : (prefixWord ++ tailWord_5880510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880510).length < 2 ^ (prefixWord ++ tailWord_5880510).sum := by decide
  have hdescent : baseEnd_5880510 < baseStart_5880510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880519 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_5880519 : Nat := 118140960795 + 5880519 * 2 ^ 59
def prefixEnd_5880519 : Nat := 4983230072969 + 3 ^ 40 * 5880519 * 2
def baseEnd_5880519 : Nat := 3019532744896783176068491

theorem tailTrace_5880519 : CollatzResearch.WordTrace tailWord_5880519 prefixEnd_5880519 3019532744896783176068491 := by
  unfold tailWord_5880519
  simp only [CollatzResearch.WordTrace]
  refine ⟨214480148182891450532892611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142986765455260967021928407 214480148182891450532892611)
  ·
    refine ⟨321720222274337175799338917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214480148182891450532892611 321720222274337175799338917)
    ·
      refine ⟨60322541676438220462376047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321720222274337175799338917 60322541676438220462376047)
      ·
        refine ⟨90483812514657330693564071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60322541676438220462376047 90483812514657330693564071)
        ·
          refine ⟨135725718771985996040346107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90483812514657330693564071 135725718771985996040346107)
          ·
            refine ⟨203588578157978994060519161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135725718771985996040346107 203588578157978994060519161)
            ·
              refine ⟨152691433618484245545389371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203588578157978994060519161 152691433618484245545389371)
              ·
                refine ⟨229037150427726368318084057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152691433618484245545389371 229037150427726368318084057)
                ·
                  refine ⟨171777862820794776238563043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229037150427726368318084057 171777862820794776238563043)
                  ·
                    refine ⟨257666794231192164357844565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171777862820794776238563043 257666794231192164357844565)
                    ·
                      refine ⟨3019532744896783176068491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 257666794231192164357844565 3019532744896783176068491)
                      ·
                        rfl

theorem cell23_5880519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_5880519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880519 prefixEnd_5880519 := by exact prefixLift 5880519
  have htrace : WordTrace (prefixWord ++ tailWord_5880519) baseStart_5880519 baseEnd_5880519 := by
    simpa [prefixWord, tailWord_5880519, baseEnd_5880519] using wordTrace_append hprefix tailTrace_5880519
  have hstable : (prefixWord ++ tailWord_5880519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880519).length < 2 ^ (prefixWord ++ tailWord_5880519).sum := by decide
  have hdescent : baseEnd_5880519 < baseStart_5880519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880539 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 5]
def baseStart_5880539 : Nat := 118140960795 + 5880539 * 2 ^ 59
def prefixEnd_5880539 : Nat := 4983230072969 + 3 ^ 40 * 5880539 * 2
def baseEnd_5880539 : Nat := 3019543014509873097818399

theorem tailTrace_5880539 : CollatzResearch.WordTrace tailWord_5880539 prefixEnd_5880539 3019543014509873097818399 := by
  unfold tailWord_5880539
  simp only [CollatzResearch.WordTrace]
  refine ⟨214480877642818993948620671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142987251761879329299080447 214480877642818993948620671)
  ·
    refine ⟨321721316464228490922931007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214480877642818993948620671 321721316464228490922931007)
    ·
      refine ⟨482581974696342736384396511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321721316464228490922931007 482581974696342736384396511)
      ·
        refine ⟨723872962044514104576594767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482581974696342736384396511 723872962044514104576594767)
        ·
          refine ⟨1085809443066771156864892151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723872962044514104576594767 1085809443066771156864892151)
          ·
            refine ⟨1628714164600156735297338227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085809443066771156864892151 1628714164600156735297338227)
            ·
              refine ⟨2443071246900235102946007341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628714164600156735297338227 2443071246900235102946007341)
              ·
                refine ⟨916151717587588163604752753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2443071246900235102946007341 916151717587588163604752753)
                ·
                  refine ⟨687113788190691122703564565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916151717587588163604752753 687113788190691122703564565)
                  ·
                    refine ⟨32208458821438646376729589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 687113788190691122703564565 32208458821438646376729589)
                    ·
                      refine ⟨3019543014509873097818399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32208458821438646376729589 3019543014509873097818399)
                      ·
                        rfl

theorem cell23_5880539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_5880539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880539 prefixEnd_5880539 := by exact prefixLift 5880539
  have htrace : WordTrace (prefixWord ++ tailWord_5880539) baseStart_5880539 baseEnd_5880539 := by
    simpa [prefixWord, tailWord_5880539, baseEnd_5880539] using wordTrace_append hprefix tailTrace_5880539
  have hstable : (prefixWord ++ tailWord_5880539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880539).length < 2 ^ (prefixWord ++ tailWord_5880539).sum := by decide
  have hdescent : baseEnd_5880539 < baseStart_5880539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880626 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_5880626 : Nat := 118140960795 + 5880626 * 2 ^ 59
def prefixEnd_5880626 : Nat := 4983230072969 + 3 ^ 40 * 5880626 * 2
def baseEnd_5880626 : Nat := 3019587687326814257430499

theorem tailTrace_5880626 : CollatzResearch.WordTrace tailWord_5880626 prefixEnd_5880626 3019587687326814257430499 := by
  unfold tailWord_5880626
  simp only [CollatzResearch.WordTrace]
  refine ⟨53621012698375951951759433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142989367195669205204691821 53621012698375951951759433)
  ·
    refine ⟨40215759523781963963819575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53621012698375951951759433 40215759523781963963819575)
    ·
      refine ⟨60323639285672945945729363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40215759523781963963819575 60323639285672945945729363)
      ·
        refine ⟨90485458928509418918594045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60323639285672945945729363 90485458928509418918594045)
        ·
          refine ⟨33932047098191032094472767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90485458928509418918594045 33932047098191032094472767)
          ·
            refine ⟨50898070647286548141709151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33932047098191032094472767 50898070647286548141709151)
            ·
              refine ⟨76347105970929822212563727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50898070647286548141709151 76347105970929822212563727)
              ·
                refine ⟨114520658956394733318845591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76347105970929822212563727 114520658956394733318845591)
                ·
                  refine ⟨171780988434592099978268387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114520658956394733318845591 171780988434592099978268387)
                  ·
                    refine ⟨257671482651888149967402581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171780988434592099978268387 257671482651888149967402581)
                    ·
                      refine ⟨3019587687326814257430499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 257671482651888149967402581 3019587687326814257430499)
                      ·
                        rfl

theorem cell23_5880626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_5880626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880626 prefixEnd_5880626 := by exact prefixLift 5880626
  have htrace : WordTrace (prefixWord ++ tailWord_5880626) baseStart_5880626 baseEnd_5880626 := by
    simpa [prefixWord, tailWord_5880626, baseEnd_5880626] using wordTrace_append hprefix tailTrace_5880626
  have hstable : (prefixWord ++ tailWord_5880626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880626).length < 2 ^ (prefixWord ++ tailWord_5880626).sum := by decide
  have hdescent : baseEnd_5880626 < baseStart_5880626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880643 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 3, 5, 2]
def baseStart_5880643 : Nat := 118140960795 + 5880643 * 2 ^ 59
def prefixEnd_5880643 : Nat := 4983230072969 + 3 ^ 40 * 5880643 * 2
def baseEnd_5880643 : Nat := 3019596416497940690917921

theorem tailTrace_5880643 : CollatzResearch.WordTrace tailWord_5880643 prefixEnd_5880643 3019596416497940690917921 := by
  unfold tailWord_5880643
  simp only [CollatzResearch.WordTrace]
  refine ⟨214484670834442219710406583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142989780556294813140271055 214484670834442219710406583)
  ·
    refine ⟨321727006251663329565609875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214484670834442219710406583 321727006251663329565609875)
    ·
      refine ⟨482590509377494994348414813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321727006251663329565609875 482590509377494994348414813)
      ·
        refine ⟨180971441016560622880655555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 482590509377494994348414813 180971441016560622880655555)
        ·
          refine ⟨271457161524840934320983333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180971441016560622880655555 271457161524840934320983333)
          ·
            refine ⟨50898217785907675185184375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271457161524840934320983333 50898217785907675185184375)
            ·
              refine ⟨76347326678861512777776563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50898217785907675185184375 76347326678861512777776563)
              ·
                refine ⟨114520990018292269166664845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76347326678861512777776563 114520990018292269166664845)
                ·
                  refine ⟨42945371256859600937499317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114520990018292269166664845 42945371256859600937499317)
                  ·
                    refine ⟨4026128555330587587890561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42945371256859600937499317 4026128555330587587890561)
                    ·
                      refine ⟨3019596416497940690917921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4026128555330587587890561 3019596416497940690917921)
                      ·
                        rfl

theorem cell23_5880643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_5880643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880643 prefixEnd_5880643 := by exact prefixLift 5880643
  have htrace : WordTrace (prefixWord ++ tailWord_5880643) baseStart_5880643 baseEnd_5880643 := by
    simpa [prefixWord, tailWord_5880643, baseEnd_5880643] using wordTrace_append hprefix tailTrace_5880643
  have hstable : (prefixWord ++ tailWord_5880643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880643).length < 2 ^ (prefixWord ++ tailWord_5880643).sum := by decide
  have hdescent : baseEnd_5880643 < baseStart_5880643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880683 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 4, 4]
def baseStart_5880683 : Nat := 118140960795 + 5880683 * 2 ^ 59
def prefixEnd_5880683 : Nat := 4983230072969 + 3 ^ 40 * 5880683 * 2
def baseEnd_5880683 : Nat := 1006538985241373511472579

theorem tailTrace_5880683 : CollatzResearch.WordTrace tailWord_5880683 prefixEnd_5880683 1006538985241373511472579 := by
  unfold tailWord_5880683
  simp only [CollatzResearch.WordTrace]
  refine ⟨214486129754297306541862703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142990753169531537694575135 214486129754297306541862703)
  ·
    refine ⟨321729194631445959812794055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214486129754297306541862703 321729194631445959812794055)
    ·
      refine ⟨482593791947168939719191083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321729194631445959812794055 482593791947168939719191083)
      ·
        refine ⟨723890687920753409578786625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482593791947168939719191083 723890687920753409578786625)
        ·
          refine ⟨542918015940565057184089969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723890687920753409578786625 542918015940565057184089969)
          ·
            refine ⟨407188511955423792888067477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542918015940565057184089969 407188511955423792888067477)
            ·
              refine ⟨19086961497910490291628163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 407188511955423792888067477 19086961497910490291628163)
              ·
                refine ⟨28630442246865735437442245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19086961497910490291628163 28630442246865735437442245)
                ·
                  refine ⟨5368207921287325394520421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28630442246865735437442245 5368207921287325394520421)
                  ·
                    refine ⟨1006538985241373511472579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5368207921287325394520421 1006538985241373511472579)
                    ·
                      rfl

theorem cell23_5880683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 4].length) (baseStart_5880683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880683 prefixEnd_5880683 := by exact prefixLift 5880683
  have htrace : WordTrace (prefixWord ++ tailWord_5880683) baseStart_5880683 baseEnd_5880683 := by
    simpa [prefixWord, tailWord_5880683, baseEnd_5880683] using wordTrace_append hprefix tailTrace_5880683
  have hstable : (prefixWord ++ tailWord_5880683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880683).length < 2 ^ (prefixWord ++ tailWord_5880683).sum := by decide
  have hdescent : baseEnd_5880683 < baseStart_5880683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880684 : List Nat := [2, 2, 1, 1, 4, 1, 5, 2, 1, 1, 3]
def baseStart_5880684 : Nat := 118140960795 + 5880684 * 2 ^ 59
def prefixEnd_5880684 : Nat := 4983230072969 + 3 ^ 40 * 5880684 * 2
def baseEnd_5880684 : Nat := 3019617469204775030505233

theorem tailTrace_5880684 : CollatzResearch.WordTrace tailWord_5880684 prefixEnd_5880684 3019617469204775030505233 := by
  unfold tailWord_5880684
  simp only [CollatzResearch.WordTrace]
  refine ⟨107243083113646841856324553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142990777484862455808432737 107243083113646841856324553)
  ·
    refine ⟨80432312335235131392243415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107243083113646841856324553 80432312335235131392243415)
    ·
      refine ⟨120648468502852697088365123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80432312335235131392243415 120648468502852697088365123)
      ·
        refine ⟨180972702754279045632547685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120648468502852697088365123 180972702754279045632547685)
        ·
          refine ⟨33932381766427321056102691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180972702754279045632547685 33932381766427321056102691)
          ·
            refine ⟨50898572649640981584154037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33932381766427321056102691 50898572649640981584154037)
            ·
              refine ⟨4771741185903842023514441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50898572649640981584154037 4771741185903842023514441)
              ·
                refine ⟨3578805889427881517635831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4771741185903842023514441 3578805889427881517635831)
                ·
                  refine ⟨5368208834141822276453747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578805889427881517635831 5368208834141822276453747)
                  ·
                    refine ⟨8052313251212733414680621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5368208834141822276453747 8052313251212733414680621)
                    ·
                      refine ⟨3019617469204775030505233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8052313251212733414680621 3019617469204775030505233)
                      ·
                        rfl

theorem cell23_5880684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 1, 3].length) (baseStart_5880684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880684 prefixEnd_5880684 := by exact prefixLift 5880684
  have htrace : WordTrace (prefixWord ++ tailWord_5880684) baseStart_5880684 baseEnd_5880684 := by
    simpa [prefixWord, tailWord_5880684, baseEnd_5880684] using wordTrace_append hprefix tailTrace_5880684
  have hstable : (prefixWord ++ tailWord_5880684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880684).length < 2 ^ (prefixWord ++ tailWord_5880684).sum := by decide
  have hdescent : baseEnd_5880684 < baseStart_5880684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880727 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 1, 2, 3]
def baseStart_5880727 : Nat := 118140960795 + 5880727 * 2 ^ 59
def prefixEnd_5880727 : Nat := 4983230072969 + 3 ^ 40 * 5880727 * 2
def baseEnd_5880727 : Nat := 3019639548872918362267535

theorem tailTrace_5880727 : CollatzResearch.WordTrace tailWord_5880727 prefixEnd_5880727 3019639548872918362267535 := by
  unfold tailWord_5880727
  simp only [CollatzResearch.WordTrace]
  refine ⟨214487734566137902056464435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142991823044091934704309623 214487734566137902056464435)
  ·
    refine ⟨321731601849206853084696653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214487734566137902056464435 321731601849206853084696653)
    ·
      refine ⟨120649350693452569906761245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321731601849206853084696653 120649350693452569906761245)
      ·
        refine ⟨45243506510044713715035467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120649350693452569906761245 45243506510044713715035467)
        ·
          refine ⟨67865259765067070572553201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45243506510044713715035467 67865259765067070572553201)
          ·
            refine ⟨50898944823800302929414901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67865259765067070572553201 50898944823800302929414901)
            ·
              refine ⟨4771776077231278399632647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50898944823800302929414901 4771776077231278399632647)
              ·
                refine ⟨7157664115846917599448971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4771776077231278399632647 7157664115846917599448971)
                ·
                  refine ⟨10736496173770376399173457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7157664115846917599448971 10736496173770376399173457)
                  ·
                    refine ⟨8052372130327782299380093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10736496173770376399173457 8052372130327782299380093)
                    ·
                      refine ⟨3019639548872918362267535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8052372130327782299380093 3019639548872918362267535)
                      ·
                        rfl

theorem cell23_5880727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_5880727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880727 prefixEnd_5880727 := by exact prefixLift 5880727
  have htrace : WordTrace (prefixWord ++ tailWord_5880727) baseStart_5880727 baseEnd_5880727 := by
    simpa [prefixWord, tailWord_5880727, baseEnd_5880727] using wordTrace_append hprefix tailTrace_5880727
  have hstable : (prefixWord ++ tailWord_5880727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880727).length < 2 ^ (prefixWord ++ tailWord_5880727).sum := by decide
  have hdescent : baseEnd_5880727 < baseStart_5880727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880757 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_5880757 : Nat := 118140960795 + 5880757 * 2 ^ 59
def prefixEnd_5880757 : Nat := 4983230072969 + 3 ^ 40 * 5880757 * 2
def baseEnd_5880757 : Nat := 3019654953292553244892397

theorem tailTrace_5880757 : CollatzResearch.WordTrace tailWord_5880757 prefixEnd_5880757 3019654953292553244892397 := by
  unfold tailWord_5880757
  simp only [CollatzResearch.WordTrace]
  refine ⟨214488828756029217180056525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142992552504019478120037683 214488828756029217180056525)
  ·
    refine ⟨80433310783510956442521197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214488828756029217180056525 80433310783510956442521197)
    ·
      refine ⟨30162491543816608665945449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80433310783510956442521197 30162491543816608665945449)
      ·
        refine ⟨22621868657862456499459087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30162491543816608665945449 22621868657862456499459087)
        ·
          refine ⟨33932802986793684749188631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22621868657862456499459087 33932802986793684749188631)
          ·
            refine ⟨50899204480190527123782947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33932802986793684749188631 50899204480190527123782947)
            ·
              refine ⟨76348806720285790685674421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50899204480190527123782947 76348806720285790685674421)
              ·
                refine ⟨7157700630026792876781977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76348806720285790685674421 7157700630026792876781977)
                ·
                  refine ⟨5368275472520094657586483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7157700630026792876781977 5368275472520094657586483)
                  ·
                    refine ⟨8052413208780141986379725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5368275472520094657586483 8052413208780141986379725)
                    ·
                      refine ⟨3019654953292553244892397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8052413208780141986379725 3019654953292553244892397)
                      ·
                        rfl

theorem cell23_5880757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_5880757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880757 prefixEnd_5880757 := by exact prefixLift 5880757
  have htrace : WordTrace (prefixWord ++ tailWord_5880757) baseStart_5880757 baseEnd_5880757 := by
    simpa [prefixWord, tailWord_5880757, baseEnd_5880757] using wordTrace_append hprefix tailTrace_5880757
  have hstable : (prefixWord ++ tailWord_5880757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880757).length < 2 ^ (prefixWord ++ tailWord_5880757).sum := by decide
  have hdescent : baseEnd_5880757 < baseStart_5880757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880810 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_5880810 : Nat := 118140960795 + 5880810 * 2 ^ 59
def prefixEnd_5880810 : Nat := 4983230072969 + 3 ^ 40 * 5880810 * 2
def baseEnd_5880810 : Nat := 3019682167767241537529653

theorem tailTrace_5880810 : CollatzResearch.WordTrace tailWord_5880810 prefixEnd_5880810 3019682167767241537529653 := by
  unfold tailWord_5880810
  simp only [CollatzResearch.WordTrace]
  refine ⟨53622690456209301807933971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142993841216558138154490589 53622690456209301807933971)
  ·
    refine ⟨80434035684313952711900957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53622690456209301807933971 80434035684313952711900957)
    ·
      refine ⟨30162763381617732266962859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80434035684313952711900957 30162763381617732266962859)
      ·
        refine ⟨45244145072426598400444289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30162763381617732266962859 45244145072426598400444289)
        ·
          refine ⟨33933108804319948800333217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45244145072426598400444289 33933108804319948800333217)
          ·
            refine ⟨25449831603239961600249913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33933108804319948800333217 25449831603239961600249913)
            ·
              refine ⟨19087373702429971200187435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25449831603239961600249913 19087373702429971200187435)
              ·
                refine ⟨28631060553644956800281153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19087373702429971200187435 28631060553644956800281153)
                ·
                  refine ⟨21473295415233717600210865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28631060553644956800281153 21473295415233717600210865)
                  ·
                    refine ⟨16104971561425288200158149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21473295415233717600210865 16104971561425288200158149)
                    ·
                      refine ⟨3019682167767241537529653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16104971561425288200158149 3019682167767241537529653)
                      ·
                        rfl

theorem cell23_5880810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_5880810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880810 prefixEnd_5880810 := by exact prefixLift 5880810
  have htrace : WordTrace (prefixWord ++ tailWord_5880810) baseStart_5880810 baseEnd_5880810 := by
    simpa [prefixWord, tailWord_5880810, baseEnd_5880810] using wordTrace_append hprefix tailTrace_5880810
  have hstable : (prefixWord ++ tailWord_5880810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880810).length < 2 ^ (prefixWord ++ tailWord_5880810).sum := by decide
  have hdescent : baseEnd_5880810 < baseStart_5880810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880834 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5880834 : Nat := 118140960795 + 5880834 * 2 ^ 59
def prefixEnd_5880834 : Nat := 4983230072969 + 3 ^ 40 * 5880834 * 2
def baseEnd_5880834 : Nat := 3019694491302949443629543

theorem tailTrace_5880834 : CollatzResearch.WordTrace tailWord_5880834 prefixEnd_5880834 3019694491302949443629543 := by
  unfold tailWord_5880834
  simp only [CollatzResearch.WordTrace]
  refine ⟨53622909294187564832652389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142994424784500172887073037 53622909294187564832652389)
  ·
    refine ⟨10054295492660168406122323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53622909294187564832652389 10054295492660168406122323)
    ·
      refine ⟨15081443238990252609183485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10054295492660168406122323 15081443238990252609183485)
      ·
        refine ⟨5655541214621344728443807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15081443238990252609183485 5655541214621344728443807)
        ·
          refine ⟨8483311821932017092665711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655541214621344728443807 8483311821932017092665711)
          ·
            refine ⟨12724967732898025638998567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483311821932017092665711 12724967732898025638998567)
            ·
              refine ⟨19087451599347038458497851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724967732898025638998567 19087451599347038458497851)
              ·
                refine ⟨28631177399020557687746777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19087451599347038458497851 28631177399020557687746777)
                ·
                  refine ⟨21473383049265418265810083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28631177399020557687746777 21473383049265418265810083)
                  ·
                    refine ⟨32210074573898127398715125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21473383049265418265810083 32210074573898127398715125)
                    ·
                      refine ⟨3019694491302949443629543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32210074573898127398715125 3019694491302949443629543)
                      ·
                        rfl

theorem cell23_5880834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5880834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880834 prefixEnd_5880834 := by exact prefixLift 5880834
  have htrace : WordTrace (prefixWord ++ tailWord_5880834) baseStart_5880834 baseEnd_5880834 := by
    simpa [prefixWord, tailWord_5880834, baseEnd_5880834] using wordTrace_append hprefix tailTrace_5880834
  have hstable : (prefixWord ++ tailWord_5880834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880834).length < 2 ^ (prefixWord ++ tailWord_5880834).sum := by decide
  have hdescent : baseEnd_5880834 < baseStart_5880834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880880 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 5, 4]
def baseStart_5880880 : Nat := 118140960795 + 5880880 * 2 ^ 59
def prefixEnd_5880880 : Nat := 4983230072969 + 3 ^ 40 * 5880880 * 2
def baseEnd_5880880 : Nat := 1006572703804352087884777

theorem tailTrace_5880880 : CollatzResearch.WordTrace tailWord_5880880 prefixEnd_5880880 1006572703804352087884777 := by
  unfold tailWord_5880880
  simp only [CollatzResearch.WordTrace]
  refine ⟨107246657467291804593392047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142995543289722406124522729 107246657467291804593392047)
  ·
    refine ⟨160869986200937706890088071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107246657467291804593392047 160869986200937706890088071)
    ·
      refine ⟨241304979301406560335132107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160869986200937706890088071 241304979301406560335132107)
      ·
        refine ⟨361957468952109840502698161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241304979301406560335132107 361957468952109840502698161)
        ·
          refine ⟨271468101714082380377023621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361957468952109840502698161 271468101714082380377023621)
          ·
            refine ⟨50900269071390446320691929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271468101714082380377023621 50900269071390446320691929)
            ·
              refine ⟨38175201803542834740518947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50900269071390446320691929 38175201803542834740518947)
              ·
                refine ⟨57262802705314252110778421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38175201803542834740518947 57262802705314252110778421)
                ·
                  refine ⟨5368387753623211135385477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57262802705314252110778421 5368387753623211135385477)
                  ·
                    refine ⟨1006572703804352087884777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5368387753623211135385477 1006572703804352087884777)
                    ·
                      rfl

theorem cell23_5880880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 4].length) (baseStart_5880880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880880 prefixEnd_5880880 := by exact prefixLift 5880880
  have htrace : WordTrace (prefixWord ++ tailWord_5880880) baseStart_5880880 baseEnd_5880880 := by
    simpa [prefixWord, tailWord_5880880, baseEnd_5880880] using wordTrace_append hprefix tailTrace_5880880
  have hstable : (prefixWord ++ tailWord_5880880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880880).length < 2 ^ (prefixWord ++ tailWord_5880880).sum := by decide
  have hdescent : baseEnd_5880880 < baseStart_5880880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880883 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 6]
def baseStart_5880883 : Nat := 118140960795 + 5880883 * 2 ^ 59
def prefixEnd_5880883 : Nat := 4983230072969 + 3 ^ 40 * 5880883 * 2
def baseEnd_5880883 : Nat := 3019719651855019751916817

theorem tailTrace_5880883 : CollatzResearch.WordTrace tailWord_5880883 prefixEnd_5880883 3019719651855019751916817 := by
  unfold tailWord_5880883
  simp only [CollatzResearch.WordTrace]
  refine ⟨214493424353572740699143303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142995616235715160466095535 214493424353572740699143303)
  ·
    refine ⟨321740136530359111048714955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214493424353572740699143303 321740136530359111048714955)
    ·
      refine ⟨482610204795538666573072433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321740136530359111048714955 482610204795538666573072433)
      ·
        refine ⟨361957653596653999929804325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482610204795538666573072433 361957653596653999929804325)
        ·
          refine ⟨67867060049372624986838311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 361957653596653999929804325 67867060049372624986838311)
          ·
            refine ⟨101800590074058937480257467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67867060049372624986838311 101800590074058937480257467)
            ·
              refine ⟨152700885111088406220386201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101800590074058937480257467 152700885111088406220386201)
              ·
                refine ⟨114525663833316304665289651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152700885111088406220386201 114525663833316304665289651)
                ·
                  refine ⟨171788495749974456997934477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114525663833316304665289651 171788495749974456997934477)
                  ·
                    refine ⟨64420685906240421374225429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171788495749974456997934477 64420685906240421374225429)
                    ·
                      refine ⟨3019719651855019751916817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64420685906240421374225429 3019719651855019751916817)
                      ·
                        rfl

theorem cell23_5880883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_5880883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880883 prefixEnd_5880883 := by exact prefixLift 5880883
  have htrace : WordTrace (prefixWord ++ tailWord_5880883) baseStart_5880883 baseEnd_5880883 := by
    simpa [prefixWord, tailWord_5880883, baseEnd_5880883] using wordTrace_append hprefix tailTrace_5880883
  have hstable : (prefixWord ++ tailWord_5880883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880883).length < 2 ^ (prefixWord ++ tailWord_5880883).sum := by decide
  have hdescent : baseEnd_5880883 < baseStart_5880883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880884 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_5880884 : Nat := 118140960795 + 5880884 * 2 ^ 59
def prefixEnd_5880884 : Nat := 4983230072969 + 3 ^ 40 * 5880884 * 2
def baseEnd_5880884 : Nat := 1006573388445224749334771

theorem tailTrace_5880884 : CollatzResearch.WordTrace tailWord_5880884 prefixEnd_5880884 1006573388445224749334771 := by
  unfold tailWord_5880884
  simp only [CollatzResearch.WordTrace]
  refine ⟨107246730413284558934964853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142995640551046078579953137 107246730413284558934964853)
  ·
    refine ⟨10054380976245427400152955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107246730413284558934964853 10054380976245427400152955)
    ·
      refine ⟨15081571464368141100229433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10054380976245427400152955 15081571464368141100229433)
      ·
        refine ⟨11311178598276105825172075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15081571464368141100229433 11311178598276105825172075)
        ·
          refine ⟨16966767897414158737758113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11311178598276105825172075 16966767897414158737758113)
          ·
            refine ⟨12725075923060619053318585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16966767897414158737758113 12725075923060619053318585)
            ·
              refine ⟨9543806942295464289988939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12725075923060619053318585 9543806942295464289988939)
              ·
                refine ⟨14315710413443196434983409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9543806942295464289988939 14315710413443196434983409)
                ·
                  refine ⟨10736782810082397326237557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14315710413443196434983409 10736782810082397326237557)
                  ·
                    refine ⟨1006573388445224749334771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10736782810082397326237557 1006573388445224749334771)
                    ·
                      rfl

theorem cell23_5880884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_5880884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880884 prefixEnd_5880884 := by exact prefixLift 5880884
  have htrace : WordTrace (prefixWord ++ tailWord_5880884) baseStart_5880884 baseEnd_5880884 := by
    simpa [prefixWord, tailWord_5880884, baseEnd_5880884] using wordTrace_append hprefix tailTrace_5880884
  have hstable : (prefixWord ++ tailWord_5880884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880884).length < 2 ^ (prefixWord ++ tailWord_5880884).sum := by decide
  have hdescent : baseEnd_5880884 < baseStart_5880884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880890 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_5880890 : Nat := 118140960795 + 5880890 * 2 ^ 59
def prefixEnd_5880890 : Nat := 4983230072969 + 3 ^ 40 * 5880890 * 2
def baseEnd_5880890 : Nat := 3019723246219601224529285

theorem tailTrace_5880890 : CollatzResearch.WordTrace tailWord_5880890 prefixEnd_5880890 3019723246219601224529285 := by
  unfold tailWord_5880890
  simp only [CollatzResearch.WordTrace]
  refine ⟨53623419916136845223662031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142995786443031587263098749 53623419916136845223662031)
  ·
    refine ⟨80435129874205267835493047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53623419916136845223662031 80435129874205267835493047)
    ·
      refine ⟨120652694811307901753239571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80435129874205267835493047 120652694811307901753239571)
      ·
        refine ⟨180979042216961852629859357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120652694811307901753239571 180979042216961852629859357)
        ·
          refine ⟨67867140831360694736197259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180979042216961852629859357 67867140831360694736197259)
          ·
            refine ⟨101800711247041042104295889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67867140831360694736197259 101800711247041042104295889)
            ·
              refine ⟨76350533435280781578221917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101800711247041042104295889 76350533435280781578221917)
              ·
                refine ⟨28631450038230293091833219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76350533435280781578221917 28631450038230293091833219)
                ·
                  refine ⟨42947175057345439637749829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28631450038230293091833219 42947175057345439637749829)
                  ·
                    refine ⟨8052595323252269932078093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42947175057345439637749829 8052595323252269932078093)
                    ·
                      refine ⟨3019723246219601224529285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8052595323252269932078093 3019723246219601224529285)
                      ·
                        rfl

theorem cell23_5880890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_5880890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880890 prefixEnd_5880890 := by exact prefixLift 5880890
  have htrace : WordTrace (prefixWord ++ tailWord_5880890) baseStart_5880890 baseEnd_5880890 := by
    simpa [prefixWord, tailWord_5880890, baseEnd_5880890] using wordTrace_append hprefix tailTrace_5880890
  have hstable : (prefixWord ++ tailWord_5880890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880890).length < 2 ^ (prefixWord ++ tailWord_5880890).sum := by decide
  have hdescent : baseEnd_5880890 < baseStart_5880890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880937 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 3]
def baseStart_5880937 : Nat := 118140960795 + 5880937 * 2 ^ 59
def prefixEnd_5880937 : Nat := 4983230072969 + 3 ^ 40 * 5880937 * 2
def baseEnd_5880937 : Nat := 3019747379810362540641569

theorem tailTrace_5880937 : CollatzResearch.WordTrace tailWord_5880937 prefixEnd_5880937 3019747379810362540641569 := by
  unfold tailWord_5880937
  simp only [CollatzResearch.WordTrace]
  refine ⟨214495393895377107921609065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142996929263584738614406043 214495393895377107921609065)
  ·
    refine ⟨160871545421532830941206799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214495393895377107921609065 160871545421532830941206799)
    ·
      refine ⟨241307318132299246411810199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160871545421532830941206799 241307318132299246411810199)
      ·
        refine ⟨361960977198448869617715299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241307318132299246411810199 361960977198448869617715299)
        ·
          refine ⟨542941465797673304426572949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361960977198448869617715299 542941465797673304426572949)
          ·
            refine ⟨25450381209265936144995607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 542941465797673304426572949 25450381209265936144995607)
            ·
              refine ⟨38175571813898904217493411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25450381209265936144995607 38175571813898904217493411)
              ·
                refine ⟨57263357720848356326240117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38175571813898904217493411 57263357720848356326240117)
                ·
                  refine ⟨5368439786329533405585011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57263357720848356326240117 5368439786329533405585011)
                  ·
                    refine ⟨8052659679494300108377517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5368439786329533405585011 8052659679494300108377517)
                    ·
                      refine ⟨3019747379810362540641569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8052659679494300108377517 3019747379810362540641569)
                      ·
                        rfl

theorem cell23_5880937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 3].length) (baseStart_5880937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880937 prefixEnd_5880937 := by exact prefixLift 5880937
  have htrace : WordTrace (prefixWord ++ tailWord_5880937) baseStart_5880937 baseEnd_5880937 := by
    simpa [prefixWord, tailWord_5880937, baseEnd_5880937] using wordTrace_append hprefix tailTrace_5880937
  have hstable : (prefixWord ++ tailWord_5880937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880937).length < 2 ^ (prefixWord ++ tailWord_5880937).sum := by decide
  have hdescent : baseEnd_5880937 < baseStart_5880937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880940 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_5880940 : Nat := 118140960795 + 5880940 * 2 ^ 59
def prefixEnd_5880940 : Nat := 4983230072969 + 3 ^ 40 * 5880940 * 2
def baseEnd_5880940 : Nat := 1006582973417442009634685

theorem tailTrace_5880940 : CollatzResearch.WordTrace tailWord_5880940 prefixEnd_5880940 1006582973417442009634685 := by
  unfold tailWord_5880940
  simp only [CollatzResearch.WordTrace]
  refine ⟨107247751657183119716984137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142997002209577492955978849 107247751657183119716984137)
  ·
    refine ⟨80435813742887339787738103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107247751657183119716984137 80435813742887339787738103)
    ·
      refine ⟨120653720614331009681607155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80435813742887339787738103 120653720614331009681607155)
      ·
        refine ⟨180980580921496514522410733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120653720614331009681607155 180980580921496514522410733)
        ·
          refine ⟨67867717845561192945904025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180980580921496514522410733 67867717845561192945904025)
          ·
            refine ⟨50900788384170894709428019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67867717845561192945904025 50900788384170894709428019)
            ·
              refine ⟨76351182576256342064142029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50900788384170894709428019 76351182576256342064142029)
              ·
                refine ⟨28631693466096128274053261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76351182576256342064142029 28631693466096128274053261)
                ·
                  refine ⟨10736885049786048102769973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28631693466096128274053261 10736885049786048102769973)
                  ·
                    refine ⟨1006582973417442009634685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10736885049786048102769973 1006582973417442009634685)
                    ·
                      rfl

theorem cell23_5880940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_5880940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880940 prefixEnd_5880940 := by exact prefixLift 5880940
  have htrace : WordTrace (prefixWord ++ tailWord_5880940) baseStart_5880940 baseEnd_5880940 := by
    simpa [prefixWord, tailWord_5880940, baseEnd_5880940] using wordTrace_append hprefix tailTrace_5880940
  have hstable : (prefixWord ++ tailWord_5880940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880940).length < 2 ^ (prefixWord ++ tailWord_5880940).sum := by decide
  have hdescent : baseEnd_5880940 < baseStart_5880940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5880957 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_5880957 : Nat := 118140960795 + 5880957 * 2 ^ 59
def prefixEnd_5880957 : Nat := 4983230072969 + 3 ^ 40 * 5880957 * 2
def baseEnd_5880957 : Nat := 1006585883141150820797159

theorem tailTrace_5880957 : CollatzResearch.WordTrace tailWord_5880957 prefixEnd_5880957 1006585883141150820797159 := by
  unfold tailWord_5880957
  simp only [CollatzResearch.WordTrace]
  refine ⟨214496123355304651337337125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142997415570203100891558083 214496123355304651337337125)
  ·
    refine ⟨40218023129119622125750711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214496123355304651337337125 40218023129119622125750711)
    ·
      refine ⟨60327034693679433188626067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40218023129119622125750711 60327034693679433188626067)
      ·
        refine ⟨90490552040519149782939101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60327034693679433188626067 90490552040519149782939101)
        ·
          refine ⟨33933957015194681168602163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90490552040519149782939101 33933957015194681168602163)
          ·
            refine ⟨50900935522792021752903245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33933957015194681168602163 50900935522792021752903245)
            ·
              refine ⟨19087850821047008157338717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50900935522792021752903245 19087850821047008157338717)
              ·
                refine ⟨7157944057892628059002019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19087850821047008157338717 7157944057892628059002019)
                ·
                  refine ⟨10736916086838942088503029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7157944057892628059002019 10736916086838942088503029)
                  ·
                    refine ⟨1006585883141150820797159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10736916086838942088503029 1006585883141150820797159)
                    ·
                      rfl

theorem cell23_5880957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_5880957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5880957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5880957 prefixEnd_5880957 := by exact prefixLift 5880957
  have htrace : WordTrace (prefixWord ++ tailWord_5880957) baseStart_5880957 baseEnd_5880957 := by
    simpa [prefixWord, tailWord_5880957, baseEnd_5880957] using wordTrace_append hprefix tailTrace_5880957
  have hstable : (prefixWord ++ tailWord_5880957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5880957).length < 2 ^ (prefixWord ++ tailWord_5880957).sum := by decide
  have hdescent : baseEnd_5880957 < baseStart_5880957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5880957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881005 : List Nat := [1, 5, 2, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_5881005 : Nat := 118140960795 + 5881005 * 2 ^ 59
def prefixEnd_5881005 : Nat := 4983230072969 + 3 ^ 40 * 5881005 * 2
def baseEnd_5881005 : Nat := 3019782296494868274591257

theorem tailTrace_5881005 : CollatzResearch.WordTrace tailWord_5881005 prefixEnd_5881005 3019782296494868274591257 := by
  unfold tailWord_5881005
  simp only [CollatzResearch.WordTrace]
  refine ⟨214497874059130755535084469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142998582706087170356722979 214497874059130755535084469)
  ·
    refine ⟨20109175693043508331414169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214497874059130755535084469 20109175693043508331414169)
    ·
      refine ⟨15081881769782631248560627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20109175693043508331414169 15081881769782631248560627)
      ·
        refine ⟨22622822654673946872840941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15081881769782631248560627 22622822654673946872840941)
        ·
          refine ⟨8483558495502730077315353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22622822654673946872840941 8483558495502730077315353)
          ·
            refine ⟨6362668871627047557986515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8483558495502730077315353 6362668871627047557986515)
            ·
              refine ⟨9544003307440571336979773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362668871627047557986515 9544003307440571336979773)
              ·
                refine ⟨3579001240290214251367415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9544003307440571336979773 3579001240290214251367415)
                ·
                  refine ⟨5368501860435321377051123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579001240290214251367415 5368501860435321377051123)
                  ·
                    refine ⟨8052752790652982065576685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5368501860435321377051123 8052752790652982065576685)
                    ·
                      refine ⟨3019782296494868274591257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8052752790652982065576685 3019782296494868274591257)
                      ·
                        rfl

theorem cell23_5881005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_5881005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881005 prefixEnd_5881005 := by exact prefixLift 5881005
  have htrace : WordTrace (prefixWord ++ tailWord_5881005) baseStart_5881005 baseEnd_5881005 := by
    simpa [prefixWord, tailWord_5881005, baseEnd_5881005] using wordTrace_append hprefix tailTrace_5881005
  have hstable : (prefixWord ++ tailWord_5881005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881005).length < 2 ^ (prefixWord ++ tailWord_5881005).sum := by decide
  have hdescent : baseEnd_5881005 < baseStart_5881005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881038 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_5881038 : Nat := 118140960795 + 5881038 * 2 ^ 59
def prefixEnd_5881038 : Nat := 4983230072969 + 3 ^ 40 * 5881038 * 2
def baseEnd_5881038 : Nat := 1006599747118822215159535

theorem tailTrace_5881038 : CollatzResearch.WordTrace tailWord_5881038 prefixEnd_5881038 1006599747118822215159535 := by
  unfold tailWord_5881038
  simp only [CollatzResearch.WordTrace]
  refine ⟨26812384708501400271379471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142999385112007468114023845 26812384708501400271379471)
  ·
    refine ⟨40218577062752100407069207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26812384708501400271379471 40218577062752100407069207)
    ·
      refine ⟨60327865594128150610603811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40218577062752100407069207 60327865594128150610603811)
      ·
        refine ⟨90491798391192225915905717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60327865594128150610603811 90491798391192225915905717)
        ·
          refine ⟨8483606099174271179616161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90491798391192225915905717 8483606099174271179616161)
          ·
            refine ⟨6362704574380703384712121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8483606099174271179616161 6362704574380703384712121)
            ·
              refine ⟨4772028430785527538534091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6362704574380703384712121 4772028430785527538534091)
              ·
                refine ⟨7158042646178291307801137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772028430785527538534091 7158042646178291307801137)
                ·
                  refine ⟨5368531984633718480850853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7158042646178291307801137 5368531984633718480850853)
                  ·
                    refine ⟨1006599747118822215159535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5368531984633718480850853 1006599747118822215159535)
                    ·
                      rfl

theorem cell23_5881038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_5881038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881038 prefixEnd_5881038 := by exact prefixLift 5881038
  have htrace : WordTrace (prefixWord ++ tailWord_5881038) baseStart_5881038 baseEnd_5881038 := by
    simpa [prefixWord, tailWord_5881038, baseEnd_5881038] using wordTrace_append hprefix tailTrace_5881038
  have hstable : (prefixWord ++ tailWord_5881038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881038).length < 2 ^ (prefixWord ++ tailWord_5881038).sum := by decide
  have hdescent : baseEnd_5881038 < baseStart_5881038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881048 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 1, 2, 3]
def baseStart_5881048 : Nat := 118140960795 + 5881048 * 2 ^ 59
def prefixEnd_5881048 : Nat := 4983230072969 + 3 ^ 40 * 5881048 * 2
def baseEnd_5881048 : Nat := 3019804376163011606353559

theorem tailTrace_5881048 : CollatzResearch.WordTrace tailWord_5881048 prefixEnd_5881048 3019804376163011606353559 := by
  unfold tailWord_5881048
  simp only [CollatzResearch.WordTrace]
  refine ⟨107249721198987486939449899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142999628265316649252599865 107249721198987486939449899)
  ·
    refine ⟨160874581798481230409174849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107249721198987486939449899 160874581798481230409174849)
    ·
      refine ⟨120655936348860922806881137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160874581798481230409174849 120655936348860922806881137)
      ·
        refine ⟨90491952261645692105160853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120655936348860922806881137 90491952261645692105160853)
        ·
          refine ⟨4241810262264641817429415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90491952261645692105160853 4241810262264641817429415)
          ·
            refine ⟨6362715393396962726144123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4241810262264641817429415 6362715393396962726144123)
            ·
              refine ⟨9544073090095444089216185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362715393396962726144123 9544073090095444089216185)
              ·
                refine ⟨7158054817571583066912139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9544073090095444089216185 7158054817571583066912139)
                ·
                  refine ⟨10737082226357374600368209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7158054817571583066912139 10737082226357374600368209)
                  ·
                    refine ⟨8052811669768030950276157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10737082226357374600368209 8052811669768030950276157)
                    ·
                      refine ⟨3019804376163011606353559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8052811669768030950276157 3019804376163011606353559)
                      ·
                        rfl

theorem cell23_5881048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_5881048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881048 prefixEnd_5881048 := by exact prefixLift 5881048
  have htrace : WordTrace (prefixWord ++ tailWord_5881048) baseStart_5881048 baseEnd_5881048 := by
    simpa [prefixWord, tailWord_5881048, baseEnd_5881048] using wordTrace_append hprefix tailTrace_5881048
  have hstable : (prefixWord ++ tailWord_5881048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881048).length < 2 ^ (prefixWord ++ tailWord_5881048).sum := by decide
  have hdescent : baseEnd_5881048 < baseStart_5881048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881050 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_5881050 : Nat := 118140960795 + 5881050 * 2 ^ 59
def prefixEnd_5881050 : Nat := 4983230072969 + 3 ^ 40 * 5881050 * 2
def baseEnd_5881050 : Nat := 3019805403124320598528549

theorem tailTrace_5881050 : CollatzResearch.WordTrace tailWord_5881050 prefixEnd_5881050 3019805403124320598528549 := by
  unfold tailWord_5881050
  simp only [CollatzResearch.WordTrace]
  refine ⟨53624878835991932055118151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142999676895978485480315069 53624878835991932055118151)
  ·
    refine ⟨80437318253987898082677227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53624878835991932055118151 80437318253987898082677227)
    ·
      refine ⟨120655977380981847124015841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80437318253987898082677227 120655977380981847124015841)
      ·
        refine ⟨90491983035736385343011881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120655977380981847124015841 90491983035736385343011881)
        ·
          refine ⟨67868987276802289007258911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90491983035736385343011881 67868987276802289007258911)
          ·
            refine ⟨101803480915203433510888367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67868987276802289007258911 101803480915203433510888367)
            ·
              refine ⟨152705221372805150266332551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101803480915203433510888367 152705221372805150266332551)
              ·
                refine ⟨229057832059207725399498827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152705221372805150266332551 229057832059207725399498827)
                ·
                  refine ⟨343586748088811588099248241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229057832059207725399498827 343586748088811588099248241)
                  ·
                    refine ⟨257690061066608691074436181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 343586748088811588099248241 257690061066608691074436181)
                    ·
                      refine ⟨3019805403124320598528549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 257690061066608691074436181 3019805403124320598528549)
                      ·
                        rfl

theorem cell23_5881050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_5881050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881050 prefixEnd_5881050 := by exact prefixLift 5881050
  have htrace : WordTrace (prefixWord ++ tailWord_5881050) baseStart_5881050 baseEnd_5881050 := by
    simpa [prefixWord, tailWord_5881050, baseEnd_5881050] using wordTrace_append hprefix tailTrace_5881050
  have hstable : (prefixWord ++ tailWord_5881050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881050).length < 2 ^ (prefixWord ++ tailWord_5881050).sum := by decide
  have hdescent : baseEnd_5881050 < baseStart_5881050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881080 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_5881080 : Nat := 118140960795 + 5881080 * 2 ^ 59
def prefixEnd_5881080 : Nat := 4983230072969 + 3 ^ 40 * 5881080 * 2
def baseEnd_5881080 : Nat := 3019820807543955481153411

theorem tailTrace_5881080 : CollatzResearch.WordTrace tailWord_5881080 prefixEnd_5881080 3019820807543955481153411 := by
  unfold tailWord_5881080
  simp only [CollatzResearch.WordTrace]
  refine ⟨107250304766929521672032347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143000406355906028896043129 107250304766929521672032347)
  ·
    refine ⟨160875457150394282508048521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107250304766929521672032347 160875457150394282508048521)
    ·
      refine ⟨120656592862795711881036391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160875457150394282508048521 120656592862795711881036391)
      ·
        refine ⟨180984889294193567821554587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120656592862795711881036391 180984889294193567821554587)
        ·
          refine ⟨271477333941290351732331881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180984889294193567821554587 271477333941290351732331881)
          ·
            refine ⟨203608000455967763799248911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271477333941290351732331881 203608000455967763799248911)
            ·
              refine ⟨305412000683951645698873367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203608000455967763799248911 305412000683951645698873367)
              ·
                refine ⟨458118001025927468548310051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305412000683951645698873367 458118001025927468548310051)
                ·
                  refine ⟨687177001538891202822465077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458118001025927468548310051 687177001538891202822465077)
                  ·
                    refine ⟨64422843894271050264606101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 687177001538891202822465077 64422843894271050264606101)
                    ·
                      refine ⟨3019820807543955481153411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64422843894271050264606101 3019820807543955481153411)
                      ·
                        rfl

theorem cell23_5881080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_5881080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881080 prefixEnd_5881080 := by exact prefixLift 5881080
  have htrace : WordTrace (prefixWord ++ tailWord_5881080) baseStart_5881080 baseEnd_5881080 := by
    simpa [prefixWord, tailWord_5881080, baseEnd_5881080] using wordTrace_append hprefix tailTrace_5881080
  have hstable : (prefixWord ++ tailWord_5881080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881080).length < 2 ^ (prefixWord ++ tailWord_5881080).sum := by decide
  have hdescent : baseEnd_5881080 < baseStart_5881080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881087 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 3]
def baseStart_5881087 : Nat := 118140960795 + 5881087 * 2 ^ 59
def prefixEnd_5881087 : Nat := 4983230072969 + 3 ^ 40 * 5881087 * 2
def baseEnd_5881087 : Nat := 3019824401908536953765879

theorem tailTrace_5881087 : CollatzResearch.WordTrace tailWord_5881087 prefixEnd_5881087 3019824401908536953765879 := by
  unfold tailWord_5881087
  simp only [CollatzResearch.WordTrace]
  refine ⟨214500864844833683539569515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143000576563222455693046343 214500864844833683539569515)
  ·
    refine ⟨321751297267250525309354273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214500864844833683539569515 321751297267250525309354273)
    ·
      refine ⟨241313472950437893982015705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321751297267250525309354273 241313472950437893982015705)
      ·
        refine ⟨180985104712828420486511779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241313472950437893982015705 180985104712828420486511779)
        ·
          refine ⟨271477657069242630729767669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180985104712828420486511779 271477657069242630729767669)
          ·
            refine ⟨25451030350241496630915719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 271477657069242630729767669 25451030350241496630915719)
            ·
              refine ⟨38176545525362244946373579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25451030350241496630915719 38176545525362244946373579)
              ·
                refine ⟨57264818288043367419560369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38176545525362244946373579 57264818288043367419560369)
                ·
                  refine ⟨42948613716032525564670277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57264818288043367419560369 42948613716032525564670277)
                  ·
                    refine ⟨8052865071756098543375677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42948613716032525564670277 8052865071756098543375677)
                    ·
                      refine ⟨3019824401908536953765879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8052865071756098543375677 3019824401908536953765879)
                      ·
                        rfl

theorem cell23_5881087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_5881087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881087 prefixEnd_5881087 := by exact prefixLift 5881087
  have htrace : WordTrace (prefixWord ++ tailWord_5881087) baseStart_5881087 baseEnd_5881087 := by
    simpa [prefixWord, tailWord_5881087, baseEnd_5881087] using wordTrace_append hprefix tailTrace_5881087
  have hstable : (prefixWord ++ tailWord_5881087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881087).length < 2 ^ (prefixWord ++ tailWord_5881087).sum := by decide
  have hdescent : baseEnd_5881087 < baseStart_5881087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881097 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_5881097 : Nat := 118140960795 + 5881097 * 2 ^ 59
def prefixEnd_5881097 : Nat := 4983230072969 + 3 ^ 40 * 5881097 * 2
def baseEnd_5881097 : Nat := 3019829536715081914640833

theorem tailTrace_5881097 : CollatzResearch.WordTrace tailWord_5881097 prefixEnd_5881097 3019829536715081914640833 := by
  unfold tailWord_5881097
  simp only [CollatzResearch.WordTrace]
  refine ⟨214501229574797455247433545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143000819716531636831622363 214501229574797455247433545)
  ·
    refine ⟨160875922181098091435575159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214501229574797455247433545 160875922181098091435575159)
    ·
      refine ⟨241313883271647137153362739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160875922181098091435575159 241313883271647137153362739)
      ·
        refine ⟨361970824907470705730044109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241313883271647137153362739 361970824907470705730044109)
        ·
          refine ⟨135739059340301514648766541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361970824907470705730044109 135739059340301514648766541)
          ·
            refine ⟨50902147252613067993287453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135739059340301514648766541 50902147252613067993287453)
            ·
              refine ⟨19088305219729900497482795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50902147252613067993287453 19088305219729900497482795)
              ·
                refine ⟨28632457829594850746224193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19088305219729900497482795 28632457829594850746224193)
                ·
                  refine ⟨21474343372196138059668145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28632457829594850746224193 21474343372196138059668145)
                  ·
                    refine ⟨16105757529147103544751109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21474343372196138059668145 16105757529147103544751109)
                    ·
                      refine ⟨3019829536715081914640833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16105757529147103544751109 3019829536715081914640833)
                      ·
                        rfl

theorem cell23_5881097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_5881097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881097 prefixEnd_5881097 := by exact prefixLift 5881097
  have htrace : WordTrace (prefixWord ++ tailWord_5881097) baseStart_5881097 baseEnd_5881097 := by
    simpa [prefixWord, tailWord_5881097, baseEnd_5881097] using wordTrace_append hprefix tailTrace_5881097
  have hstable : (prefixWord ++ tailWord_5881097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881097).length < 2 ^ (prefixWord ++ tailWord_5881097).sum := by decide
  have hdescent : baseEnd_5881097 < baseStart_5881097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881122 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_5881122 : Nat := 118140960795 + 5881122 * 2 ^ 59
def prefixEnd_5881122 : Nat := 4983230072969 + 3 ^ 40 * 5881122 * 2
def baseEnd_5881122 : Nat := 3019842373731444316828219

theorem tailTrace_5881122 : CollatzResearch.WordTrace tailWord_5881122 prefixEnd_5881122 3019842373731444316828219 := by
  unfold tailWord_5881122
  simp only [CollatzResearch.WordTrace]
  refine ⟨53625535349926721129273405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143001427599804589678062413 53625535349926721129273405)
  ·
    refine ⟨20109575756222520423477527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53625535349926721129273405 20109575756222520423477527)
    ·
      refine ⟨30164363634333780635216291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20109575756222520423477527 30164363634333780635216291)
      ·
        refine ⟨45246545451500670952824437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30164363634333780635216291 45246545451500670952824437)
        ·
          refine ⟨4241863636078187901827291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45246545451500670952824437 4241863636078187901827291)
          ·
            refine ⟨6362795454117281852740937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4241863636078187901827291 6362795454117281852740937)
            ·
              refine ⟨4772096590587961389555703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6362795454117281852740937 4772096590587961389555703)
              ·
                refine ⟨7158144885881942084333555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772096590587961389555703 7158144885881942084333555)
                ·
                  refine ⟨10737217328822913126500333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7158144885881942084333555 10737217328822913126500333)
                  ·
                    refine ⟨4026456498308592422437625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10737217328822913126500333 4026456498308592422437625)
                    ·
                      refine ⟨3019842373731444316828219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4026456498308592422437625 3019842373731444316828219)
                      ·
                        rfl

theorem cell23_5881122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_5881122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881122 prefixEnd_5881122 := by exact prefixLift 5881122
  have htrace : WordTrace (prefixWord ++ tailWord_5881122) baseStart_5881122 baseEnd_5881122 := by
    simpa [prefixWord, tailWord_5881122, baseEnd_5881122] using wordTrace_append hprefix tailTrace_5881122
  have hstable : (prefixWord ++ tailWord_5881122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881122).length < 2 ^ (prefixWord ++ tailWord_5881122).sum := by decide
  have hdescent : baseEnd_5881122 < baseStart_5881122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881191 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_5881191 : Nat := 118140960795 + 5881191 * 2 ^ 59
def prefixEnd_5881191 : Nat := 4983230072969 + 3 ^ 40 * 5881191 * 2
def baseEnd_5881191 : Nat := 3019877803896604546865401

theorem tailTrace_5881191 : CollatzResearch.WordTrace tailWord_5881191 prefixEnd_5881191 3019877803896604546865401 := by
  unfold tailWord_5881191
  simp only [CollatzResearch.WordTrace]
  refine ⟨214504658036456909301355427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143003105357637939534236951 214504658036456909301355427)
  ·
    refine ⟨321756987054685363952033141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214504658036456909301355427 321756987054685363952033141)
    ·
      refine ⟨30164717536376752870503107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321756987054685363952033141 30164717536376752870503107)
      ·
        refine ⟨45247076304565129305754661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30164717536376752870503107 45247076304565129305754661)
        ·
          refine ⟨8483826807105961744828999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45247076304565129305754661 8483826807105961744828999)
          ·
            refine ⟨12725740210658942617243499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483826807105961744828999 12725740210658942617243499)
            ·
              refine ⟨19088610315988413925865249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12725740210658942617243499 19088610315988413925865249)
              ·
                refine ⟨14316457736991310444398937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19088610315988413925865249 14316457736991310444398937)
                ·
                  refine ⟨10737343302743482833299203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14316457736991310444398937 10737343302743482833299203)
                  ·
                    refine ⟨16106014954115224249948805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10737343302743482833299203 16106014954115224249948805)
                    ·
                      refine ⟨3019877803896604546865401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16106014954115224249948805 3019877803896604546865401)
                      ·
                        rfl

theorem cell23_5881191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_5881191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881191 prefixEnd_5881191 := by exact prefixLift 5881191
  have htrace : WordTrace (prefixWord ++ tailWord_5881191) baseStart_5881191 baseEnd_5881191 := by
    simpa [prefixWord, tailWord_5881191, baseEnd_5881191] using wordTrace_append hprefix tailTrace_5881191
  have hstable : (prefixWord ++ tailWord_5881191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881191).length < 2 ^ (prefixWord ++ tailWord_5881191).sum := by decide
  have hdescent : baseEnd_5881191 < baseStart_5881191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881201 : List Nat := [1, 2, 2, 2, 1, 2, 2, 6, 1, 4]
def baseStart_5881201 : Nat := 118140960795 + 5881201 * 2 ^ 59
def prefixEnd_5881201 : Nat := 4983230072969 + 3 ^ 40 * 5881201 * 2
def baseEnd_5881201 : Nat := 1006627646234383169246785

theorem tailTrace_5881201 : CollatzResearch.WordTrace tailWord_5881201 prefixEnd_5881201 1006627646234383169246785 := by
  unfold tailWord_5881201
  simp only [CollatzResearch.WordTrace]
  refine ⟨214505022766420681009219457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143003348510947120672812971 214505022766420681009219457)
  ·
    refine ⟨160878767074815510756914593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214505022766420681009219457 160878767074815510756914593)
    ·
      refine ⟨120659075306111633067685945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160878767074815510756914593 120659075306111633067685945)
      ·
        refine ⟨90494306479583724800764459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120659075306111633067685945 90494306479583724800764459)
        ·
          refine ⟨135741459719375587201146689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90494306479583724800764459 135741459719375587201146689)
          ·
            refine ⟨101806094789531690400860017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135741459719375587201146689 101806094789531690400860017)
            ·
              refine ⟨76354571092148767800645013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101806094789531690400860017 76354571092148767800645013)
              ·
                refine ⟨3579120519944473490655235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76354571092148767800645013 3579120519944473490655235)
                ·
                  refine ⟨5368680779916710235982853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579120519944473490655235 5368680779916710235982853)
                  ·
                    refine ⟨1006627646234383169246785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5368680779916710235982853 1006627646234383169246785)
                    ·
                      rfl

theorem cell23_5881201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_5881201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881201 prefixEnd_5881201 := by exact prefixLift 5881201
  have htrace : WordTrace (prefixWord ++ tailWord_5881201) baseStart_5881201 baseEnd_5881201 := by
    simpa [prefixWord, tailWord_5881201, baseEnd_5881201] using wordTrace_append hprefix tailTrace_5881201
  have hstable : (prefixWord ++ tailWord_5881201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881201).length < 2 ^ (prefixWord ++ tailWord_5881201).sum := by decide
  have hdescent : baseEnd_5881201 < baseStart_5881201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881251 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 2, 3, 2]
def baseStart_5881251 : Nat := 118140960795 + 5881251 * 2 ^ 59
def prefixEnd_5881251 : Nat := 4983230072969 + 3 ^ 40 * 5881251 * 2
def baseEnd_5881251 : Nat := 3019908612735874312115125

theorem tailTrace_5881251 : CollatzResearch.WordTrace tailWord_5881251 prefixEnd_5881251 3019908612735874312115125 := by
  unfold tailWord_5881251
  simp only [CollatzResearch.WordTrace]
  refine ⟨214506846416239539548539607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143004564277493026365693071 214506846416239539548539607)
  ·
    refine ⟨321760269624359309322809411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214506846416239539548539607 321760269624359309322809411)
    ·
      refine ⟨482640404436538963984214117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321760269624359309322809411 482640404436538963984214117)
      ·
        refine ⟨90495075831851055747040147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 482640404436538963984214117 90495075831851055747040147)
        ·
          refine ⟨135742613747776583620560221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90495075831851055747040147 135742613747776583620560221)
          ·
            refine ⟨50903480155416218857710083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135742613747776583620560221 50903480155416218857710083)
            ·
              refine ⟨76355220233124328286565125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50903480155416218857710083 76355220233124328286565125)
              ·
                refine ⟨14316603793710811553730961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76355220233124328286565125 14316603793710811553730961)
                ·
                  refine ⟨10737452845283108665298221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14316603793710811553730961 10737452845283108665298221)
                  ·
                    refine ⟨4026544816981165749486833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10737452845283108665298221 4026544816981165749486833)
                    ·
                      refine ⟨3019908612735874312115125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4026544816981165749486833 3019908612735874312115125)
                      ·
                        rfl

theorem cell23_5881251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_5881251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881251 prefixEnd_5881251 := by exact prefixLift 5881251
  have htrace : WordTrace (prefixWord ++ tailWord_5881251) baseStart_5881251 baseEnd_5881251 := by
    simpa [prefixWord, tailWord_5881251, baseEnd_5881251] using wordTrace_append hprefix tailTrace_5881251
  have hstable : (prefixWord ++ tailWord_5881251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881251).length < 2 ^ (prefixWord ++ tailWord_5881251).sum := by decide
  have hdescent : baseEnd_5881251 < baseStart_5881251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881261 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_5881261 : Nat := 118140960795 + 5881261 * 2 ^ 59
def prefixEnd_5881261 : Nat := 4983230072969 + 3 ^ 40 * 5881261 * 2
def baseEnd_5881261 : Nat := 1006637915847473090996693

theorem tailTrace_5881261 : CollatzResearch.WordTrace tailWord_5881261 prefixEnd_5881261 1006637915847473090996693 := by
  unfold tailWord_5881261
  simp only [CollatzResearch.WordTrace]
  refine ⟨214507211146203311256403637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143004807430802207504269091 214507211146203311256403637)
  ·
    refine ⟨20110051044956560430287841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214507211146203311256403637 20110051044956560430287841)
    ·
      refine ⟨15082538283717420322715881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20110051044956560430287841 15082538283717420322715881)
      ·
        refine ⟨11311903712788065242036911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15082538283717420322715881 11311903712788065242036911)
        ·
          refine ⟨16967855569182097863055367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11311903712788065242036911 16967855569182097863055367)
          ·
            refine ⟨25451783353773146794583051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16967855569182097863055367 25451783353773146794583051)
            ·
              refine ⟨38177675030659720191874577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25451783353773146794583051 38177675030659720191874577)
              ·
                refine ⟨28633256272994790143905933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38177675030659720191874577 28633256272994790143905933)
                ·
                  refine ⟨10737471102373046303964725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28633256272994790143905933 10737471102373046303964725)
                  ·
                    refine ⟨1006637915847473090996693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10737471102373046303964725 1006637915847473090996693)
                    ·
                      rfl

theorem cell23_5881261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_5881261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881261 prefixEnd_5881261 := by exact prefixLift 5881261
  have htrace : WordTrace (prefixWord ++ tailWord_5881261) baseStart_5881261 baseEnd_5881261 := by
    simpa [prefixWord, tailWord_5881261, baseEnd_5881261] using wordTrace_append hprefix tailTrace_5881261
  have hstable : (prefixWord ++ tailWord_5881261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881261).length < 2 ^ (prefixWord ++ tailWord_5881261).sum := by decide
  have hdescent : baseEnd_5881261 < baseStart_5881261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881274 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_5881274 : Nat := 118140960795 + 5881274 * 2 ^ 59
def prefixEnd_5881274 : Nat := 4983230072969 + 3 ^ 40 * 5881274 * 2
def baseEnd_5881274 : Nat := 1006640140930309240709173

theorem tailTrace_5881274 : CollatzResearch.WordTrace tailWord_5881274 prefixEnd_5881274 1006640140930309240709173 := by
  unfold tailWord_5881274
  simp only [CollatzResearch.WordTrace]
  refine ⟨53626921323789053619156719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143005123530104142984417917 53626921323789053619156719)
  ·
    refine ⟨80440381985683580428735079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53626921323789053619156719 80440381985683580428735079)
    ·
      refine ⟨120660572978525370643102619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80440381985683580428735079 120660572978525370643102619)
      ·
        refine ⟨180990859467788055964653929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120660572978525370643102619 180990859467788055964653929)
        ·
          refine ⟨135743144600841041973490447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180990859467788055964653929 135743144600841041973490447)
          ·
            refine ⟨203614716901261562960235671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135743144600841041973490447 203614716901261562960235671)
            ·
              refine ⟨305422075351892344440353507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203614716901261562960235671 305422075351892344440353507)
              ·
                refine ⟨458133113027838516660530261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305422075351892344440353507 458133113027838516660530261)
                ·
                  refine ⟨5368747418294982617115589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 458133113027838516660530261 5368747418294982617115589)
                  ·
                    refine ⟨1006640140930309240709173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5368747418294982617115589 1006640140930309240709173)
                    ·
                      rfl

theorem cell23_5881274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_5881274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881274 prefixEnd_5881274 := by exact prefixLift 5881274
  have htrace : WordTrace (prefixWord ++ tailWord_5881274) baseStart_5881274 baseEnd_5881274 := by
    simpa [prefixWord, tailWord_5881274, baseEnd_5881274] using wordTrace_append hprefix tailTrace_5881274
  have hstable : (prefixWord ++ tailWord_5881274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881274).length < 2 ^ (prefixWord ++ tailWord_5881274).sum := by decide
  have hdescent : baseEnd_5881274 < baseStart_5881274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881315 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 3, 2, 2]
def baseStart_5881315 : Nat := 118140960795 + 5881315 * 2 ^ 59
def prefixEnd_5881315 : Nat := 4983230072969 + 3 ^ 40 * 5881315 * 2
def baseEnd_5881315 : Nat := 3019941475497762061714831

theorem tailTrace_5881315 : CollatzResearch.WordTrace tailWord_5881315 prefixEnd_5881315 3019941475497762061714831 := by
  unfold tailWord_5881315
  simp only [CollatzResearch.WordTrace]
  refine ⟨214509180688007678478869399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143006120458671785652579599 214509180688007678478869399)
  ·
    refine ⟨321763771032011517718304099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214509180688007678478869399 321763771032011517718304099)
    ·
      refine ⟨482645656548017276577456149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321763771032011517718304099 482645656548017276577456149)
      ·
        refine ⟨22624015150688309839568257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 482645656548017276577456149 22624015150688309839568257)
        ·
          refine ⟨16968011363016232379676193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22624015150688309839568257 16968011363016232379676193)
          ·
            refine ⟨12726008522262174284757145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16968011363016232379676193 12726008522262174284757145)
            ·
              refine ⟨9544506391696630713567859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12726008522262174284757145 9544506391696630713567859)
              ·
                refine ⟨14316759587544946070351789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9544506391696630713567859 14316759587544946070351789)
                ·
                  refine ⟨5368784845329354776381921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14316759587544946070351789 5368784845329354776381921)
                  ·
                    refine ⟨4026588633997016082286441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5368784845329354776381921 4026588633997016082286441)
                    ·
                      refine ⟨3019941475497762061714831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4026588633997016082286441 3019941475497762061714831)
                      ·
                        rfl

theorem cell23_5881315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_5881315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881315 prefixEnd_5881315 := by exact prefixLift 5881315
  have htrace : WordTrace (prefixWord ++ tailWord_5881315) baseStart_5881315 baseEnd_5881315 := by
    simpa [prefixWord, tailWord_5881315, baseEnd_5881315] using wordTrace_append hprefix tailTrace_5881315
  have hstable : (prefixWord ++ tailWord_5881315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881315).length < 2 ^ (prefixWord ++ tailWord_5881315).sum := by decide
  have hdescent : baseEnd_5881315 < baseStart_5881315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881325 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_5881325 : Nat := 118140960795 + 5881325 * 2 ^ 59
def prefixEnd_5881325 : Nat := 4983230072969 + 3 ^ 40 * 5881325 * 2
def baseEnd_5881325 : Nat := 1006648870101435674196595

theorem tailTrace_5881325 : CollatzResearch.WordTrace tailWord_5881325 prefixEnd_5881325 1006648870101435674196595 := by
  unfold tailWord_5881325
  simp only [CollatzResearch.WordTrace]
  refine ⟨214509545417971450186733429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143006363611980966791155619 214509545417971450186733429)
  ·
    refine ⟨20110269882934823455006259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214509545417971450186733429 20110269882934823455006259)
    ·
      refine ⟨30165404824402235182509389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20110269882934823455006259 30165404824402235182509389)
      ·
        refine ⟨11312026809150838193441021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30165404824402235182509389 11312026809150838193441021)
        ·
          refine ⟨4242010053431564322540383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11312026809150838193441021 4242010053431564322540383)
          ·
            refine ⟨6363015080147346483810575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242010053431564322540383 6363015080147346483810575)
            ·
              refine ⟨9544522620221019725715863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6363015080147346483810575 9544522620221019725715863)
              ·
                refine ⟨14316783930331529588573795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9544522620221019725715863 14316783930331529588573795)
                ·
                  refine ⟨21475175895497294382860693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14316783930331529588573795 21475175895497294382860693)
                  ·
                    refine ⟨1006648870101435674196595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21475175895497294382860693 1006648870101435674196595)
                    ·
                      rfl

theorem cell23_5881325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_5881325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881325 prefixEnd_5881325 := by exact prefixLift 5881325
  have htrace : WordTrace (prefixWord ++ tailWord_5881325) baseStart_5881325 baseEnd_5881325 := by
    simpa [prefixWord, tailWord_5881325, baseEnd_5881325] using wordTrace_append hprefix tailTrace_5881325
  have hstable : (prefixWord ++ tailWord_5881325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881325).length < 2 ^ (prefixWord ++ tailWord_5881325).sum := by decide
  have hdescent : baseEnd_5881325 < baseStart_5881325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881394 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 9]
def baseStart_5881394 : Nat := 118140960795 + 5881394 * 2 ^ 59
def prefixEnd_5881394 : Nat := 4983230072969 + 3 ^ 40 * 5881394 * 2
def baseEnd_5881394 : Nat := 335553560052163028069663

theorem tailTrace_5881394 : CollatzResearch.WordTrace tailWord_5881394 prefixEnd_5881394 335553560052163028069663 := by
  unfold tailWord_5881394
  simp only [CollatzResearch.WordTrace]
  refine ⟨53628015513680368742748809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143008041369814316647330157 53628015513680368742748809)
  ·
    refine ⟨40221011635260276557061607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53628015513680368742748809 40221011635260276557061607)
    ·
      refine ⟨60331517452890414835592411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40221011635260276557061607 60331517452890414835592411)
      ·
        refine ⟨90497276179335622253388617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60331517452890414835592411 90497276179335622253388617)
        ·
          refine ⟨67872957134501716690041463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90497276179335622253388617 67872957134501716690041463)
          ·
            refine ⟨101809435701752575035062195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67872957134501716690041463 101809435701752575035062195)
            ·
              refine ⟨152714153552628862552593293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101809435701752575035062195 152714153552628862552593293)
              ·
                refine ⟨57267807582235823457222485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152714153552628862552593293 57267807582235823457222485)
                ·
                  refine ⟨335553560052163028069663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57267807582235823457222485 335553560052163028069663)
                  ·
                    rfl

theorem cell23_5881394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_5881394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881394 prefixEnd_5881394 := by exact prefixLift 5881394
  have htrace : WordTrace (prefixWord ++ tailWord_5881394) baseStart_5881394 baseEnd_5881394 := by
    simpa [prefixWord, tailWord_5881394, baseEnd_5881394] using wordTrace_append hprefix tailTrace_5881394
  have hstable : (prefixWord ++ tailWord_5881394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881394).length < 2 ^ (prefixWord ++ tailWord_5881394).sum := by decide
  have hdescent : baseEnd_5881394 < baseStart_5881394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881405 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_5881405 : Nat := 118140960795 + 5881405 * 2 ^ 59
def prefixEnd_5881405 : Nat := 4983230072969 + 3 ^ 40 * 5881405 * 2
def baseEnd_5881405 : Nat := 3019987688756666709589417

theorem tailTrace_5881405 : CollatzResearch.WordTrace tailWord_5881405 prefixEnd_5881405 3019987688756666709589417 := by
  unfold tailWord_5881405
  simp only [CollatzResearch.WordTrace]
  refine ⟨214512463257681623849645669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143008308838454415899763779 214512463257681623849645669)
  ·
    refine ⟨40221086860815304471808563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214512463257681623849645669 40221086860815304471808563)
    ·
      refine ⟨60331630291222956707712845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40221086860815304471808563 60331630291222956707712845)
      ·
        refine ⟨22624361359208608765392317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60331630291222956707712845 22624361359208608765392317)
        ·
          refine ⟨8484135509703228287022119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22624361359208608765392317 8484135509703228287022119)
          ·
            refine ⟨12726203264554842430533179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8484135509703228287022119 12726203264554842430533179)
            ·
              refine ⟨19089304896832263645799769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12726203264554842430533179 19089304896832263645799769)
              ·
                refine ⟨14316978672624197734349827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19089304896832263645799769 14316978672624197734349827)
                ·
                  refine ⟨21475468008936296601524741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14316978672624197734349827 21475468008936296601524741)
                  ·
                    refine ⟨4026650251675555612785889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21475468008936296601524741 4026650251675555612785889)
                    ·
                      refine ⟨3019987688756666709589417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4026650251675555612785889 3019987688756666709589417)
                      ·
                        rfl

theorem cell23_5881405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_5881405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881405 prefixEnd_5881405 := by exact prefixLift 5881405
  have htrace : WordTrace (prefixWord ++ tailWord_5881405) baseStart_5881405 baseEnd_5881405 := by
    simpa [prefixWord, tailWord_5881405, baseEnd_5881405] using wordTrace_append hprefix tailTrace_5881405
  have hstable : (prefixWord ++ tailWord_5881405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881405).length < 2 ^ (prefixWord ++ tailWord_5881405).sum := by decide
  have hdescent : baseEnd_5881405 < baseStart_5881405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881428 : List Nat := [2, 4, 1, 1, 1, 2, 3, 4, 5]
def baseStart_5881428 : Nat := 118140960795 + 5881428 * 2 ^ 59
def prefixEnd_5881428 : Nat := 4983230072969 + 3 ^ 40 * 5881428 * 2
def baseEnd_5881428 : Nat := 335555499867968902177979

theorem tailTrace_5881428 : CollatzResearch.WordTrace tailWord_5881428 prefixEnd_5881428 335555499867968902177979 := by
  unfold tailWord_5881428
  simp only [CollatzResearch.WordTrace]
  refine ⟨107256651068299149388866469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143008868091065532518488625 107256651068299149388866469)
  ·
    refine ⟨20110622075306090510412463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107256651068299149388866469 20110622075306090510412463)
    ·
      refine ⟨30165933112959135765618695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20110622075306090510412463 30165933112959135765618695)
      ·
        refine ⟨45248899669438703648428043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30165933112959135765618695 45248899669438703648428043)
        ·
          refine ⟨67873349504158055472642065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45248899669438703648428043 67873349504158055472642065)
          ·
            refine ⟨50905012128118541604481549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67873349504158055472642065 50905012128118541604481549)
            ·
              refine ⟨19089379548044453101680581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50905012128118541604481549 19089379548044453101680581)
              ·
                refine ⟨3579258665258334956565109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19089379548044453101680581 3579258665258334956565109)
                ·
                  refine ⟨335555499867968902177979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579258665258334956565109 335555499867968902177979)
                  ·
                    rfl

theorem cell23_5881428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_5881428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881428 prefixEnd_5881428 := by exact prefixLift 5881428
  have htrace : WordTrace (prefixWord ++ tailWord_5881428) baseStart_5881428 baseEnd_5881428 := by
    simpa [prefixWord, tailWord_5881428, baseEnd_5881428] using wordTrace_append hprefix tailTrace_5881428
  have hstable : (prefixWord ++ tailWord_5881428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881428).length < 2 ^ (prefixWord ++ tailWord_5881428).sum := by decide
  have hdescent : baseEnd_5881428 < baseStart_5881428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881458 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_5881458 : Nat := 118140960795 + 5881458 * 2 ^ 59
def prefixEnd_5881458 : Nat := 4983230072969 + 3 ^ 40 * 5881458 * 2
def baseEnd_5881458 : Nat := 1006671634410451667408891

theorem tailTrace_5881458 : CollatzResearch.WordTrace tailWord_5881458 prefixEnd_5881458 1006671634410451667408891 := by
  unfold tailWord_5881458
  simp only [CollatzResearch.WordTrace]
  refine ⟨53628599081622403475331257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143009597550993075934216685 53628599081622403475331257)
  ·
    refine ⟨40221449311216802606498443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53628599081622403475331257 40221449311216802606498443)
    ·
      refine ⟨60332173966825203909747665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40221449311216802606498443 60332173966825203909747665)
      ·
        refine ⟨45249130475118902932310749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60332173966825203909747665 45249130475118902932310749)
        ·
          refine ⟨16968423928169588599616531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45249130475118902932310749 16968423928169588599616531)
          ·
            refine ⟨25452635892254382899424797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16968423928169588599616531 25452635892254382899424797)
            ·
              refine ⟨9544738459595393587284299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25452635892254382899424797 9544738459595393587284299)
              ·
                refine ⟨14317107689393090380926449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9544738459595393587284299 14317107689393090380926449)
                ·
                  refine ⟨10737830767044817785694837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14317107689393090380926449 10737830767044817785694837)
                  ·
                    refine ⟨1006671634410451667408891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10737830767044817785694837 1006671634410451667408891)
                    ·
                      rfl

theorem cell23_5881458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_5881458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881458 prefixEnd_5881458 := by exact prefixLift 5881458
  have htrace : WordTrace (prefixWord ++ tailWord_5881458) baseStart_5881458 baseEnd_5881458 := by
    simpa [prefixWord, tailWord_5881458, baseEnd_5881458] using wordTrace_append hprefix tailTrace_5881458
  have hstable : (prefixWord ++ tailWord_5881458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881458).length < 2 ^ (prefixWord ++ tailWord_5881458).sum := by decide
  have hdescent : baseEnd_5881458 < baseStart_5881458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881464 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_5881464 : Nat := 118140960795 + 5881464 * 2 ^ 59
def prefixEnd_5881464 : Nat := 4983230072969 + 3 ^ 40 * 5881464 * 2
def baseEnd_5881464 : Nat := 3020017984115281978751645

theorem tailTrace_5881464 : CollatzResearch.WordTrace tailWord_5881464 prefixEnd_5881464 3020017984115281978751645 := by
  unfold tailWord_5881464
  simp only [CollatzResearch.WordTrace]
  refine ⟨107257307582233938463021723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143009743442978584617362297 107257307582233938463021723)
  ·
    refine ⟨160885961373350907694532585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107257307582233938463021723 160885961373350907694532585)
    ·
      refine ⟨120664471030013180770899439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160885961373350907694532585 120664471030013180770899439)
      ·
        refine ⟨180996706545019771156349159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120664471030013180770899439 180996706545019771156349159)
        ·
          refine ⟨271495059817529656734523739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180996706545019771156349159 271495059817529656734523739)
          ·
            refine ⟨407242589726294485101785609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271495059817529656734523739 407242589726294485101785609)
            ·
              refine ⟨305431942294720863826339207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407242589726294485101785609 305431942294720863826339207)
              ·
                refine ⟨458147913442081295739508811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305431942294720863826339207 458147913442081295739508811)
                ·
                  refine ⟨687221870163121943609263217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458147913442081295739508811 687221870163121943609263217)
                  ·
                    refine ⟨515416402622341457706947413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 687221870163121943609263217 515416402622341457706947413)
                    ·
                      refine ⟨3020017984115281978751645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 515416402622341457706947413 3020017984115281978751645)
                      ·
                        rfl

theorem cell23_5881464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_5881464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881464 prefixEnd_5881464 := by exact prefixLift 5881464
  have htrace : WordTrace (prefixWord ++ tailWord_5881464) baseStart_5881464 baseEnd_5881464 := by
    simpa [prefixWord, tailWord_5881464, baseEnd_5881464] using wordTrace_append hprefix tailTrace_5881464
  have hstable : (prefixWord ++ tailWord_5881464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881464).length < 2 ^ (prefixWord ++ tailWord_5881464).sum := by decide
  have hdescent : baseEnd_5881464 < baseStart_5881464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881528 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 5, 1, 3]
def baseStart_5881528 : Nat := 118140960795 + 5881528 * 2 ^ 59
def prefixEnd_5881528 : Nat := 4983230072969 + 3 ^ 40 * 5881528 * 2
def baseEnd_5881528 : Nat := 3020050846877169728351351

theorem tailTrace_5881528 : CollatzResearch.WordTrace tailWord_5881528 prefixEnd_5881528 3020050846877169728351351 := by
  unfold tailWord_5881528
  simp only [CollatzResearch.WordTrace]
  refine ⟨107258474718118007928186619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143011299624157343904248825 107258474718118007928186619)
  ·
    refine ⟨160887712077177011892279929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107258474718118007928186619 160887712077177011892279929)
    ·
      refine ⟨120665784057882758919209947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160887712077177011892279929 120665784057882758919209947)
      ·
        refine ⟨180998676086824138378814921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120665784057882758919209947 180998676086824138378814921)
        ·
          refine ⟨135749007065118103784111191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180998676086824138378814921 135749007065118103784111191)
          ·
            refine ⟨203623510597677155676166787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135749007065118103784111191 203623510597677155676166787)
            ·
              refine ⟨305435265896515733514250181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203623510597677155676166787 305435265896515733514250181)
              ·
                refine ⟨57269112355596700033921909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305435265896515733514250181 57269112355596700033921909)
                ·
                  refine ⟨5368979283337190628180179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57269112355596700033921909 5368979283337190628180179)
                  ·
                    refine ⟨8053468925005785942270269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5368979283337190628180179 8053468925005785942270269)
                    ·
                      refine ⟨3020050846877169728351351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8053468925005785942270269 3020050846877169728351351)
                      ·
                        rfl

theorem cell23_5881528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_5881528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881528 prefixEnd_5881528 := by exact prefixLift 5881528
  have htrace : WordTrace (prefixWord ++ tailWord_5881528) baseStart_5881528 baseEnd_5881528 := by
    simpa [prefixWord, tailWord_5881528, baseEnd_5881528] using wordTrace_append hprefix tailTrace_5881528
  have hstable : (prefixWord ++ tailWord_5881528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881528).length < 2 ^ (prefixWord ++ tailWord_5881528).sum := by decide
  have hdescent : baseEnd_5881528 < baseStart_5881528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881568 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 2, 6, 2]
def baseStart_5881568 : Nat := 118140960795 + 5881568 * 2 ^ 59
def prefixEnd_5881568 : Nat := 4983230072969 + 3 ^ 40 * 5881568 * 2
def baseEnd_5881568 : Nat := 3020071386103349571851167

theorem tailTrace_5881568 : CollatzResearch.WordTrace tailWord_5881568 prefixEnd_5881568 3020071386103349571851167 := by
  unfold tailWord_5881568
  simp only [CollatzResearch.WordTrace]
  refine ⟨107259204178045551343914679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143012272237394068458552905 107259204178045551343914679)
  ·
    refine ⟨160888806267068327015872019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107259204178045551343914679 160888806267068327015872019)
    ·
      refine ⟨241333209400602490523808029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160888806267068327015872019 241333209400602490523808029)
      ·
        refine ⟨90499953525225933946428011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241333209400602490523808029 90499953525225933946428011)
        ·
          refine ⟨135749930287838900919642017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90499953525225933946428011 135749930287838900919642017)
          ·
            refine ⟨101812447715879175689731513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135749930287838900919642017 101812447715879175689731513)
            ·
              refine ⟨76359335786909381767298635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101812447715879175689731513 76359335786909381767298635)
              ·
                refine ⟨114539003680364072650947953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76359335786909381767298635 114539003680364072650947953)
                ·
                  refine ⟨85904252760273054488210965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114539003680364072650947953 85904252760273054488210965)
                  ·
                    refine ⟨4026761848137799429134889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85904252760273054488210965 4026761848137799429134889)
                    ·
                      refine ⟨3020071386103349571851167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4026761848137799429134889 3020071386103349571851167)
                      ·
                        rfl

theorem cell23_5881568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_5881568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881568 prefixEnd_5881568 := by exact prefixLift 5881568
  have htrace : WordTrace (prefixWord ++ tailWord_5881568) baseStart_5881568 baseEnd_5881568 := by
    simpa [prefixWord, tailWord_5881568, baseEnd_5881568] using wordTrace_append hprefix tailTrace_5881568
  have hstable : (prefixWord ++ tailWord_5881568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881568).length < 2 ^ (prefixWord ++ tailWord_5881568).sum := by decide
  have hdescent : baseEnd_5881568 < baseStart_5881568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881578 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_5881578 : Nat := 118140960795 + 5881578 * 2 ^ 59
def prefixEnd_5881578 : Nat := 4983230072969 + 3 ^ 40 * 5881578 * 2
def baseEnd_5881578 : Nat := 1006692173636631510908707

theorem tailTrace_5881578 : CollatzResearch.WordTrace tailWord_5881578 prefixEnd_5881578 1006692173636631510908707 := by
  unfold tailWord_5881578
  simp only [CollatzResearch.WordTrace]
  refine ⟨53629693271513718598923347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143012515390703249597128925 53629693271513718598923347)
  ·
    refine ⟨80444539907270577898385021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53629693271513718598923347 80444539907270577898385021)
    ·
      refine ⟨30166702465226466711894383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80444539907270577898385021 30166702465226466711894383)
      ·
        refine ⟨45250053697839700067841575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30166702465226466711894383 45250053697839700067841575)
        ·
          refine ⟨67875080546759550101762363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45250053697839700067841575 67875080546759550101762363)
          ·
            refine ⟨101812620820139325152643545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67875080546759550101762363 101812620820139325152643545)
            ·
              refine ⟨76359465615104493864482659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101812620820139325152643545 76359465615104493864482659)
              ·
                refine ⟨114539198422656740796723989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76359465615104493864482659 114539198422656740796723989)
                ·
                  refine ⟨5369024926062034724846437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114539198422656740796723989 5369024926062034724846437)
                  ·
                    refine ⟨1006692173636631510908707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369024926062034724846437 1006692173636631510908707)
                    ·
                      rfl

theorem cell23_5881578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_5881578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881578 prefixEnd_5881578 := by exact prefixLift 5881578
  have htrace : WordTrace (prefixWord ++ tailWord_5881578) baseStart_5881578 baseEnd_5881578 := by
    simpa [prefixWord, tailWord_5881578, baseEnd_5881578] using wordTrace_append hprefix tailTrace_5881578
  have hstable : (prefixWord ++ tailWord_5881578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881578).length < 2 ^ (prefixWord ++ tailWord_5881578).sum := by decide
  have hdescent : baseEnd_5881578 < baseStart_5881578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881611 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 6]
def baseStart_5881611 : Nat := 118140960795 + 5881611 * 2 ^ 59
def prefixEnd_5881611 : Nat := 4983230072969 + 3 ^ 40 * 5881611 * 2
def baseEnd_5881611 : Nat := 3020093465771492903613469

theorem tailTrace_5881611 : CollatzResearch.WordTrace tailWord_5881611 prefixEnd_5881611 3020093465771492903613469 := by
  unfold tailWord_5881611
  simp only [CollatzResearch.WordTrace]
  refine ⟨214519976694935321031644687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143013317796623547354429791 214519976694935321031644687)
  ·
    refine ⟨321779965042402981547467031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214519976694935321031644687 321779965042402981547467031)
    ·
      refine ⟨482669947563604472321200547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321779965042402981547467031 482669947563604472321200547)
      ·
        refine ⟨724004921345406708481800821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482669947563604472321200547 724004921345406708481800821)
        ·
          refine ⟨67875461376131878920168827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 724004921345406708481800821 67875461376131878920168827)
          ·
            refine ⟨101813192064197818380253241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67875461376131878920168827 101813192064197818380253241)
            ·
              refine ⟨76359894048148363785189931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101813192064197818380253241 76359894048148363785189931)
              ·
                refine ⟨114539841072222545677784897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76359894048148363785189931 114539841072222545677784897)
                ·
                  refine ⟨85904880804166909258338673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114539841072222545677784897 85904880804166909258338673)
                  ·
                    refine ⟨64428660603125181943754005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85904880804166909258338673 64428660603125181943754005)
                    ·
                      refine ⟨3020093465771492903613469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64428660603125181943754005 3020093465771492903613469)
                      ·
                        rfl

theorem cell23_5881611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_5881611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881611 prefixEnd_5881611 := by exact prefixLift 5881611
  have htrace : WordTrace (prefixWord ++ tailWord_5881611) baseStart_5881611 baseEnd_5881611 := by
    simpa [prefixWord, tailWord_5881611, baseEnd_5881611] using wordTrace_append hprefix tailTrace_5881611
  have hstable : (prefixWord ++ tailWord_5881611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881611).length < 2 ^ (prefixWord ++ tailWord_5881611).sum := by decide
  have hdescent : baseEnd_5881611 < baseStart_5881611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881613 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_5881613 : Nat := 118140960795 + 5881613 * 2 ^ 59
def prefixEnd_5881613 : Nat := 4983230072969 + 3 ^ 40 * 5881613 * 2
def baseEnd_5881613 : Nat := 3020094492732801895788461

theorem tailTrace_5881613 : CollatzResearch.WordTrace tailWord_5881613 prefixEnd_5881613 3020094492732801895788461 := by
  unfold tailWord_5881613
  simp only [CollatzResearch.WordTrace]
  refine ⟨214520049640928075373217493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143013366427285383582144995 214520049640928075373217493)
  ·
    refine ⟨5027813663459251766559785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 214520049640928075373217493 5027813663459251766559785)
    ·
      refine ⟨3770860247594438824919839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5027813663459251766559785 3770860247594438824919839)
      ·
        refine ⟨5656290371391658237379759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770860247594438824919839 5656290371391658237379759)
        ·
          refine ⟨8484435557087487356069639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5656290371391658237379759 8484435557087487356069639)
          ·
            refine ⟨12726653335631231034104459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8484435557087487356069639 12726653335631231034104459)
            ·
              refine ⟨19089980003446846551156689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12726653335631231034104459 19089980003446846551156689)
              ·
                refine ⟨14317485002585134913367517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19089980003446846551156689 14317485002585134913367517)
                ·
                  refine ⟨5369056875969425592512819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14317485002585134913367517 5369056875969425592512819)
                  ·
                    refine ⟨8053585313954138388769229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5369056875969425592512819 8053585313954138388769229)
                    ·
                      refine ⟨3020094492732801895788461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8053585313954138388769229 3020094492732801895788461)
                      ·
                        rfl

theorem cell23_5881613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_5881613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881613 prefixEnd_5881613 := by exact prefixLift 5881613
  have htrace : WordTrace (prefixWord ++ tailWord_5881613) baseStart_5881613 baseEnd_5881613 := by
    simpa [prefixWord, tailWord_5881613, baseEnd_5881613] using wordTrace_append hprefix tailTrace_5881613
  have hstable : (prefixWord ++ tailWord_5881613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881613).length < 2 ^ (prefixWord ++ tailWord_5881613).sum := by decide
  have hdescent : baseEnd_5881613 < baseStart_5881613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881636 : List Nat := [2, 3, 1, 3, 2, 2, 2, 3, 1, 2, 2]
def baseStart_5881636 : Nat := 118140960795 + 5881636 * 2 ^ 59
def prefixEnd_5881636 : Nat := 4983230072969 + 3 ^ 40 * 5881636 * 2
def baseEnd_5881636 : Nat := 3020106302787855305800855

theorem tailTrace_5881636 : CollatzResearch.WordTrace tailWord_5881636 prefixEnd_5881636 3020106302787855305800855 := by
  unfold tailWord_5881636
  simp only [CollatzResearch.WordTrace]
  refine ⟨107260444259922375150652381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143013925679896500200869841 107260444259922375150652381)
  ·
    refine ⟨40222666597470890681494643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107260444259922375150652381 40222666597470890681494643)
    ·
      refine ⟨60333999896206336022241965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40222666597470890681494643 60333999896206336022241965)
      ·
        refine ⟨22625249961077376008340737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60333999896206336022241965 22625249961077376008340737)
        ·
          refine ⟨16968937470808032006255553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22625249961077376008340737 16968937470808032006255553)
          ·
            refine ⟨12726703103106024004691665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16968937470808032006255553 12726703103106024004691665)
            ·
              refine ⟨9545027327329518003518749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12726703103106024004691665 9545027327329518003518749)
              ·
                refine ⟨3579385247748569251319531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9545027327329518003518749 3579385247748569251319531)
                ·
                  refine ⟨5369077871622853876979297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579385247748569251319531 5369077871622853876979297)
                  ·
                    refine ⟨4026808403717140407734473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5369077871622853876979297 4026808403717140407734473)
                    ·
                      refine ⟨3020106302787855305800855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4026808403717140407734473 3020106302787855305800855)
                      ·
                        rfl

theorem cell23_5881636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_5881636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881636 prefixEnd_5881636 := by exact prefixLift 5881636
  have htrace : WordTrace (prefixWord ++ tailWord_5881636) baseStart_5881636 baseEnd_5881636 := by
    simpa [prefixWord, tailWord_5881636, baseEnd_5881636] using wordTrace_append hprefix tailTrace_5881636
  have hstable : (prefixWord ++ tailWord_5881636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881636).length < 2 ^ (prefixWord ++ tailWord_5881636).sum := by decide
  have hdescent : baseEnd_5881636 < baseStart_5881636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881646 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_5881646 : Nat := 118140960795 + 5881646 * 2 ^ 59
def prefixEnd_5881646 : Nat := 4983230072969 + 3 ^ 40 * 5881646 * 2
def baseEnd_5881646 : Nat := 1006703812531466755558603

theorem tailTrace_5881646 : CollatzResearch.WordTrace tailWord_5881646 prefixEnd_5881646 1006703812531466755558603 := by
  unfold tailWord_5881646
  simp only [CollatzResearch.WordTrace]
  refine ⟨26815156656226065251146099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143014168833205681339445861 26815156656226065251146099)
  ·
    refine ⟨40222734984339097876719149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26815156656226065251146099 40222734984339097876719149)
    ·
      refine ⟨15083525619127161703769681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40222734984339097876719149 15083525619127161703769681)
      ·
        refine ⟨11312644214345371277827261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15083525619127161703769681 11312644214345371277827261)
        ·
          refine ⟨4242241580379514229185223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11312644214345371277827261 4242241580379514229185223)
          ·
            refine ⟨6363362370569271343777835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242241580379514229185223 6363362370569271343777835)
            ·
              refine ⟨9545043555853907015666753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6363362370569271343777835 9545043555853907015666753)
              ·
                refine ⟨7158782666890430261750065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9545043555853907015666753 7158782666890430261750065)
                ·
                  refine ⟨5369087000167822696312549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7158782666890430261750065 5369087000167822696312549)
                  ·
                    refine ⟨1006703812531466755558603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369087000167822696312549 1006703812531466755558603)
                    ·
                      rfl

theorem cell23_5881646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_5881646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881646 prefixEnd_5881646 := by exact prefixLift 5881646
  have htrace : WordTrace (prefixWord ++ tailWord_5881646) baseStart_5881646 baseEnd_5881646 := by
    simpa [prefixWord, tailWord_5881646, baseEnd_5881646] using wordTrace_append hprefix tailTrace_5881646
  have hstable : (prefixWord ++ tailWord_5881646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881646).length < 2 ^ (prefixWord ++ tailWord_5881646).sum := by decide
  have hdescent : baseEnd_5881646 < baseStart_5881646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881728 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 4, 5]
def baseStart_5881728 : Nat := 118140960795 + 5881728 * 2 ^ 59
def prefixEnd_5881728 : Nat := 4983230072969 + 3 ^ 40 * 5881728 * 2
def baseEnd_5881728 : Nat := 1006717847669356315283477

theorem tailTrace_5881728 : CollatzResearch.WordTrace tailWord_5881728 prefixEnd_5881728 1006717847669356315283477 := by
  unfold tailWord_5881728
  simp only [CollatzResearch.WordTrace]
  refine ⟨107262122017755725006826919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143016162690340966675769225 107262122017755725006826919)
  ·
    refine ⟨160893183026633587510240379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107262122017755725006826919 160893183026633587510240379)
    ·
      refine ⟨241339774539950381265360569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160893183026633587510240379 241339774539950381265360569)
      ·
        refine ⟨181004830904962785949020427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241339774539950381265360569 181004830904962785949020427)
        ·
          refine ⟨271507246357444178923530641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181004830904962785949020427 271507246357444178923530641)
          ·
            refine ⟨203630434768083134192647981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271507246357444178923530641 203630434768083134192647981)
            ·
              refine ⟨76361413038031175322242993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203630434768083134192647981 76361413038031175322242993)
              ·
                refine ⟨57271059778523381491682245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76361413038031175322242993 57271059778523381491682245)
                ·
                  refine ⟨10738323708473134029690421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57271059778523381491682245 10738323708473134029690421)
                  ·
                    refine ⟨1006717847669356315283477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10738323708473134029690421 1006717847669356315283477)
                    ·
                      rfl

theorem cell23_5881728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_5881728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881728 prefixEnd_5881728 := by exact prefixLift 5881728
  have htrace : WordTrace (prefixWord ++ tailWord_5881728) baseStart_5881728 baseEnd_5881728 := by
    simpa [prefixWord, tailWord_5881728, baseEnd_5881728] using wordTrace_append hprefix tailTrace_5881728
  have hstable : (prefixWord ++ tailWord_5881728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881728).length < 2 ^ (prefixWord ++ tailWord_5881728).sum := by decide
  have hdescent : baseEnd_5881728 < baseStart_5881728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881765 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 3, 6, 2]
def baseStart_5881765 : Nat := 118140960795 + 5881765 * 2 ^ 59
def prefixEnd_5881765 : Nat := 4983230072969 + 3 ^ 40 * 5881765 * 2
def baseEnd_5881765 : Nat := 3020172541792285301087761

theorem tailTrace_5881765 : CollatzResearch.WordTrace tailWord_5881765 prefixEnd_5881765 3020172541792285301087761 := by
  unfold tailWord_5881765
  simp only [CollatzResearch.WordTrace]
  refine ⟨214525593536377405332750749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143017062357584936888500499 214525593536377405332750749)
  ·
    refine ⟨80447097576141526999781531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214525593536377405332750749 80447097576141526999781531)
    ·
      refine ⟨120670646364212290499672297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80447097576141526999781531 120670646364212290499672297)
      ·
        refine ⟨90502984773159217874754223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120670646364212290499672297 90502984773159217874754223)
        ·
          refine ⟨135754477159738826812131335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90502984773159217874754223 135754477159738826812131335)
          ·
            refine ⟨203631715739608240218197003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135754477159738826812131335 203631715739608240218197003)
            ·
              refine ⟨305447573609412360327295505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203631715739608240218197003 305447573609412360327295505)
              ·
                refine ⟨229085680207059270245471629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305447573609412360327295505 229085680207059270245471629)
                ·
                  refine ⟨85907130077647226342051861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229085680207059270245471629 85907130077647226342051861)
                  ·
                    refine ⟨4026896722389713734783681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85907130077647226342051861 4026896722389713734783681)
                    ·
                      refine ⟨3020172541792285301087761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4026896722389713734783681 3020172541792285301087761)
                      ·
                        rfl

theorem cell23_5881765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_5881765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881765 prefixEnd_5881765 := by exact prefixLift 5881765
  have htrace : WordTrace (prefixWord ++ tailWord_5881765) baseStart_5881765 baseEnd_5881765 := by
    simpa [prefixWord, tailWord_5881765, baseEnd_5881765] using wordTrace_append hprefix tailTrace_5881765
  have hstable : (prefixWord ++ tailWord_5881765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881765).length < 2 ^ (prefixWord ++ tailWord_5881765).sum := by decide
  have hdescent : baseEnd_5881765 < baseStart_5881765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881775 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 3, 4]
def baseStart_5881775 : Nat := 118140960795 + 5881775 * 2 ^ 59
def prefixEnd_5881775 : Nat := 4983230072969 + 3 ^ 40 * 5881775 * 2
def baseEnd_5881775 : Nat := 1006725892199610087320905

theorem tailTrace_5881775 : CollatzResearch.WordTrace tailWord_5881775 prefixEnd_5881775 1006725892199610087320905 := by
  unfold tailWord_5881775
  simp only [CollatzResearch.WordTrace]
  refine ⟨214525958266341177040614779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143017305510894118027076519 214525958266341177040614779)
  ·
    refine ⟨321788937399511765560922169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214525958266341177040614779 321788937399511765560922169)
    ·
      refine ⟨241341703049633824170691627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321788937399511765560922169 241341703049633824170691627)
      ·
        refine ⟨362012554574450736256037441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241341703049633824170691627 362012554574450736256037441)
        ·
          refine ⟨271509415930838052192028081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362012554574450736256037441 271509415930838052192028081)
          ·
            refine ⟨203632061948128539144021061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271509415930838052192028081 203632061948128539144021061)
            ·
              refine ⟨38181011615274101089503949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203632061948128539144021061 38181011615274101089503949)
              ·
                refine ⟨14317879355727787908563981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38181011615274101089503949 14317879355727787908563981)
                ·
                  refine ⟨5369204758397920465711493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14317879355727787908563981 5369204758397920465711493)
                  ·
                    refine ⟨1006725892199610087320905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369204758397920465711493 1006725892199610087320905)
                    ·
                      rfl

theorem cell23_5881775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 4].length) (baseStart_5881775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881775 prefixEnd_5881775 := by exact prefixLift 5881775
  have htrace : WordTrace (prefixWord ++ tailWord_5881775) baseStart_5881775 baseEnd_5881775 := by
    simpa [prefixWord, tailWord_5881775, baseEnd_5881775] using wordTrace_append hprefix tailTrace_5881775
  have hstable : (prefixWord ++ tailWord_5881775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881775).length < 2 ^ (prefixWord ++ tailWord_5881775).sum := by decide
  have hdescent : baseEnd_5881775 < baseStart_5881775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881785 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 3]
def baseStart_5881785 : Nat := 118140960795 + 5881785 * 2 ^ 59
def prefixEnd_5881785 : Nat := 4983230072969 + 3 ^ 40 * 5881785 * 2
def baseEnd_5881785 : Nat := 3020182811405375222837669

theorem tailTrace_5881785 : CollatzResearch.WordTrace tailWord_5881785 prefixEnd_5881785 3020182811405375222837669 := by
  unfold tailWord_5881785
  simp only [CollatzResearch.WordTrace]
  refine ⟨214526322996304948748478809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143017548664203299165652539 214526322996304948748478809)
  ·
    refine ⟨160894742247228711561359107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214526322996304948748478809 160894742247228711561359107)
    ·
      refine ⟨241342113370843067342038661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160894742247228711561359107 241342113370843067342038661)
      ·
        refine ⟨45251646257033075126632249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241342113370843067342038661 45251646257033075126632249)
        ·
          refine ⟨33938734692774806344974187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45251646257033075126632249 33938734692774806344974187)
          ·
            refine ⟨50908102039162209517461281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33938734692774806344974187 50908102039162209517461281)
            ·
              refine ⟨38181076529371657138095961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50908102039162209517461281 38181076529371657138095961)
              ·
                refine ⟨28635807397028742853571971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38181076529371657138095961 28635807397028742853571971)
                ·
                  refine ⟨42953711095543114280357957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28635807397028742853571971 42953711095543114280357957)
                  ·
                    refine ⟨8053820830414333927567117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42953711095543114280357957 8053820830414333927567117)
                    ·
                      refine ⟨3020182811405375222837669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8053820830414333927567117 3020182811405375222837669)
                      ·
                        rfl

theorem cell23_5881785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_5881785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881785 prefixEnd_5881785 := by exact prefixLift 5881785
  have htrace : WordTrace (prefixWord ++ tailWord_5881785) baseStart_5881785 baseEnd_5881785 := by
    simpa [prefixWord, tailWord_5881785, baseEnd_5881785] using wordTrace_append hprefix tailTrace_5881785
  have hstable : (prefixWord ++ tailWord_5881785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881785).length < 2 ^ (prefixWord ++ tailWord_5881785).sum := by decide
  have hdescent : baseEnd_5881785 < baseStart_5881785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881802 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_5881802 : Nat := 118140960795 + 5881802 * 2 ^ 59
def prefixEnd_5881802 : Nat := 4983230072969 + 3 ^ 40 * 5881802 * 2
def baseEnd_5881802 : Nat := 3020191540576501656325091

theorem tailTrace_5881802 : CollatzResearch.WordTrace tailWord_5881802 prefixEnd_5881802 3020191540576501656325091 := by
  unfold tailWord_5881802
  simp only [CollatzResearch.WordTrace]
  refine ⟨53631735759310840162961915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143017962024828907101231773 53631735759310840162961915)
  ·
    refine ⟨80447603638966260244442873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53631735759310840162961915 80447603638966260244442873)
    ·
      refine ⟨60335702729224695183332155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80447603638966260244442873 60335702729224695183332155)
      ·
        refine ⟨90503554093837042774998233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60335702729224695183332155 90503554093837042774998233)
        ·
          refine ⟨67877665570377782081248675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90503554093837042774998233 67877665570377782081248675)
          ·
            refine ⟨101816498355566673121873013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67877665570377782081248675 101816498355566673121873013)
            ·
              refine ⟨9545296720834375605175595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101816498355566673121873013 9545296720834375605175595)
              ·
                refine ⟨14317945081251563407763393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9545296720834375605175595 14317945081251563407763393)
                ·
                  refine ⟨10738458810938672555822545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14317945081251563407763393 10738458810938672555822545)
                  ·
                    refine ⟨8053844108204004416866909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10738458810938672555822545 8053844108204004416866909)
                    ·
                      refine ⟨3020191540576501656325091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8053844108204004416866909 3020191540576501656325091)
                      ·
                        rfl

theorem cell23_5881802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_5881802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881802 prefixEnd_5881802 := by exact prefixLift 5881802
  have htrace : WordTrace (prefixWord ++ tailWord_5881802) baseStart_5881802 baseEnd_5881802 := by
    simpa [prefixWord, tailWord_5881802, baseEnd_5881802] using wordTrace_append hprefix tailTrace_5881802
  have hstable : (prefixWord ++ tailWord_5881802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881802).length < 2 ^ (prefixWord ++ tailWord_5881802).sum := by decide
  have hdescent : baseEnd_5881802 < baseStart_5881802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881826 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_5881826 : Nat := 118140960795 + 5881826 * 2 ^ 59
def prefixEnd_5881826 : Nat := 4983230072969 + 3 ^ 40 * 5881826 * 2
def baseEnd_5881826 : Nat := 1006734621370736520808327

theorem tailTrace_5881826 : CollatzResearch.WordTrace tailWord_5881826 prefixEnd_5881826 1006734621370736520808327 := by
  unfold tailWord_5881826
  simp only [CollatzResearch.WordTrace]
  refine ⟨53631954597289103187680333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143018545592770941833814221 53631954597289103187680333)
  ·
    refine ⟨20111982973983413695380125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53631954597289103187680333 20111982973983413695380125)
    ·
      refine ⟨7541993615243780135767547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20111982973983413695380125 7541993615243780135767547)
      ·
        refine ⟨11312990422865670203651321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7541993615243780135767547 11312990422865670203651321)
        ·
          refine ⟨8484742817149252652738491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11312990422865670203651321 8484742817149252652738491)
          ·
            refine ⟨12727114225723878979107737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8484742817149252652738491 12727114225723878979107737)
            ·
              refine ⟨9545335669292909234330803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12727114225723878979107737 9545335669292909234330803)
              ·
                refine ⟨14318003503939363851496205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9545335669292909234330803 14318003503939363851496205)
                ·
                  refine ⟨5369251313977261444311077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14318003503939363851496205 5369251313977261444311077)
                  ·
                    refine ⟨1006734621370736520808327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369251313977261444311077 1006734621370736520808327)
                    ·
                      rfl

theorem cell23_5881826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_5881826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881826 prefixEnd_5881826 := by exact prefixLift 5881826
  have htrace : WordTrace (prefixWord ++ tailWord_5881826) baseStart_5881826 baseEnd_5881826 := by
    simpa [prefixWord, tailWord_5881826, baseEnd_5881826] using wordTrace_append hprefix tailTrace_5881826
  have hstable : (prefixWord ++ tailWord_5881826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881826).length < 2 ^ (prefixWord ++ tailWord_5881826).sum := by decide
  have hdescent : baseEnd_5881826 < baseStart_5881826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881852 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_5881852 : Nat := 118140960795 + 5881852 * 2 ^ 59
def prefixEnd_5881852 : Nat := 4983230072969 + 3 ^ 40 * 5881852 * 2
def baseEnd_5881852 : Nat := 1006739071536408820233287

theorem tailTrace_5881852 : CollatzResearch.WordTrace tailWord_5881852 prefixEnd_5881852 1006739071536408820233287 := by
  unfold tailWord_5881852
  simp only [CollatzResearch.WordTrace]
  refine ⟨107264383343531109595583905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143019177791374812794111873 107264383343531109595583905)
  ·
    refine ⟨80448287507648332196687929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107264383343531109595583905 80448287507648332196687929)
    ·
      refine ⟨60336215630736249147515947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80448287507648332196687929 60336215630736249147515947)
      ·
        refine ⟨90504323446104373721273921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60336215630736249147515947 90504323446104373721273921)
        ·
          refine ⟨67878242584578280290955441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90504323446104373721273921 67878242584578280290955441)
          ·
            refine ⟨50908681938433710218216581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67878242584578280290955441 50908681938433710218216581)
            ·
              refine ⟨9545377863456320665915609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50908681938433710218216581 9545377863456320665915609)
              ·
                refine ⟨7159033397592240499436707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9545377863456320665915609 7159033397592240499436707)
                ·
                  refine ⟨10738550096388360749155061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7159033397592240499436707 10738550096388360749155061)
                  ·
                    refine ⟨1006739071536408820233287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10738550096388360749155061 1006739071536408820233287)
                    ·
                      rfl

theorem cell23_5881852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_5881852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881852 prefixEnd_5881852 := by exact prefixLift 5881852
  have htrace : WordTrace (prefixWord ++ tailWord_5881852) baseStart_5881852 baseEnd_5881852 := by
    simpa [prefixWord, tailWord_5881852, baseEnd_5881852] using wordTrace_append hprefix tailTrace_5881852
  have hstable : (prefixWord ++ tailWord_5881852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881852).length < 2 ^ (prefixWord ++ tailWord_5881852).sum := by decide
  have hdescent : baseEnd_5881852 < baseStart_5881852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881855 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_5881855 : Nat := 118140960795 + 5881855 * 2 ^ 59
def prefixEnd_5881855 : Nat := 4983230072969 + 3 ^ 40 * 5881855 * 2
def baseEnd_5881855 : Nat := 3020218755051189948962347

theorem tailTrace_5881855 : CollatzResearch.WordTrace tailWord_5881855 prefixEnd_5881855 3020218755051189948962347 := by
  unfold tailWord_5881855
  simp only [CollatzResearch.WordTrace]
  refine ⟨214528876106051350703527019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143019250737367567135684679 214528876106051350703527019)
  ·
    refine ⟨321793314159077026055290529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214528876106051350703527019 321793314159077026055290529)
    ·
      refine ⟨241344985619307769541467897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321793314159077026055290529 241344985619307769541467897)
      ·
        refine ⟨181008739214480827156100923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241344985619307769541467897 181008739214480827156100923)
        ·
          refine ⟨271513108821721240734151385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181008739214480827156100923 271513108821721240734151385)
          ·
            refine ⟨203634831616290930550613539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271513108821721240734151385 203634831616290930550613539)
            ·
              refine ⟨305452247424436395825920309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203634831616290930550613539 305452247424436395825920309)
              ·
                refine ⟨28636148196040912108680029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 305452247424436395825920309 28636148196040912108680029)
                ·
                  refine ⟨10738555573515342040755011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28636148196040912108680029 10738555573515342040755011)
                  ·
                    refine ⟨16107833360273013061132517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10738555573515342040755011 16107833360273013061132517)
                    ·
                      refine ⟨3020218755051189948962347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16107833360273013061132517 3020218755051189948962347)
                      ·
                        rfl

theorem cell23_5881855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_5881855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881855 prefixEnd_5881855 := by exact prefixLift 5881855
  have htrace : WordTrace (prefixWord ++ tailWord_5881855) baseStart_5881855 baseEnd_5881855 := by
    simpa [prefixWord, tailWord_5881855, baseEnd_5881855] using wordTrace_append hprefix tailTrace_5881855
  have hstable : (prefixWord ++ tailWord_5881855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881855).length < 2 ^ (prefixWord ++ tailWord_5881855).sum := by decide
  have hdescent : baseEnd_5881855 < baseStart_5881855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881860 : List Nat := [2, 3, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_5881860 : Nat := 118140960795 + 5881860 * 2 ^ 59
def prefixEnd_5881860 : Nat := 4983230072969 + 3 ^ 40 * 5881860 * 2
def baseEnd_5881860 : Nat := 1006740440818154143133275

theorem tailTrace_5881860 : CollatzResearch.WordTrace tailWord_5881860 prefixEnd_5881860 1006740440818154143133275 := by
  unfold tailWord_5881860
  simp only [CollatzResearch.WordTrace]
  refine ⟨107264529235516618278729517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143019372314022157704972689 107264529235516618278729517)
  ·
    refine ⟨40224198463318731854523569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107264529235516618278729517 40224198463318731854523569)
    ·
      refine ⟨30168148847489048890892677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40224198463318731854523569 30168148847489048890892677)
      ·
        refine ⟨5656527908904196667042377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30168148847489048890892677 5656527908904196667042377)
        ·
          refine ⟨4242395931678147500281783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656527908904196667042377 4242395931678147500281783)
          ·
            refine ⟨6363593897517221250422675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242395931678147500281783 6363593897517221250422675)
            ·
              refine ⟨9545390846275831875634013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6363593897517221250422675 9545390846275831875634013)
              ·
                refine ⟨3579521567353436953362755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9545390846275831875634013 3579521567353436953362755)
                ·
                  refine ⟨5369282351030155430044133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579521567353436953362755 5369282351030155430044133)
                  ·
                    refine ⟨1006740440818154143133275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369282351030155430044133 1006740440818154143133275)
                    ·
                      rfl

theorem cell23_5881860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_5881860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881860 prefixEnd_5881860 := by exact prefixLift 5881860
  have htrace : WordTrace (prefixWord ++ tailWord_5881860) baseStart_5881860 baseEnd_5881860 := by
    simpa [prefixWord, tailWord_5881860, baseEnd_5881860] using wordTrace_append hprefix tailTrace_5881860
  have hstable : (prefixWord ++ tailWord_5881860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881860).length < 2 ^ (prefixWord ++ tailWord_5881860).sum := by decide
  have hdescent : baseEnd_5881860 < baseStart_5881860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881875 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 5]
def baseStart_5881875 : Nat := 118140960795 + 5881875 * 2 ^ 59
def prefixEnd_5881875 : Nat := 4983230072969 + 3 ^ 40 * 5881875 * 2
def baseEnd_5881875 : Nat := 3020229024664279870712255

theorem tailTrace_5881875 : CollatzResearch.WordTrace tailWord_5881875 prefixEnd_5881875 3020229024664279870712255 := by
  unfold tailWord_5881875
  simp only [CollatzResearch.WordTrace]
  refine ⟨214529605565978894119255079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143019737043985929412836719 214529605565978894119255079)
  ·
    refine ⟨321794408348968341178882619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214529605565978894119255079 321794408348968341178882619)
    ·
      refine ⟨482691612523452511768323929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321794408348968341178882619 482691612523452511768323929)
      ·
        refine ⟨362018709392589383826242947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482691612523452511768323929 362018709392589383826242947)
        ·
          refine ⟨543028064088884075739364421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362018709392589383826242947 543028064088884075739364421)
          ·
            refine ⟨101817762016665764201130829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 543028064088884075739364421 101817762016665764201130829)
            ·
              refine ⟨38181660756249661575424061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101817762016665764201130829 38181660756249661575424061)
              ·
                refine ⟨14318122783593623090784023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38181660756249661575424061 14318122783593623090784023)
                ·
                  refine ⟨21477184175390434636176035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14318122783593623090784023 21477184175390434636176035)
                  ·
                    refine ⟨32215776263085651954264053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21477184175390434636176035 32215776263085651954264053)
                    ·
                      refine ⟨3020229024664279870712255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32215776263085651954264053 3020229024664279870712255)
                      ·
                        rfl

theorem cell23_5881875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_5881875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881875 prefixEnd_5881875 := by exact prefixLift 5881875
  have htrace : WordTrace (prefixWord ++ tailWord_5881875) baseStart_5881875 baseEnd_5881875 := by
    simpa [prefixWord, tailWord_5881875, baseEnd_5881875] using wordTrace_append hprefix tailTrace_5881875
  have hstable : (prefixWord ++ tailWord_5881875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881875).length < 2 ^ (prefixWord ++ tailWord_5881875).sum := by decide
  have hdescent : baseEnd_5881875 < baseStart_5881875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881882 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_5881882 : Nat := 118140960795 + 5881882 * 2 ^ 59
def prefixEnd_5881882 : Nat := 4983230072969 + 3 ^ 40 * 5881882 * 2
def baseEnd_5881882 : Nat := 1006744206342953781108241

theorem tailTrace_5881882 : CollatzResearch.WordTrace tailWord_5881882 prefixEnd_5881882 1006744206342953781108241 := by
  unfold tailWord_5881882
  simp only [CollatzResearch.WordTrace]
  refine ⟨53632465219238383578689975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143019907251302356209839933 53632465219238383578689975)
  ·
    refine ⟨80448697828857575368034963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53632465219238383578689975 80448697828857575368034963)
    ·
      refine ⟨120673046743286363052052445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80448697828857575368034963 120673046743286363052052445)
      ·
        refine ⟨45252392528732386144519667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120673046743286363052052445 45252392528732386144519667)
        ·
          refine ⟨67878588793098579216779501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45252392528732386144519667 67878588793098579216779501)
          ·
            refine ⟨25454470797411967206292313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67878588793098579216779501 25454470797411967206292313)
            ·
              refine ⟨19090853098058975404719235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25454470797411967206292313 19090853098058975404719235)
              ·
                refine ⟨28636279647088463107078853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19090853098058975404719235 28636279647088463107078853)
                ·
                  refine ⟨5369302433829086832577285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28636279647088463107078853 5369302433829086832577285)
                  ·
                    refine ⟨1006744206342953781108241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369302433829086832577285 1006744206342953781108241)
                    ·
                      rfl

theorem cell23_5881882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_5881882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881882 prefixEnd_5881882 := by exact prefixLift 5881882
  have htrace : WordTrace (prefixWord ++ tailWord_5881882) baseStart_5881882 baseEnd_5881882 := by
    simpa [prefixWord, tailWord_5881882, baseEnd_5881882] using wordTrace_append hprefix tailTrace_5881882
  have hstable : (prefixWord ++ tailWord_5881882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881882).length < 2 ^ (prefixWord ++ tailWord_5881882).sum := by decide
  have hdescent : baseEnd_5881882 < baseStart_5881882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881902 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_5881902 : Nat := 118140960795 + 5881902 * 2 ^ 59
def prefixEnd_5881902 : Nat := 4983230072969 + 3 ^ 40 * 5881902 * 2
def baseEnd_5881902 : Nat := 3020242888641951265074631

theorem tailTrace_5881902 : CollatzResearch.WordTrace tailWord_5881902 prefixEnd_5881902 3020242888641951265074631 := by
  unfold tailWord_5881902
  simp only [CollatzResearch.WordTrace]
  refine ⟨26816323792110134716310995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143020393557920718486991973 26816323792110134716310995)
  ·
    refine ⟨40224485688165202074466493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26816323792110134716310995 40224485688165202074466493)
    ·
      refine ⟨15084182133061950777924935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40224485688165202074466493 15084182133061950777924935)
      ·
        refine ⟨22626273199592926166887403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15084182133061950777924935 22626273199592926166887403)
        ·
          refine ⟨33939409799389389250331105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22626273199592926166887403 33939409799389389250331105)
          ·
            refine ⟨25454557349542041937748329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33939409799389389250331105 25454557349542041937748329)
            ·
              refine ⟨19090918012156531453311247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25454557349542041937748329 19090918012156531453311247)
              ·
                refine ⟨28636377018234797179966871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19090918012156531453311247 28636377018234797179966871)
                ·
                  refine ⟨42954565527352195769950307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28636377018234797179966871 42954565527352195769950307)
                  ·
                    refine ⟨64431848291028293654925461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42954565527352195769950307 64431848291028293654925461)
                    ·
                      refine ⟨3020242888641951265074631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64431848291028293654925461 3020242888641951265074631)
                      ·
                        rfl

theorem cell23_5881902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_5881902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881902 prefixEnd_5881902 := by exact prefixLift 5881902
  have htrace : WordTrace (prefixWord ++ tailWord_5881902) baseStart_5881902 baseEnd_5881902 := by
    simpa [prefixWord, tailWord_5881902, baseEnd_5881902] using wordTrace_append hprefix tailTrace_5881902
  have hstable : (prefixWord ++ tailWord_5881902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881902).length < 2 ^ (prefixWord ++ tailWord_5881902).sum := by decide
  have hdescent : baseEnd_5881902 < baseStart_5881902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881909 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_5881909 : Nat := 118140960795 + 5881909 * 2 ^ 59
def prefixEnd_5881909 : Nat := 4983230072969 + 3 ^ 40 * 5881909 * 2
def baseEnd_5881909 : Nat := 3020246483006532737687099

theorem tailTrace_5881909 : CollatzResearch.WordTrace tailWord_5881909 prefixEnd_5881909 3020246483006532737687099 := by
  unfold tailWord_5881909
  simp only [CollatzResearch.WordTrace]
  refine ⟨214530845647855717925992781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143020563765237145283995187 214530845647855717925992781)
  ·
    refine ⟨80449067117945894222247293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214530845647855717925992781 80449067117945894222247293)
    ·
      refine ⟨30168400169229710333342735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80449067117945894222247293 30168400169229710333342735)
      ·
        refine ⟨45252600253844565500014103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30168400169229710333342735 45252600253844565500014103)
        ·
          refine ⟨67878900380766848250021155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45252600253844565500014103 67878900380766848250021155)
          ·
            refine ⟨101818350571150272375031733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67878900380766848250021155 101818350571150272375031733)
            ·
              refine ⟨9545470366045338035159225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101818350571150272375031733 9545470366045338035159225)
              ·
                refine ⟨7159102774534003526369419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9545470366045338035159225 7159102774534003526369419)
                ·
                  refine ⟨10738654161801005289554129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7159102774534003526369419 10738654161801005289554129)
                  ·
                    refine ⟨8053990621350753967165597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10738654161801005289554129 8053990621350753967165597)
                    ·
                      refine ⟨3020246483006532737687099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8053990621350753967165597 3020246483006532737687099)
                      ·
                        rfl

theorem cell23_5881909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_5881909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881909 prefixEnd_5881909 := by exact prefixLift 5881909
  have htrace : WordTrace (prefixWord ++ tailWord_5881909) baseStart_5881909 baseEnd_5881909 := by
    simpa [prefixWord, tailWord_5881909, baseEnd_5881909] using wordTrace_append hprefix tailTrace_5881909
  have hstable : (prefixWord ++ tailWord_5881909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881909).length < 2 ^ (prefixWord ++ tailWord_5881909).sum := by decide
  have hdescent : baseEnd_5881909 < baseStart_5881909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881945 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_5881945 : Nat := 118140960795 + 5881945 * 2 ^ 59
def prefixEnd_5881945 : Nat := 4983230072969 + 3 ^ 40 * 5881945 * 2
def baseEnd_5881945 : Nat := 3020264968310094596836933

theorem tailTrace_5881945 : CollatzResearch.WordTrace tailWord_5881945 prefixEnd_5881945 3020264968310094596836933 := by
  unfold tailWord_5881945
  simp only [CollatzResearch.WordTrace]
  refine ⟨214532158675725296074303289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143021439117150197382868859 214532158675725296074303289)
  ·
    refine ⟨160899119006793972055727467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214532158675725296074303289 160899119006793972055727467)
    ·
      refine ⟨241348678510190958083591201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160899119006793972055727467 241348678510190958083591201)
      ·
        refine ⟨181011508882643218562693401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241348678510190958083591201 181011508882643218562693401)
        ·
          refine ⟨135758631661982413922020051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181011508882643218562693401 135758631661982413922020051)
          ·
            refine ⟨203637947492973620883030077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135758631661982413922020051 203637947492973620883030077)
            ·
              refine ⟨76364230309865107831136279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203637947492973620883030077 76364230309865107831136279)
              ·
                refine ⟨114546345464797661746704419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76364230309865107831136279 114546345464797661746704419)
                ·
                  refine ⟨171819518197196492620056629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114546345464797661746704419 171819518197196492620056629)
                  ·
                    refine ⟨16108079830987171183130309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 171819518197196492620056629 16108079830987171183130309)
                    ·
                      refine ⟨3020264968310094596836933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16108079830987171183130309 3020264968310094596836933)
                      ·
                        rfl

theorem cell23_5881945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_5881945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881945 prefixEnd_5881945 := by exact prefixLift 5881945
  have htrace : WordTrace (prefixWord ++ tailWord_5881945) baseStart_5881945 baseEnd_5881945 := by
    simpa [prefixWord, tailWord_5881945, baseEnd_5881945] using wordTrace_append hprefix tailTrace_5881945
  have hstable : (prefixWord ++ tailWord_5881945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881945).length < 2 ^ (prefixWord ++ tailWord_5881945).sum := by decide
  have hdescent : baseEnd_5881945 < baseStart_5881945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881955 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 1, 8]
def baseStart_5881955 : Nat := 118140960795 + 5881955 * 2 ^ 59
def prefixEnd_5881955 : Nat := 4983230072969 + 3 ^ 40 * 5881955 * 2
def baseEnd_5881955 : Nat := 1006756701038879852570629

theorem tailTrace_5881955 : CollatzResearch.WordTrace tailWord_5881955 prefixEnd_5881955 1006756701038879852570629 := by
  unfold tailWord_5881955
  simp only [CollatzResearch.WordTrace]
  refine ⟨214532523405689067782167319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143021682270459378521444879 214532523405689067782167319)
  ·
    refine ⟨321798785108533601673250979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214532523405689067782167319 321798785108533601673250979)
    ·
      refine ⟨482698177662800402509876469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321798785108533601673250979 482698177662800402509876469)
      ·
        refine ⟨45252954155887537735300919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 482698177662800402509876469 45252954155887537735300919)
        ·
          refine ⟨67879431233831306602951379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45252954155887537735300919 67879431233831306602951379)
          ·
            refine ⟨101819146850746959904427069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67879431233831306602951379 101819146850746959904427069)
            ·
              refine ⟨38182180069030109964160151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101819146850746959904427069 38182180069030109964160151)
              ·
                refine ⟨57273270103545164946240227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38182180069030109964160151 57273270103545164946240227)
                ·
                  refine ⟨85909905155317747419360341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57273270103545164946240227 85909905155317747419360341)
                  ·
                    refine ⟨1006756701038879852570629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85909905155317747419360341 1006756701038879852570629)
                    ·
                      rfl

theorem cell23_5881955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 8].length) (baseStart_5881955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881955 prefixEnd_5881955 := by exact prefixLift 5881955
  have htrace : WordTrace (prefixWord ++ tailWord_5881955) baseStart_5881955 baseEnd_5881955 := by
    simpa [prefixWord, tailWord_5881955, baseEnd_5881955] using wordTrace_append hprefix tailTrace_5881955
  have hstable : (prefixWord ++ tailWord_5881955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881955).length < 2 ^ (prefixWord ++ tailWord_5881955).sum := by decide
  have hdescent : baseEnd_5881955 < baseStart_5881955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5881966 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_5881966 : Nat := 118140960795 + 5881966 * 2 ^ 59
def prefixEnd_5881966 : Nat := 4983230072969 + 3 ^ 40 * 5881966 * 2
def baseEnd_5881966 : Nat := 3020275751403839014674337

theorem tailTrace_5881966 : CollatzResearch.WordTrace tailWord_5881966 prefixEnd_5881966 3020275751403839014674337 := by
  unfold tailWord_5881966
  simp only [CollatzResearch.WordTrace]
  refine ⟨26816615576081152082602219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143021949739099477773878501 26816615576081152082602219)
  ·
    refine ⟨40224923364121728123903329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26816615576081152082602219 40224923364121728123903329)
    ·
      refine ⟨30168692523091296092927497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40224923364121728123903329 30168692523091296092927497)
      ·
        refine ⟨22626519392318472069695623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30168692523091296092927497 22626519392318472069695623)
        ·
          refine ⟨33939779088477708104543435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22626519392318472069695623 33939779088477708104543435)
          ·
            refine ⟨50909668632716562156815153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33939779088477708104543435 50909668632716562156815153)
            ·
              refine ⟨38182251474537421617611365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50909668632716562156815153 38182251474537421617611365)
              ·
                refine ⟨7159172151475766553302131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38182251474537421617611365 7159172151475766553302131)
                ·
                  refine ⟨10738758227213649829953197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7159172151475766553302131 10738758227213649829953197)
                  ·
                    refine ⟨4027034335205118686232449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10738758227213649829953197 4027034335205118686232449)
                    ·
                      refine ⟨3020275751403839014674337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027034335205118686232449 3020275751403839014674337)
                      ·
                        rfl

theorem cell23_5881966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_5881966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5881966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5881966 prefixEnd_5881966 := by exact prefixLift 5881966
  have htrace : WordTrace (prefixWord ++ tailWord_5881966) baseStart_5881966 baseEnd_5881966 := by
    simpa [prefixWord, tailWord_5881966, baseEnd_5881966] using wordTrace_append hprefix tailTrace_5881966
  have hstable : (prefixWord ++ tailWord_5881966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5881966).length < 2 ^ (prefixWord ++ tailWord_5881966).sum := by decide
  have hdescent : baseEnd_5881966 < baseStart_5881966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5881966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882136 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 3, 1, 3]
def baseStart_5882136 : Nat := 118140960795 + 5882136 * 2 ^ 59
def prefixEnd_5882136 : Nat := 4983230072969 + 3 ^ 40 * 5882136 * 2
def baseEnd_5882136 : Nat := 3020363043115103349548555

theorem tailTrace_5882136 : CollatzResearch.WordTrace tailWord_5882136 prefixEnd_5882136 3020363043115103349548555 := by
  unfold tailWord_5882136
  simp only [CollatzResearch.WordTrace]
  refine ⟨107269562509016667847253131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143026083345355557129670841 107269562509016667847253131)
  ·
    refine ⟨160904343763525001770879697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107269562509016667847253131 160904343763525001770879697)
    ·
      refine ⟨120678257822643751328159773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160904343763525001770879697 120678257822643751328159773)
      ·
        refine ⟨45254346683491406748059915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120678257822643751328159773 45254346683491406748059915)
        ·
          refine ⟨67881520025237110122089873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45254346683491406748059915 67881520025237110122089873)
          ·
            refine ⟨50911140018927832591567405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67881520025237110122089873 50911140018927832591567405)
            ·
              refine ⟨19091677507097937221837777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50911140018927832591567405 19091677507097937221837777)
              ·
                refine ⟨14318758130323452916378333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19091677507097937221837777 14318758130323452916378333)
                ·
                  refine ⟨5369534298871294843641875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14318758130323452916378333 5369534298871294843641875)
                  ·
                    refine ⟨8054301448306942265462813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5369534298871294843641875 8054301448306942265462813)
                    ·
                      refine ⟨3020363043115103349548555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8054301448306942265462813 3020363043115103349548555)
                      ·
                        rfl

theorem cell23_5882136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_5882136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882136 prefixEnd_5882136 := by exact prefixLift 5882136
  have htrace : WordTrace (prefixWord ++ tailWord_5882136) baseStart_5882136 baseEnd_5882136 := by
    simpa [prefixWord, tailWord_5882136, baseEnd_5882136] using wordTrace_append hprefix tailTrace_5882136
  have hstable : (prefixWord ++ tailWord_5882136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882136).length < 2 ^ (prefixWord ++ tailWord_5882136).sum := by decide
  have hdescent : baseEnd_5882136 < baseStart_5882136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882156 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_5882156 : Nat := 118140960795 + 5882156 * 2 ^ 59
def prefixEnd_5882156 : Nat := 4983230072969 + 3 ^ 40 * 5882156 * 2
def baseEnd_5882156 : Nat := 1006791104242731090432821

theorem tailTrace_5882156 : CollatzResearch.WordTrace tailWord_5882156 prefixEnd_5882156 1006791104242731090432821 := by
  unfold tailWord_5882156
  simp only [CollatzResearch.WordTrace]
  refine ⟨107269927238980439555117161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143026569651973919406822881 107269927238980439555117161)
  ·
    refine ⟨80452445429235329666337871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107269927238980439555117161 80452445429235329666337871)
    ·
      refine ⟨120678668143852994499506807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80452445429235329666337871 120678668143852994499506807)
      ·
        refine ⟨181018002215779491749260211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120678668143852994499506807 181018002215779491749260211)
        ·
          refine ⟨271527003323669237623890317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181018002215779491749260211 271527003323669237623890317)
          ·
            refine ⟨101822626246375964108958869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271527003323669237623890317 101822626246375964108958869)
            ·
              refine ⟨4772935605298873317607447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101822626246375964108958869 4772935605298873317607447)
              ·
                refine ⟨7159403407948309976411171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772935605298873317607447 7159403407948309976411171)
                ·
                  refine ⟨10739105111922464964616757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7159403407948309976411171 10739105111922464964616757)
                  ·
                    refine ⟨1006791104242731090432821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10739105111922464964616757 1006791104242731090432821)
                    ·
                      rfl

theorem cell23_5882156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_5882156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882156 prefixEnd_5882156 := by exact prefixLift 5882156
  have htrace : WordTrace (prefixWord ++ tailWord_5882156) baseStart_5882156 baseEnd_5882156 := by
    simpa [prefixWord, tailWord_5882156, baseEnd_5882156] using wordTrace_append hprefix tailTrace_5882156
  have hstable : (prefixWord ++ tailWord_5882156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882156).length < 2 ^ (prefixWord ++ tailWord_5882156).sum := by decide
  have hdescent : baseEnd_5882156 < baseStart_5882156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882179 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 3]
def baseStart_5882179 : Nat := 118140960795 + 5882179 * 2 ^ 59
def prefixEnd_5882179 : Nat := 4983230072969 + 3 ^ 40 * 5882179 * 2
def baseEnd_5882179 : Nat := 3020385122783246681310857

theorem tailTrace_5882179 : CollatzResearch.WordTrace tailWord_5882179 prefixEnd_5882179 3020385122783246681310857 := by
  unfold tailWord_5882179
  simp only [CollatzResearch.WordTrace]
  refine ⟨214540693356877554038321591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143027128904585036025547727 214540693356877554038321591)
  ·
    refine ⟨321811040035316331057482387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214540693356877554038321591 321811040035316331057482387)
    ·
      refine ⟨482716560052974496586223581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321811040035316331057482387 482716560052974496586223581)
      ·
        refine ⟨181018710019865436219833843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 482716560052974496586223581 181018710019865436219833843)
        ·
          refine ⟨271528065029798154329750765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181018710019865436219833843 271528065029798154329750765)
          ·
            refine ⟨101823024386174307873656537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271528065029798154329750765 101823024386174307873656537)
            ·
              refine ⟨76367268289630730905242403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101823024386174307873656537 76367268289630730905242403)
              ·
                refine ⟨114550902434446096357863605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76367268289630730905242403 114550902434446096357863605)
                ·
                  refine ⟨10739147103229321533549713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114550902434446096357863605 10739147103229321533549713)
                  ·
                    refine ⟨8054360327421991150162285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10739147103229321533549713 8054360327421991150162285)
                    ·
                      refine ⟨3020385122783246681310857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8054360327421991150162285 3020385122783246681310857)
                      ·
                        rfl

theorem cell23_5882179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_5882179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882179 prefixEnd_5882179 := by exact prefixLift 5882179
  have htrace : WordTrace (prefixWord ++ tailWord_5882179) baseStart_5882179 baseEnd_5882179 := by
    simpa [prefixWord, tailWord_5882179, baseEnd_5882179] using wordTrace_append hprefix tailTrace_5882179
  have hstable : (prefixWord ++ tailWord_5882179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882179).length < 2 ^ (prefixWord ++ tailWord_5882179).sum := by decide
  have hdescent : baseEnd_5882179 < baseStart_5882179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882193 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 3, 2, 2]
def baseStart_5882193 : Nat := 118140960795 + 5882193 * 2 ^ 59
def prefixEnd_5882193 : Nat := 4983230072969 + 3 ^ 40 * 5882193 * 2
def baseEnd_5882193 : Nat := 3020392311512409626535793

theorem tailTrace_5882193 : CollatzResearch.WordTrace tailWord_5882193 prefixEnd_5882193 3020392311512409626535793 := by
  unfold tailWord_5882193
  simp only [CollatzResearch.WordTrace]
  refine ⟨214541203978826834429331233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143027469319217889619554155 214541203978826834429331233)
  ·
    refine ⟨160905902984120125821998425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214541203978826834429331233 160905902984120125821998425)
    ·
      refine ⟨120679427238090094366498819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160905902984120125821998425 120679427238090094366498819)
      ·
        refine ⟨181019140857135141549748229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120679427238090094366498819 181019140857135141549748229)
        ·
          refine ⟨33941088910712839040577793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181019140857135141549748229 33941088910712839040577793)
          ·
            refine ⟨25455816683034629280433345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33941088910712839040577793 25455816683034629280433345)
            ·
              refine ⟨19091862512275971960325009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25455816683034629280433345 19091862512275971960325009)
              ·
                refine ⟨14318896884206978970243757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19091862512275971960325009 14318896884206978970243757)
                ·
                  refine ⟨5369586331577617113841409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14318896884206978970243757 5369586331577617113841409)
                  ·
                    refine ⟨4027189748683212835381057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5369586331577617113841409 4027189748683212835381057)
                    ·
                      refine ⟨3020392311512409626535793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027189748683212835381057 3020392311512409626535793)
                      ·
                        rfl

theorem cell23_5882193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_5882193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882193 prefixEnd_5882193 := by exact prefixLift 5882193
  have htrace : WordTrace (prefixWord ++ tailWord_5882193) baseStart_5882193 baseEnd_5882193 := by
    simpa [prefixWord, tailWord_5882193, baseEnd_5882193] using wordTrace_append hprefix tailTrace_5882193
  have hstable : (prefixWord ++ tailWord_5882193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882193).length < 2 ^ (prefixWord ++ tailWord_5882193).sum := by decide
  have hdescent : baseEnd_5882193 < baseStart_5882193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882204 : List Nat := [2, 2, 4, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5882204 : Nat := 118140960795 + 5882204 * 2 ^ 59
def prefixEnd_5882204 : Nat := 4983230072969 + 3 ^ 40 * 5882204 * 2
def baseEnd_5882204 : Nat := 3020397959799609083498243

theorem tailTrace_5882204 : CollatzResearch.WordTrace tailWord_5882204 prefixEnd_5882204 3020397959799609083498243 := by
  unfold tailWord_5882204
  simp only [CollatzResearch.WordTrace]
  refine ⟨107270802590893491653990833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143027736787857988871987777 107270802590893491653990833)
  ·
    refine ⟨80453101943170118740493125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107270802590893491653990833 80453101943170118740493125)
    ·
      refine ⟨15084956614344397263842461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80453101943170118740493125 15084956614344397263842461)
      ·
        refine ⟨5656858730379148973940923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15084956614344397263842461 5656858730379148973940923)
        ·
          refine ⟨8485288095568723460911385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5656858730379148973940923 8485288095568723460911385)
          ·
            refine ⟨6363966071676542595683539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8485288095568723460911385 6363966071676542595683539)
            ·
              refine ⟨9545949107514813893525309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6363966071676542595683539 9545949107514813893525309)
              ·
                refine ⟨3579730915318055210071991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9545949107514813893525309 3579730915318055210071991)
                ·
                  refine ⟨5369596372977082815107987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579730915318055210071991 5369596372977082815107987)
                  ·
                    refine ⟨8054394559465624222661981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5369596372977082815107987 8054394559465624222661981)
                    ·
                      refine ⟨3020397959799609083498243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8054394559465624222661981 3020397959799609083498243)
                      ·
                        rfl

theorem cell23_5882204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5882204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882204 prefixEnd_5882204 := by exact prefixLift 5882204
  have htrace : WordTrace (prefixWord ++ tailWord_5882204) baseStart_5882204 baseEnd_5882204 := by
    simpa [prefixWord, tailWord_5882204, baseEnd_5882204] using wordTrace_append hprefix tailTrace_5882204
  have hstable : (prefixWord ++ tailWord_5882204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882204).length < 2 ^ (prefixWord ++ tailWord_5882204).sum := by decide
  have hdescent : baseEnd_5882204 < baseStart_5882204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882300 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5882300 : Nat := 118140960795 + 5882300 * 2 ^ 59
def prefixEnd_5882300 : Nat := 4983230072969 + 3 ^ 40 * 5882300 * 2
def baseEnd_5882300 : Nat := 3020447253942440707897801

theorem tailTrace_5882300 : CollatzResearch.WordTrace tailWord_5882300 prefixEnd_5882300 3020447253942440707897801 := by
  unfold tailWord_5882300
  simp only [CollatzResearch.WordTrace]
  refine ⟨107272553294719595851738177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143030071059626127802317569 107272553294719595851738177)
  ·
    refine ⟨80454414971039696888803633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107272553294719595851738177 80454414971039696888803633)
    ·
      refine ⟨60340811228279772666602725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80454414971039696888803633 60340811228279772666602725)
      ·
        refine ⟨11313902105302457374988011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60340811228279772666602725 11313902105302457374988011)
        ·
          refine ⟨16970853157953686062482017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11313902105302457374988011 16970853157953686062482017)
          ·
            refine ⟨12728139868465264546861513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16970853157953686062482017 12728139868465264546861513)
            ·
              refine ⟨9546104901348948410146135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12728139868465264546861513 9546104901348948410146135)
              ·
                refine ⟨14319157352023422615219203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9546104901348948410146135 14319157352023422615219203)
                ·
                  refine ⟨21478736028035133922828805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14319157352023422615219203 21478736028035133922828805)
                  ·
                    refine ⟨4027263005256587610530401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21478736028035133922828805 4027263005256587610530401)
                    ·
                      refine ⟨3020447253942440707897801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027263005256587610530401 3020447253942440707897801)
                      ·
                        rfl

theorem cell23_5882300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5882300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882300 prefixEnd_5882300 := by exact prefixLift 5882300
  have htrace : WordTrace (prefixWord ++ tailWord_5882300) baseStart_5882300 baseEnd_5882300 := by
    simpa [prefixWord, tailWord_5882300, baseEnd_5882300] using wordTrace_append hprefix tailTrace_5882300
  have hstable : (prefixWord ++ tailWord_5882300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882300).length < 2 ^ (prefixWord ++ tailWord_5882300).sum := by decide
  have hdescent : baseEnd_5882300 < baseStart_5882300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882359 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_5882359 : Nat := 118140960795 + 5882359 * 2 ^ 59
def prefixEnd_5882359 : Nat := 4983230072969 + 3 ^ 40 * 5882359 * 2
def baseEnd_5882359 : Nat := 3020477549301055977060029

theorem tailTrace_5882359 : CollatzResearch.WordTrace tailWord_5882359 prefixEnd_5882359 3020477549301055977060029 := by
  unfold tailWord_5882359
  simp only [CollatzResearch.WordTrace]
  refine ⟨214547258496225444779874131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143031505664150296519916087 214547258496225444779874131)
  ·
    refine ⟨321820887744338167169811197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214547258496225444779874131 321820887744338167169811197)
    ·
      refine ⟨120682832904126812688679199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321820887744338167169811197 120682832904126812688679199)
      ·
        refine ⟨181024249356190219033018799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120682832904126812688679199 181024249356190219033018799)
        ·
          refine ⟨271536374034285328549528199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181024249356190219033018799 271536374034285328549528199)
          ·
            refine ⟨407304561051427992824292299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271536374034285328549528199 407304561051427992824292299)
            ·
              refine ⟨610956841577141989236438449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407304561051427992824292299 610956841577141989236438449)
              ·
                refine ⟨458217631182856491927328837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610956841577141989236438449 458217631182856491927328837)
                ·
                  refine ⟨85915805846785592236374157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 458217631182856491927328837 85915805846785592236374157)
                  ·
                    refine ⟨32218427192544597088640309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85915805846785592236374157 32218427192544597088640309)
                    ·
                      refine ⟨3020477549301055977060029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32218427192544597088640309 3020477549301055977060029)
                      ·
                        rfl

theorem cell23_5882359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_5882359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882359 prefixEnd_5882359 := by exact prefixLift 5882359
  have htrace : WordTrace (prefixWord ++ tailWord_5882359) baseStart_5882359 baseEnd_5882359 := by
    simpa [prefixWord, tailWord_5882359, baseEnd_5882359] using wordTrace_append hprefix tailTrace_5882359
  have hstable : (prefixWord ++ tailWord_5882359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882359).length < 2 ^ (prefixWord ++ tailWord_5882359).sum := by decide
  have hdescent : baseEnd_5882359 < baseStart_5882359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882374 : List Nat := [6, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5882374 : Nat := 118140960795 + 5882374 * 2 ^ 59
def prefixEnd_5882374 : Nat := 4983230072969 + 3 ^ 40 * 5882374 * 2
def baseEnd_5882374 : Nat := 335609472390097046485829

theorem tailTrace_5882374 : CollatzResearch.WordTrace tailWord_5882374 prefixEnd_5882374 335609472390097046485829 := by
  unfold tailWord_5882374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704618924724096948177193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143031870394114068227780117 6704618924724096948177193)
  ·
    refine ⟨5028464193543072711132895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6704618924724096948177193 5028464193543072711132895)
    ·
      refine ⟨7542696290314609066699343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5028464193543072711132895 7542696290314609066699343)
      ·
        refine ⟨11314044435471913600049015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7542696290314609066699343 11314044435471913600049015)
        ·
          refine ⟨16971066653207870400073523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11314044435471913600049015 16971066653207870400073523)
          ·
            refine ⟨25456599979811805600110285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16971066653207870400073523 25456599979811805600110285)
            ·
              refine ⟨9546224992429427100041357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25456599979811805600110285 9546224992429427100041357)
              ·
                refine ⟨3579834372161035162515509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9546224992429427100041357 3579834372161035162515509)
                ·
                  refine ⟨335609472390097046485829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579834372161035162515509 335609472390097046485829)
                  ·
                    rfl

theorem cell23_5882374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5882374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882374 prefixEnd_5882374 := by exact prefixLift 5882374
  have htrace : WordTrace (prefixWord ++ tailWord_5882374) baseStart_5882374 baseEnd_5882374 := by
    simpa [prefixWord, tailWord_5882374, baseEnd_5882374] using wordTrace_append hprefix tailTrace_5882374
  have hstable : (prefixWord ++ tailWord_5882374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882374).length < 2 ^ (prefixWord ++ tailWord_5882374).sum := by decide
  have hdescent : baseEnd_5882374 < baseStart_5882374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882396 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 8]
def baseStart_5882396 : Nat := 118140960795 + 5882396 * 2 ^ 59
def prefixEnd_5882396 : Nat := 4983230072969 + 3 ^ 40 * 5882396 * 2
def baseEnd_5882396 : Nat := 335610727565030259144151

theorem tailTrace_5882396 : CollatzResearch.WordTrace tailWord_5882396 prefixEnd_5882396 335610727565030259144151 := by
  unfold tailWord_5882396
  simp only [CollatzResearch.WordTrace]
  refine ⟨107274303998545700049485521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143032405331394266732647361 107274303998545700049485521)
  ·
    refine ⟨80455727998909275037114141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107274303998545700049485521 80455727998909275037114141)
    ·
      refine ⟨30170897999590978138917803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80455727998909275037114141 30170897999590978138917803)
      ·
        refine ⟨45256346999386467208376705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30170897999590978138917803 45256346999386467208376705)
        ·
          refine ⟨33942260249539850406282529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45256346999386467208376705 33942260249539850406282529)
          ·
            refine ⟨25456695187154887804711897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33942260249539850406282529 25456695187154887804711897)
            ·
              refine ⟨19092521390366165853533923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25456695187154887804711897 19092521390366165853533923)
              ·
                refine ⟨28638782085549248780300885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19092521390366165853533923 28638782085549248780300885)
                ·
                  refine ⟨335610727565030259144151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28638782085549248780300885 335610727565030259144151)
                  ·
                    rfl

theorem cell23_5882396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_5882396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882396 prefixEnd_5882396 := by exact prefixLift 5882396
  have htrace : WordTrace (prefixWord ++ tailWord_5882396) baseStart_5882396 baseEnd_5882396 := by
    simpa [prefixWord, tailWord_5882396, baseEnd_5882396] using wordTrace_append hprefix tailTrace_5882396
  have hstable : (prefixWord ++ tailWord_5882396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882396).length < 2 ^ (prefixWord ++ tailWord_5882396).sum := by decide
  have hdescent : baseEnd_5882396 < baseStart_5882396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882423 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 3]
def baseStart_5882423 : Nat := 118140960795 + 5882423 * 2 ^ 59
def prefixEnd_5882423 : Nat := 4983230072969 + 3 ^ 40 * 5882423 * 2
def baseEnd_5882423 : Nat := 3020510412062943726659735

theorem tailTrace_5882423 : CollatzResearch.WordTrace tailWord_5882423 prefixEnd_5882423 3020510412062943726659735 := by
  unfold tailWord_5882423
  simp only [CollatzResearch.WordTrace]
  refine ⟨214549592767993583710203923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143033061845329055806802615 214549592767993583710203923)
  ·
    refine ⟨321824389151990375565305885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214549592767993583710203923 321824389151990375565305885)
    ·
      refine ⟨120684145931996390836989707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321824389151990375565305885 120684145931996390836989707)
      ·
        refine ⟨181026218897994586255484561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120684145931996390836989707 181026218897994586255484561)
        ·
          refine ⟨135769664173495939691613421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181026218897994586255484561 135769664173495939691613421)
          ·
            refine ⟨50913624065060977384355033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135769664173495939691613421 50913624065060977384355033)
            ·
              refine ⟨38185218048795733038266275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50913624065060977384355033 38185218048795733038266275)
              ·
                refine ⟨57277827073193599557399413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38185218048795733038266275 57277827073193599557399413)
                ·
                  refine ⟨5369796288111899958506195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57277827073193599557399413 5369796288111899958506195)
                  ·
                    refine ⟨8054694432167849937759293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5369796288111899958506195 8054694432167849937759293)
                    ·
                      refine ⟨3020510412062943726659735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8054694432167849937759293 3020510412062943726659735)
                      ·
                        rfl

theorem cell23_5882423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_5882423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882423 prefixEnd_5882423 := by exact prefixLift 5882423
  have htrace : WordTrace (prefixWord ++ tailWord_5882423) baseStart_5882423 baseEnd_5882423 := by
    simpa [prefixWord, tailWord_5882423, baseEnd_5882423] using wordTrace_append hprefix tailTrace_5882423
  have hstable : (prefixWord ++ tailWord_5882423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882423).length < 2 ^ (prefixWord ++ tailWord_5882423).sum := by decide
  have hdescent : baseEnd_5882423 < baseStart_5882423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882450 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_5882450 : Nat := 118140960795 + 5882450 * 2 ^ 59
def prefixEnd_5882450 : Nat := 4983230072969 + 3 ^ 40 * 5882450 * 2
def baseEnd_5882450 : Nat := 3020524276040615121022111

theorem tailTrace_5882450 : CollatzResearch.WordTrace tailWord_5882450 prefixEnd_5882450 3020524276040615121022111 := by
  unfold tailWord_5882450
  simp only [CollatzResearch.WordTrace]
  refine ⟨53637644384723941830359201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143033718359263844880957869 53637644384723941830359201)
  ·
    refine ⟨40228233288542956372769401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53637644384723941830359201 40228233288542956372769401)
    ·
      refine ⟨30171174966407217279577051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40228233288542956372769401 30171174966407217279577051)
      ·
        refine ⟨45256762449610825919365577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30171174966407217279577051 45256762449610825919365577)
        ·
          refine ⟨33942571837208119439524183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45256762449610825919365577 33942571837208119439524183)
          ·
            refine ⟨50913857755812179159286275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33942571837208119439524183 50913857755812179159286275)
            ·
              refine ⟨76370786633718268738929413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50913857755812179159286275 76370786633718268738929413)
              ·
                refine ⟨14319522493822175388549265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76370786633718268738929413 14319522493822175388549265)
                ·
                  refine ⟨10739641870366631541411949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14319522493822175388549265 10739641870366631541411949)
                  ·
                    refine ⟨4027365701387486828029481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10739641870366631541411949 4027365701387486828029481)
                    ·
                      refine ⟨3020524276040615121022111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027365701387486828029481 3020524276040615121022111)
                      ·
                        rfl

theorem cell23_5882450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_5882450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882450 prefixEnd_5882450 := by exact prefixLift 5882450
  have htrace : WordTrace (prefixWord ++ tailWord_5882450) baseStart_5882450 baseEnd_5882450 := by
    simpa [prefixWord, tailWord_5882450, baseEnd_5882450] using wordTrace_append hprefix tailTrace_5882450
  have hstable : (prefixWord ++ tailWord_5882450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882450).length < 2 ^ (prefixWord ++ tailWord_5882450).sum := by decide
  have hdescent : baseEnd_5882450 < baseStart_5882450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882476 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_5882476 : Nat := 118140960795 + 5882476 * 2 ^ 59
def prefixEnd_5882476 : Nat := 4983230072969 + 3 ^ 40 * 5882476 * 2
def baseEnd_5882476 : Nat := 3020537626537632019296991

theorem tailTrace_5882476 : CollatzResearch.WordTrace tailWord_5882476 prefixEnd_5882476 3020537626537632019296991 := by
  unfold tailWord_5882476
  simp only [CollatzResearch.WordTrace]
  refine ⟨107275762918400786880941641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143034350557867715841255521 107275762918400786880941641)
  ·
    refine ⟨80456822188800590160706231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107275762918400786880941641 80456822188800590160706231)
    ·
      refine ⟨120685233283200885241059347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80456822188800590160706231 120685233283200885241059347)
      ·
        refine ⟨181027849924801327861589021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120685233283200885241059347 181027849924801327861589021)
        ·
          refine ⟨67885443721800497948095883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181027849924801327861589021 67885443721800497948095883)
          ·
            refine ⟨101828165582700746922143825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67885443721800497948095883 101828165582700746922143825)
            ·
              refine ⟨76371124187025560191607869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101828165582700746922143825 76371124187025560191607869)
              ·
                refine ⟨28639171570134585071852951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76371124187025560191607869 28639171570134585071852951)
                ·
                  refine ⟨42958757355201877607779427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28639171570134585071852951 42958757355201877607779427)
                  ·
                    refine ⟨64438136032802816411669141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42958757355201877607779427 64438136032802816411669141)
                    ·
                      refine ⟨3020537626537632019296991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64438136032802816411669141 3020537626537632019296991)
                      ·
                        rfl

theorem cell23_5882476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_5882476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882476 prefixEnd_5882476 := by exact prefixLift 5882476
  have htrace : WordTrace (prefixWord ++ tailWord_5882476) baseStart_5882476 baseEnd_5882476 := by
    simpa [prefixWord, tailWord_5882476, baseEnd_5882476] using wordTrace_append hprefix tailTrace_5882476
  have hstable : (prefixWord ++ tailWord_5882476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882476).length < 2 ^ (prefixWord ++ tailWord_5882476).sum := by decide
  have hdescent : baseEnd_5882476 < baseStart_5882476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882514 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_5882514 : Nat := 118140960795 + 5882514 * 2 ^ 59
def prefixEnd_5882514 : Nat := 4983230072969 + 3 ^ 40 * 5882514 * 2
def baseEnd_5882514 : Nat := 3020557138802502870621817

theorem tailTrace_5882514 : CollatzResearch.WordTrace tailWord_5882514 prefixEnd_5882514 3020557138802502870621817 := by
  unfold tailWord_5882514
  simp only [CollatzResearch.WordTrace]
  refine ⟨53638227952665976562941649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143035274540442604167844397 53638227952665976562941649)
  ·
    refine ⟨40228670964499482422206237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53638227952665976562941649 40228670964499482422206237)
    ·
      refine ⟨15085751611687305908327339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40228670964499482422206237 15085751611687305908327339)
      ·
        refine ⟨22628627417530958862491009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15085751611687305908327339 22628627417530958862491009)
        ·
          refine ⟨16971470563148219146868257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22628627417530958862491009 16971470563148219146868257)
          ·
            refine ⟨12728602922361164360151193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16971470563148219146868257 12728602922361164360151193)
            ·
              refine ⟨9546452191770873270113395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12728602922361164360151193 9546452191770873270113395)
              ·
                refine ⟨14319678287656309905170093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9546452191770873270113395 14319678287656309905170093)
                ·
                  refine ⟨5369879357871116214438785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14319678287656309905170093 5369879357871116214438785)
                  ·
                    refine ⟨4027409518403337160829089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5369879357871116214438785 4027409518403337160829089)
                    ·
                      refine ⟨3020557138802502870621817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027409518403337160829089 3020557138802502870621817)
                      ·
                        rfl

theorem cell23_5882514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_5882514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882514 prefixEnd_5882514 := by exact prefixLift 5882514
  have htrace : WordTrace (prefixWord ++ tailWord_5882514) baseStart_5882514 baseEnd_5882514 := by
    simpa [prefixWord, tailWord_5882514, baseEnd_5882514] using wordTrace_append hprefix tailTrace_5882514
  have hstable : (prefixWord ++ tailWord_5882514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882514).length < 2 ^ (prefixWord ++ tailWord_5882514).sum := by decide
  have hdescent : baseEnd_5882514 < baseStart_5882514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882557 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_5882557 : Nat := 118140960795 + 5882557 * 2 ^ 59
def prefixEnd_5882557 : Nat := 4983230072969 + 3 ^ 40 * 5882557 * 2
def baseEnd_5882557 : Nat := 3020579218470646202384119

theorem tailTrace_5882557 : CollatzResearch.WordTrace tailWord_5882557 prefixEnd_5882557 3020579218470646202384119 := by
  unfold tailWord_5882557
  simp only [CollatzResearch.WordTrace]
  refine ⟨214554480149508124595581925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143036320099672083063721283 214554480149508124595581925)
  ·
    refine ⟨40228965028032773361671611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214554480149508124595581925 40228965028032773361671611)
    ·
      refine ⟨60343447542049160042507417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40228965028032773361671611 60343447542049160042507417)
      ·
        refine ⟨45257585656536870031880563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60343447542049160042507417 45257585656536870031880563)
        ·
          refine ⟨67886378484805305047820845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45257585656536870031880563 67886378484805305047820845)
          ·
            refine ⟨25457391931801989392932817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67886378484805305047820845 25457391931801989392932817)
            ·
              refine ⟨19093043948851492044699613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25457391931801989392932817 19093043948851492044699613)
              ·
                refine ⟨7159891480819309516762355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19093043948851492044699613 7159891480819309516762355)
                ·
                  refine ⟨10739837221228964275143533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7159891480819309516762355 10739837221228964275143533)
                  ·
                    refine ⟨4027438957960861603178825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10739837221228964275143533 4027438957960861603178825)
                    ·
                      refine ⟨3020579218470646202384119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027438957960861603178825 3020579218470646202384119)
                      ·
                        rfl

theorem cell23_5882557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_5882557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882557 prefixEnd_5882557 := by exact prefixLift 5882557
  have htrace : WordTrace (prefixWord ++ tailWord_5882557) baseStart_5882557 baseEnd_5882557 := by
    simpa [prefixWord, tailWord_5882557, baseEnd_5882557] using wordTrace_append hprefix tailTrace_5882557
  have hstable : (prefixWord ++ tailWord_5882557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882557).length < 2 ^ (prefixWord ++ tailWord_5882557).sum := by decide
  have hdescent : baseEnd_5882557 < baseStart_5882557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882603 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 3]
def baseStart_5882603 : Nat := 118140960795 + 5882603 * 2 ^ 59
def prefixEnd_5882603 : Nat := 4983230072969 + 3 ^ 40 * 5882603 * 2
def baseEnd_5882603 : Nat := 3020602838580753022408907

theorem tailTrace_5882603 : CollatzResearch.WordTrace tailWord_5882603 prefixEnd_5882603 3020602838580753022408907 := by
  unfold tailWord_5882603
  simp only [CollatzResearch.WordTrace]
  refine ⟨214556157907341474451756463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143037438604894316301170975 214556157907341474451756463)
  ·
    refine ⟨321834236861012211677634695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214556157907341474451756463 321834236861012211677634695)
    ·
      refine ⟨482751355291518317516452043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321834236861012211677634695 482751355291518317516452043)
      ·
        refine ⟨724127032937277476274678065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482751355291518317516452043 724127032937277476274678065)
        ·
          refine ⟨543095274702958107206008549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724127032937277476274678065 543095274702958107206008549)
          ·
            refine ⟨101830364006804645101126603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 543095274702958107206008549 101830364006804645101126603)
            ·
              refine ⟨152745546010206967651689905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101830364006804645101126603 152745546010206967651689905)
              ·
                refine ⟨114559159507655225738767429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152745546010206967651689905 114559159507655225738767429)
                ·
                  refine ⟨21479842407685354826018893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114559159507655225738767429 21479842407685354826018893)
                  ·
                    refine ⟨8054940902882008059757085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21479842407685354826018893 8054940902882008059757085)
                    ·
                      refine ⟨3020602838580753022408907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8054940902882008059757085 3020602838580753022408907)
                      ·
                        rfl

theorem cell23_5882603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 3].length) (baseStart_5882603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882603 prefixEnd_5882603 := by exact prefixLift 5882603
  have htrace : WordTrace (prefixWord ++ tailWord_5882603) baseStart_5882603 baseEnd_5882603 := by
    simpa [prefixWord, tailWord_5882603, baseEnd_5882603] using wordTrace_append hprefix tailTrace_5882603
  have hstable : (prefixWord ++ tailWord_5882603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882603).length < 2 ^ (prefixWord ++ tailWord_5882603).sum := by decide
  have hdescent : baseEnd_5882603 < baseStart_5882603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882633 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_5882633 : Nat := 118140960795 + 5882633 * 2 ^ 59
def prefixEnd_5882633 : Nat := 4983230072969 + 3 ^ 40 * 5882633 * 2
def baseEnd_5882633 : Nat := 3020618243000387905033769

theorem tailTrace_5882633 : CollatzResearch.WordTrace tailWord_5882633 prefixEnd_5882633 3020618243000387905033769 := by
  unfold tailWord_5882633
  simp only [CollatzResearch.WordTrace]
  refine ⟨214557252097232789575348553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143038168064821859716899035 214557252097232789575348553)
  ·
    refine ⟨160917939072924592181511415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214557252097232789575348553 160917939072924592181511415)
    ·
      refine ⟨241376908609386888272267123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160917939072924592181511415 241376908609386888272267123)
      ·
        refine ⟨362065362914080332408400685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241376908609386888272267123 362065362914080332408400685)
        ·
          refine ⟨135774511092780124653150257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362065362914080332408400685 135774511092780124653150257)
          ·
            refine ⟨101830883319585093489862693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135774511092780124653150257 101830883319585093489862693)
            ·
              refine ⟨19093290622422205029349255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101830883319585093489862693 19093290622422205029349255)
              ·
                refine ⟨28639935933633307544023883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19093290622422205029349255 28639935933633307544023883)
                ·
                  refine ⟨42959903900449961316035825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28639935933633307544023883 42959903900449961316035825)
                  ·
                    refine ⟨32219927925337470987026869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42959903900449961316035825 32219927925337470987026869)
                    ·
                      refine ⟨3020618243000387905033769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32219927925337470987026869 3020618243000387905033769)
                      ·
                        rfl

theorem cell23_5882633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_5882633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882633 prefixEnd_5882633 := by exact prefixLift 5882633
  have htrace : WordTrace (prefixWord ++ tailWord_5882633) baseStart_5882633 baseEnd_5882633 := by
    simpa [prefixWord, tailWord_5882633, baseEnd_5882633] using wordTrace_append hprefix tailTrace_5882633
  have hstable : (prefixWord ++ tailWord_5882633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882633).length < 2 ^ (prefixWord ++ tailWord_5882633).sum := by decide
  have hdescent : baseEnd_5882633 < baseStart_5882633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882643 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 4]
def baseStart_5882643 : Nat := 118140960795 + 5882643 * 2 ^ 59
def prefixEnd_5882643 : Nat := 4983230072969 + 3 ^ 40 * 5882643 * 2
def baseEnd_5882643 : Nat := 3020623377806932865908723

theorem tailTrace_5882643 : CollatzResearch.WordTrace tailWord_5882643 prefixEnd_5882643 3020623377806932865908723 := by
  unfold tailWord_5882643
  simp only [CollatzResearch.WordTrace]
  refine ⟨214557616827196561283212583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143038411218131040855475055 214557616827196561283212583)
  ·
    refine ⟨321836425240794841924818875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214557616827196561283212583 321836425240794841924818875)
    ·
      refine ⟨482754637861192262887228313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321836425240794841924818875 482754637861192262887228313)
      ·
        refine ⟨362065978395894197165421235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482754637861192262887228313 362065978395894197165421235)
        ·
          refine ⟨543098967593841295748131853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362065978395894197165421235 543098967593841295748131853)
          ·
            refine ⟨203662112847690485905549445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 543098967593841295748131853 203662112847690485905549445)
            ·
              refine ⟨38186646158941966107290521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203662112847690485905549445 38186646158941966107290521)
              ·
                refine ⟨28639984619206474580467891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38186646158941966107290521 28639984619206474580467891)
                ·
                  refine ⟨42959976928809711870701837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28639984619206474580467891 42959976928809711870701837)
                  ·
                    refine ⟨16109991348303641951513189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42959976928809711870701837 16109991348303641951513189)
                    ·
                      refine ⟨3020623377806932865908723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16109991348303641951513189 3020623377806932865908723)
                      ·
                        rfl

theorem cell23_5882643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_5882643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882643 prefixEnd_5882643 := by exact prefixLift 5882643
  have htrace : WordTrace (prefixWord ++ tailWord_5882643) baseStart_5882643 baseEnd_5882643 := by
    simpa [prefixWord, tailWord_5882643, baseEnd_5882643] using wordTrace_append hprefix tailTrace_5882643
  have hstable : (prefixWord ++ tailWord_5882643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882643).length < 2 ^ (prefixWord ++ tailWord_5882643).sum := by decide
  have hdescent : baseEnd_5882643 < baseStart_5882643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882673 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_5882673 : Nat := 118140960795 + 5882673 * 2 ^ 59
def prefixEnd_5882673 : Nat := 4983230072969 + 3 ^ 40 * 5882673 * 2
def baseEnd_5882673 : Nat := 3020638782226567748533585

theorem tailTrace_5882673 : CollatzResearch.WordTrace tailWord_5882673 prefixEnd_5882673 3020638782226567748533585 := by
  unfold tailWord_5882673
  simp only [CollatzResearch.WordTrace]
  refine ⟨214558711017087876406804673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143039140678058584271203115 214558711017087876406804673)
  ·
    refine ⟨160919033262815907305103505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214558711017087876406804673 160919033262815907305103505)
    ·
      refine ⟨120689274947111930478827629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160919033262815907305103505 120689274947111930478827629)
      ·
        refine ⟨45258478105166973929560361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120689274947111930478827629 45258478105166973929560361)
        ·
          refine ⟨33943858578875230447170271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45258478105166973929560361 33943858578875230447170271)
          ·
            refine ⟨50915787868312845670755407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33943858578875230447170271 50915787868312845670755407)
            ·
              refine ⟨76373681802469268506133111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50915787868312845670755407 76373681802469268506133111)
              ·
                refine ⟨114560522703703902759199667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76373681802469268506133111 114560522703703902759199667)
                ·
                  refine ⟨171840784055555854138799501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114560522703703902759199667 171840784055555854138799501)
                  ·
                    refine ⟨64440294020833445302049813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171840784055555854138799501 64440294020833445302049813)
                    ·
                      refine ⟨3020638782226567748533585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64440294020833445302049813 3020638782226567748533585)
                      ·
                        rfl

theorem cell23_5882673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_5882673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882673 prefixEnd_5882673 := by exact prefixLift 5882673
  have htrace : WordTrace (prefixWord ++ tailWord_5882673) baseStart_5882673 baseEnd_5882673 := by
    simpa [prefixWord, tailWord_5882673, baseEnd_5882673] using wordTrace_append hprefix tailTrace_5882673
  have hstable : (prefixWord ++ tailWord_5882673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882673).length < 2 ^ (prefixWord ++ tailWord_5882673).sum := by decide
  have hdescent : baseEnd_5882673 < baseStart_5882673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882677 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_5882677 : Nat := 118140960795 + 5882677 * 2 ^ 59
def prefixEnd_5882677 : Nat := 4983230072969 + 3 ^ 40 * 5882677 * 2
def baseEnd_5882677 : Nat := 3020640836149185732883567

theorem tailTrace_5882677 : CollatzResearch.WordTrace tailWord_5882677 prefixEnd_5882677 3020640836149185732883567 := by
  unfold tailWord_5882677
  simp only [CollatzResearch.WordTrace]
  refine ⟨214558856909073385089950285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143039237939382256726633523 214558856909073385089950285)
  ·
    refine ⟨80459571340902519408731357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214558856909073385089950285 80459571340902519408731357)
    ·
      refine ⟨30172339252838444778274259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80459571340902519408731357 30172339252838444778274259)
      ·
        refine ⟨45258508879257667167411389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30172339252838444778274259 45258508879257667167411389)
        ·
          refine ⟨16971940829721625187779271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45258508879257667167411389 16971940829721625187779271)
          ·
            refine ⟨25457911244582437781668907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16971940829721625187779271 25457911244582437781668907)
            ·
              refine ⟨38186866866873656672503361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25457911244582437781668907 38186866866873656672503361)
              ·
                refine ⟨28640150150155242504377521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38186866866873656672503361 28640150150155242504377521)
                ·
                  refine ⟨21480112612616431878283141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28640150150155242504377521 21480112612616431878283141)
                  ·
                    refine ⟨4027521114865580977178089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21480112612616431878283141 4027521114865580977178089)
                    ·
                      refine ⟨3020640836149185732883567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027521114865580977178089 3020640836149185732883567)
                      ·
                        rfl

theorem cell23_5882677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_5882677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882677 prefixEnd_5882677 := by exact prefixLift 5882677
  have htrace : WordTrace (prefixWord ++ tailWord_5882677) baseStart_5882677 baseEnd_5882677 := by
    simpa [prefixWord, tailWord_5882677, baseEnd_5882677] using wordTrace_append hprefix tailTrace_5882677
  have hstable : (prefixWord ++ tailWord_5882677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882677).length < 2 ^ (prefixWord ++ tailWord_5882677).sum := by decide
  have hdescent : baseEnd_5882677 < baseStart_5882677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882680 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_5882680 : Nat := 118140960795 + 5882680 * 2 ^ 59
def prefixEnd_5882680 : Nat := 4983230072969 + 3 ^ 40 * 5882680 * 2
def baseEnd_5882680 : Nat := 3020642376591149221146053

theorem tailTrace_5882680 : CollatzResearch.WordTrace tailWord_5882680 prefixEnd_5882680 3020642376591149221146053 := by
  unfold tailWord_5882680
  simp only [CollatzResearch.WordTrace]
  refine ⟨107279483164031258301154747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143039310885375011068206329 107279483164031258301154747)
  ·
    refine ⟨160919224746046887451732121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107279483164031258301154747 160919224746046887451732121)
    ·
      refine ⟨120689418559535165588799091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160919224746046887451732121 120689418559535165588799091)
      ·
        refine ⟨181034127839302748383198637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120689418559535165588799091 181034127839302748383198637)
        ·
          refine ⟨67887797939738530643699489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181034127839302748383198637 67887797939738530643699489)
          ·
            refine ⟨50915848454803897982774617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67887797939738530643699489 50915848454803897982774617)
            ·
              refine ⟨38186886341102923487080963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50915848454803897982774617 38186886341102923487080963)
              ·
                refine ⟨57280329511654385230621445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38186886341102923487080963 57280329511654385230621445)
                ·
                  refine ⟨10740061783435197230741521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57280329511654385230621445 10740061783435197230741521)
                  ·
                    refine ⟨8055046337576397923056141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10740061783435197230741521 8055046337576397923056141)
                    ·
                      refine ⟨3020642376591149221146053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8055046337576397923056141 3020642376591149221146053)
                      ·
                        rfl

theorem cell23_5882680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_5882680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882680 prefixEnd_5882680 := by exact prefixLift 5882680
  have htrace : WordTrace (prefixWord ++ tailWord_5882680) baseStart_5882680 baseEnd_5882680 := by
    simpa [prefixWord, tailWord_5882680, baseEnd_5882680] using wordTrace_append hprefix tailTrace_5882680
  have hstable : (prefixWord ++ tailWord_5882680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882680).length < 2 ^ (prefixWord ++ tailWord_5882680).sum := by decide
  have hdescent : baseEnd_5882680 < baseStart_5882680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882687 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 3, 4]
def baseStart_5882687 : Nat := 118140960795 + 5882687 * 2 ^ 59
def prefixEnd_5882687 : Nat := 4983230072969 + 3 ^ 40 * 5882687 * 2
def baseEnd_5882687 : Nat := 1006881990318576897919507

theorem tailTrace_5882687 : CollatzResearch.WordTrace tailWord_5882687 prefixEnd_5882687 1006881990318576897919507 := by
  unfold tailWord_5882687
  simp only [CollatzResearch.WordTrace]
  refine ⟨214559221639037156797814315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143039481092691437865209543 214559221639037156797814315)
  ·
    refine ⟨321838832458555735196721473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214559221639037156797814315 321838832458555735196721473)
    ·
      refine ⟨241379124343916801397541105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321838832458555735196721473 241379124343916801397541105)
      ·
        refine ⟨181034343257937601048155829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241379124343916801397541105 181034343257937601048155829)
        ·
          refine ⟨16971969680431650098264609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181034343257937601048155829 16971969680431650098264609)
          ·
            refine ⟨12728977260323737573698457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16971969680431650098264609 12728977260323737573698457)
            ·
              refine ⟨9546732945242803180273843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12728977260323737573698457 9546732945242803180273843)
              ·
                refine ⟨14320099417864204770410765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9546732945242803180273843 14320099417864204770410765)
                ·
                  refine ⟨5370037281699076788904037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14320099417864204770410765 5370037281699076788904037)
                  ·
                    refine ⟨1006881990318576897919507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5370037281699076788904037 1006881990318576897919507)
                    ·
                      rfl

theorem cell23_5882687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 4].length) (baseStart_5882687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882687 prefixEnd_5882687 := by exact prefixLift 5882687
  have htrace : WordTrace (prefixWord ++ tailWord_5882687) baseStart_5882687 baseEnd_5882687 := by
    simpa [prefixWord, tailWord_5882687, baseEnd_5882687] using wordTrace_append hprefix tailTrace_5882687
  have hstable : (prefixWord ++ tailWord_5882687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882687).length < 2 ^ (prefixWord ++ tailWord_5882687).sum := by decide
  have hdescent : baseEnd_5882687 < baseStart_5882687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882737 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 4, 3, 2]
def baseStart_5882737 : Nat := 118140960795 + 5882737 * 2 ^ 59
def prefixEnd_5882737 : Nat := 4983230072969 + 3 ^ 40 * 5882737 * 2
def baseEnd_5882737 : Nat := 3020671644988455498133291

theorem tailTrace_5882737 : CollatzResearch.WordTrace tailWord_5882737 prefixEnd_5882737 3020671644988455498133291 := by
  unfold tailWord_5882737
  simp only [CollatzResearch.WordTrace]
  refine ⟨214561045288856015337134465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143040696859237343558089643 214561045288856015337134465)
  ·
    refine ⟨160920783966642011502850849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214561045288856015337134465 160920783966642011502850849)
    ·
      refine ⟨120690587974981508627138137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160920783966642011502850849 120690587974981508627138137)
      ·
        refine ⟨90517940981236131470353603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120690587974981508627138137 90517940981236131470353603)
        ·
          refine ⟨135776911471854197205530405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90517940981236131470353603 135776911471854197205530405)
          ·
            refine ⟨25458170900972661976036951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135776911471854197205530405 25458170900972661976036951)
            ·
              refine ⟨38187256351458992964055427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25458170900972661976036951 38187256351458992964055427)
              ·
                refine ⟨57280884527188489446083141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38187256351458992964055427 57280884527188489446083141)
                ·
                  refine ⟨10740165848847841771140589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57280884527188489446083141 10740165848847841771140589)
                  ·
                    refine ⟨4027562193317940664177721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10740165848847841771140589 4027562193317940664177721)
                    ·
                      refine ⟨3020671644988455498133291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027562193317940664177721 3020671644988455498133291)
                      ·
                        rfl

theorem cell23_5882737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_5882737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882737 prefixEnd_5882737 := by exact prefixLift 5882737
  have htrace : WordTrace (prefixWord ++ tailWord_5882737) baseStart_5882737 baseEnd_5882737 := by
    simpa [prefixWord, tailWord_5882737, baseEnd_5882737] using wordTrace_append hprefix tailTrace_5882737
  have hstable : (prefixWord ++ tailWord_5882737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882737).length < 2 ^ (prefixWord ++ tailWord_5882737).sum := by decide
  have hdescent : baseEnd_5882737 < baseStart_5882737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882787 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 3]
def baseStart_5882787 : Nat := 118140960795 + 5882787 * 2 ^ 59
def prefixEnd_5882787 : Nat := 4983230072969 + 3 ^ 40 * 5882787 * 2
def baseEnd_5882787 : Nat := 3020697319021180302508061

theorem tailTrace_5882787 : CollatzResearch.WordTrace tailWord_5882787 prefixEnd_5882787 3020697319021180302508061 := by
  unfold tailWord_5882787
  simp only [CollatzResearch.WordTrace]
  refine ⟨214562868938674873876454615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143041912625783249250969743 214562868938674873876454615)
  ·
    refine ⟨321844303408012310814681923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214562868938674873876454615 321844303408012310814681923)
    ·
      refine ⟨482766455112018466222022885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321844303408012310814681923 482766455112018466222022885)
      ·
        refine ⟨90518710333503462416629291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 482766455112018466222022885 90518710333503462416629291)
        ·
          refine ⟨135778065500255193624943937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90518710333503462416629291 135778065500255193624943937)
          ·
            refine ⟨101833549125191395218707953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135778065500255193624943937 101833549125191395218707953)
            ·
              refine ⟨76375161843893546414030965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101833549125191395218707953 76375161843893546414030965)
              ·
                refine ⟨7160171422865019976315403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76375161843893546414030965 7160171422865019976315403)
                ·
                  refine ⟨10740257134297529964473105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7160171422865019976315403 10740257134297529964473105)
                  ·
                    refine ⟨8055192850723147473354829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10740257134297529964473105 8055192850723147473354829)
                    ·
                      refine ⟨3020697319021180302508061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8055192850723147473354829 3020697319021180302508061)
                      ·
                        rfl

theorem cell23_5882787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_5882787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882787 prefixEnd_5882787 := by exact prefixLift 5882787
  have htrace : WordTrace (prefixWord ++ tailWord_5882787) baseStart_5882787 baseEnd_5882787 := by
    simpa [prefixWord, tailWord_5882787, baseEnd_5882787] using wordTrace_append hprefix tailTrace_5882787
  have hstable : (prefixWord ++ tailWord_5882787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882787).length < 2 ^ (prefixWord ++ tailWord_5882787).sum := by decide
  have hdescent : baseEnd_5882787 < baseStart_5882787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882834 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_5882834 : Nat := 118140960795 + 5882834 * 2 ^ 59
def prefixEnd_5882834 : Nat := 4983230072969 + 3 ^ 40 * 5882834 * 2
def baseEnd_5882834 : Nat := 3020721452611941618620345

theorem tailTrace_5882834 : CollatzResearch.WordTrace tailWord_5882834 prefixEnd_5882834 3020721452611941618620345 := by
  unfold tailWord_5882834
  simp only [CollatzResearch.WordTrace]
  refine ⟨53641145792376150225853889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143043055446336400602277037 53641145792376150225853889)
  ·
    refine ⟨40230859344282112669390417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53641145792376150225853889 40230859344282112669390417)
    ·
      refine ⟨30173144508211584502042813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40230859344282112669390417 30173144508211584502042813)
      ·
        refine ⟨11314929190579344188266055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30173144508211584502042813 11314929190579344188266055)
        ·
          refine ⟨16972393785869016282399083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11314929190579344188266055 16972393785869016282399083)
          ·
            refine ⟨25458590678803524423598625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16972393785869016282399083 25458590678803524423598625)
            ·
              refine ⟨19093943009102643317698969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25458590678803524423598625 19093943009102643317698969)
              ·
                refine ⟨14320457256826982488274227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19093943009102643317698969 14320457256826982488274227)
                ·
                  refine ⟨21480685885240473732411341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14320457256826982488274227 21480685885240473732411341)
                  ·
                    refine ⟨8055257206965177649654253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21480685885240473732411341 8055257206965177649654253)
                    ·
                      refine ⟨3020721452611941618620345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8055257206965177649654253 3020721452611941618620345)
                      ·
                        rfl

theorem cell23_5882834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_5882834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882834 prefixEnd_5882834 := by exact prefixLift 5882834
  have htrace : WordTrace (prefixWord ++ tailWord_5882834) baseStart_5882834 baseEnd_5882834 := by
    simpa [prefixWord, tailWord_5882834, baseEnd_5882834] using wordTrace_append hprefix tailTrace_5882834
  have hstable : (prefixWord ++ tailWord_5882834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882834).length < 2 ^ (prefixWord ++ tailWord_5882834).sum := by decide
  have hdescent : baseEnd_5882834 < baseStart_5882834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882838 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_5882838 : Nat := 118140960795 + 5882838 * 2 ^ 59
def prefixEnd_5882838 : Nat := 4983230072969 + 3 ^ 40 * 5882838 * 2
def baseEnd_5882838 : Nat := 3020723506534559602970327

theorem tailTrace_5882838 : CollatzResearch.WordTrace tailWord_5882838 prefixEnd_5882838 3020723506534559602970327 := by
  unfold tailWord_5882838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13410295566343131849160073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143043152707660073057707445 13410295566343131849160073)
  ·
    refine ⟨10057721674757348886870055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13410295566343131849160073 10057721674757348886870055)
    ·
      refine ⟨15086582512136023330305083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10057721674757348886870055 15086582512136023330305083)
      ·
        refine ⟨22629873768204034995457625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15086582512136023330305083 22629873768204034995457625)
        ·
          refine ⟨16972405326153026246593219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22629873768204034995457625 16972405326153026246593219)
          ·
            refine ⟨25458607989229539369889829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16972405326153026246593219 25458607989229539369889829)
            ·
              refine ⟨4773488997980538631854343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25458607989229539369889829 4773488997980538631854343)
              ·
                refine ⟨7160233496970807947781515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773488997980538631854343 7160233496970807947781515)
                ·
                  refine ⟨10740350245456211921672273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7160233496970807947781515 10740350245456211921672273)
                  ·
                    refine ⟨8055262684092158941254205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10740350245456211921672273 8055262684092158941254205)
                    ·
                      refine ⟨3020723506534559602970327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8055262684092158941254205 3020723506534559602970327)
                      ·
                        rfl

theorem cell23_5882838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_5882838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882838 prefixEnd_5882838 := by exact prefixLift 5882838
  have htrace : WordTrace (prefixWord ++ tailWord_5882838) baseStart_5882838 baseEnd_5882838 := by
    simpa [prefixWord, tailWord_5882838, baseEnd_5882838] using wordTrace_append hprefix tailTrace_5882838
  have hstable : (prefixWord ++ tailWord_5882838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882838).length < 2 ^ (prefixWord ++ tailWord_5882838).sum := by decide
  have hdescent : baseEnd_5882838 < baseStart_5882838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882860 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_5882860 : Nat := 118140960795 + 5882860 * 2 ^ 59
def prefixEnd_5882860 : Nat := 4983230072969 + 3 ^ 40 * 5882860 * 2
def baseEnd_5882860 : Nat := 3020734803108958516895225

theorem tailTrace_5882860 : CollatzResearch.WordTrace tailWord_5882860 prefixEnd_5882860 3020734803108958516895225 := by
  unfold tailWord_5882860
  simp only [CollatzResearch.WordTrace]
  refine ⟨107282765733705203671931017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143043687644940271562574689 107282765733705203671931017)
  ·
    refine ⟨80462074300278902753948263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107282765733705203671931017 80462074300278902753948263)
    ·
      refine ⟨120693111450418354130922395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80462074300278902753948263 120693111450418354130922395)
      ·
        refine ⟨181039667175627531196383593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120693111450418354130922395 181039667175627531196383593)
        ·
          refine ⟨135779750381720648397287695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181039667175627531196383593 135779750381720648397287695)
          ·
            refine ⟨203669625572580972595931543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135779750381720648397287695 203669625572580972595931543)
            ·
              refine ⟨305504438358871458893897315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203669625572580972595931543 305504438358871458893897315)
              ·
                refine ⟨458256657538307188340845973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305504438358871458893897315 458256657538307188340845973)
                ·
                  refine ⟨21480780822108149453477155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 458256657538307188340845973 21480780822108149453477155)
                  ·
                    refine ⟨32221171233162224180215733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21480780822108149453477155 32221171233162224180215733)
                    ·
                      refine ⟨3020734803108958516895225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32221171233162224180215733 3020734803108958516895225)
                      ·
                        rfl

theorem cell23_5882860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_5882860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882860 prefixEnd_5882860 := by exact prefixLift 5882860
  have htrace : WordTrace (prefixWord ++ tailWord_5882860) baseStart_5882860 baseEnd_5882860 := by
    simpa [prefixWord, tailWord_5882860, baseEnd_5882860] using wordTrace_append hprefix tailTrace_5882860
  have hstable : (prefixWord ++ tailWord_5882860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882860).length < 2 ^ (prefixWord ++ tailWord_5882860).sum := by decide
  have hdescent : baseEnd_5882860 < baseStart_5882860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882914 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 7]
def baseStart_5882914 : Nat := 118140960795 + 5882914 * 2 ^ 59
def prefixEnd_5882914 : Nat := 4983230072969 + 3 ^ 40 * 5882914 * 2
def baseEnd_5882914 : Nat := 335640281229366811735553

theorem tailTrace_5882914 : CollatzResearch.WordTrace tailWord_5882914 prefixEnd_5882914 335640281229366811735553 := by
  unfold tailWord_5882914
  simp only [CollatzResearch.WordTrace]
  refine ⟨53641875252303693641581949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143045000672809849710885197 53641875252303693641581949)
  ·
    refine ⟨20115703219613885115593231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53641875252303693641581949 20115703219613885115593231)
    ·
      refine ⟨30173554829420827673389847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20115703219613885115593231 30173554829420827673389847)
      ·
        refine ⟨45260332244131241510084771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30173554829420827673389847 45260332244131241510084771)
        ·
          refine ⟨67890498366196862265127157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45260332244131241510084771 67890498366196862265127157)
          ·
            refine ⟨6364734221830955837355671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67890498366196862265127157 6364734221830955837355671)
            ·
              refine ⟨9547101332746433756033507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6364734221830955837355671 9547101332746433756033507)
              ·
                refine ⟨14320651999119650634050261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9547101332746433756033507 14320651999119650634050261)
                ·
                  refine ⟨335640281229366811735553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14320651999119650634050261 335640281229366811735553)
                  ·
                    rfl

theorem cell23_5882914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_5882914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882914 prefixEnd_5882914 := by exact prefixLift 5882914
  have htrace : WordTrace (prefixWord ++ tailWord_5882914) baseStart_5882914 baseEnd_5882914 := by
    simpa [prefixWord, tailWord_5882914, baseEnd_5882914] using wordTrace_append hprefix tailTrace_5882914
  have hstable : (prefixWord ++ tailWord_5882914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882914).length < 2 ^ (prefixWord ++ tailWord_5882914).sum := by decide
  have hdescent : baseEnd_5882914 < baseStart_5882914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882964 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_5882964 : Nat := 118140960795 + 5882964 * 2 ^ 59
def prefixEnd_5882964 : Nat := 4983230072969 + 3 ^ 40 * 5882964 * 2
def baseEnd_5882964 : Nat := 3020788205097026109994747

theorem tailTrace_5882964 : CollatzResearch.WordTrace tailWord_5882964 prefixEnd_5882964 3020788205097026109994747 := by
  unfold tailWord_5882964
  simp only [CollatzResearch.WordTrace]
  refine ⟨107284662329516816552823973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143046216439355755403765297 107284662329516816552823973)
  ·
    refine ⟨20115874186784403103654495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107284662329516816552823973 20115874186784403103654495)
    ·
      refine ⟨30173811280176604655481743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20115874186784403103654495 30173811280176604655481743)
      ·
        refine ⟨45260716920264906983222615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30173811280176604655481743 45260716920264906983222615)
        ·
          refine ⟨67891075380397360474833923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45260716920264906983222615 67891075380397360474833923)
          ·
            refine ⟨101836613070596040712250885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67891075380397360474833923 101836613070596040712250885)
            ·
              refine ⟨19094364950736757633547041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101836613070596040712250885 19094364950736757633547041)
              ·
                refine ⟨14320773713052568225160281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19094364950736757633547041 14320773713052568225160281)
                ·
                  refine ⟨10740580284789426168870211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14320773713052568225160281 10740580284789426168870211)
                  ·
                    refine ⟨16110870427184139253305317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10740580284789426168870211 16110870427184139253305317)
                    ·
                      refine ⟨3020788205097026109994747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16110870427184139253305317 3020788205097026109994747)
                      ·
                        rfl

theorem cell23_5882964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_5882964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882964 prefixEnd_5882964 := by exact prefixLift 5882964
  have htrace : WordTrace (prefixWord ++ tailWord_5882964) baseStart_5882964 baseEnd_5882964 := by
    simpa [prefixWord, tailWord_5882964, baseEnd_5882964] using wordTrace_append hprefix tailTrace_5882964
  have hstable : (prefixWord ++ tailWord_5882964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882964).length < 2 ^ (prefixWord ++ tailWord_5882964).sum := by decide
  have hdescent : baseEnd_5882964 < baseStart_5882964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5882967 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_5882967 : Nat := 118140960795 + 5882967 * 2 ^ 59
def prefixEnd_5882967 : Nat := 4983230072969 + 3 ^ 40 * 5882967 * 2
def baseEnd_5882967 : Nat := 3020789745538989598257233

theorem tailTrace_5882967 : CollatzResearch.WordTrace tailWord_5882967 prefixEnd_5882967 3020789745538989598257233 := by
  unfold tailWord_5882967
  simp only [CollatzResearch.WordTrace]
  refine ⟨214569434078022764618007155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143046289385348509745338103 214569434078022764618007155)
  ·
    refine ⟨321854151117034146927010733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214569434078022764618007155 321854151117034146927010733)
    ·
      refine ⟨120695306668887805097629025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321854151117034146927010733 120695306668887805097629025)
      ·
        refine ⟨90521480001665853823221769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120695306668887805097629025 90521480001665853823221769)
        ·
          refine ⟨67891110001249390367416327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90521480001665853823221769 67891110001249390367416327)
          ·
            refine ⟨101836665001874085551124491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67891110001249390367416327 101836665001874085551124491)
            ·
              refine ⟨152754997502811128326686737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101836665001874085551124491 152754997502811128326686737)
              ·
                refine ⟨114566248127108346245015053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152754997502811128326686737 114566248127108346245015053)
                ·
                  refine ⟨42962343047665629841880645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114566248127108346245015053 42962343047665629841880645)
                  ·
                    refine ⟨8055439321437305595352621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42962343047665629841880645 8055439321437305595352621)
                    ·
                      refine ⟨3020789745538989598257233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8055439321437305595352621 3020789745538989598257233)
                      ·
                        rfl

theorem cell23_5882967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_5882967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5882967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5882967 prefixEnd_5882967 := by exact prefixLift 5882967
  have htrace : WordTrace (prefixWord ++ tailWord_5882967) baseStart_5882967 baseEnd_5882967 := by
    simpa [prefixWord, tailWord_5882967, baseEnd_5882967] using wordTrace_append hprefix tailTrace_5882967
  have hstable : (prefixWord ++ tailWord_5882967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5882967).length < 2 ^ (prefixWord ++ tailWord_5882967).sum := by decide
  have hdescent : baseEnd_5882967 < baseStart_5882967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5882967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883031 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 3]
def baseStart_5883031 : Nat := 118140960795 + 5883031 * 2 ^ 59
def prefixEnd_5883031 : Nat := 4983230072969 + 3 ^ 40 * 5883031 * 2
def baseEnd_5883031 : Nat := 3020822608300877347856939

theorem tailTrace_5883031 : CollatzResearch.WordTrace tailWord_5883031 prefixEnd_5883031 3020822608300877347856939 := by
  unfold tailWord_5883031
  simp only [CollatzResearch.WordTrace]
  refine ⟨214571768349790903548336947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143047845566527269032224631 214571768349790903548336947)
  ·
    refine ⟨321857652524686355322505421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214571768349790903548336947 321857652524686355322505421)
    ·
      refine ⟨120696619696757383245939533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321857652524686355322505421 120696619696757383245939533)
      ·
        refine ⟨45261232386284018717227325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120696619696757383245939533 45261232386284018717227325)
        ·
          refine ⟨16972962144856507018960247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45261232386284018717227325 16972962144856507018960247)
          ·
            refine ⟨25459443217284760528440371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16972962144856507018960247 25459443217284760528440371)
            ·
              refine ⟨38189164825927140792660557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25459443217284760528440371 38189164825927140792660557)
              ·
                refine ⟨14320936809722677797247709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38189164825927140792660557 14320936809722677797247709)
                ·
                  refine ⟨5370351303646004173967891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14320936809722677797247709 5370351303646004173967891)
                  ·
                    refine ⟨8055526955469006260951837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5370351303646004173967891 8055526955469006260951837)
                    ·
                      refine ⟨3020822608300877347856939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8055526955469006260951837 3020822608300877347856939)
                      ·
                        rfl

theorem cell23_5883031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_5883031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883031 prefixEnd_5883031 := by exact prefixLift 5883031
  have htrace : WordTrace (prefixWord ++ tailWord_5883031) baseStart_5883031 baseEnd_5883031 := by
    simpa [prefixWord, tailWord_5883031, baseEnd_5883031] using wordTrace_append hprefix tailTrace_5883031
  have hstable : (prefixWord ++ tailWord_5883031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883031).length < 2 ^ (prefixWord ++ tailWord_5883031).sum := by decide
  have hdescent : baseEnd_5883031 < baseStart_5883031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883038 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_5883038 : Nat := 118140960795 + 5883038 * 2 ^ 59
def prefixEnd_5883038 : Nat := 4983230072969 + 3 ^ 40 * 5883038 * 2
def baseEnd_5883038 : Nat := 335647355851717646718823

theorem tailTrace_5883038 : CollatzResearch.WordTrace tailWord_5883038 prefixEnd_5883038 335647355851717646718823 := by
  unfold tailWord_5883038
  simp only [CollatzResearch.WordTrace]
  refine ⟨26821502957595692967980221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143048015773843695829227845 26821502957595692967980221)
  ·
    refine ⟨10058063609098384862992583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26821502957595692967980221 10058063609098384862992583)
    ·
      refine ⟨15087095413647577294488875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10058063609098384862992583 15087095413647577294488875)
      ·
        refine ⟨22630643120471365941733313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15087095413647577294488875 22630643120471365941733313)
        ·
          refine ⟨16972982340353524456299985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22630643120471365941733313 16972982340353524456299985)
          ·
            refine ⟨12729736755265143342224989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16972982340353524456299985 12729736755265143342224989)
            ·
              refine ⟨4773651283224428753334371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12729736755265143342224989 4773651283224428753334371)
              ·
                refine ⟨7160476924836643130001557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773651283224428753334371 7160476924836643130001557)
                ·
                  refine ⟨335647355851717646718823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7160476924836643130001557 335647355851717646718823)
                  ·
                    rfl

theorem cell23_5883038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_5883038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883038 prefixEnd_5883038 := by exact prefixLift 5883038
  have htrace : WordTrace (prefixWord ++ tailWord_5883038) baseStart_5883038 baseEnd_5883038 := by
    simpa [prefixWord, tailWord_5883038, baseEnd_5883038] using wordTrace_append hprefix tailTrace_5883038
  have hstable : (prefixWord ++ tailWord_5883038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883038).length < 2 ^ (prefixWord ++ tailWord_5883038).sum := by decide
  have hdescent : baseEnd_5883038 < baseStart_5883038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883065 : List Nat := [1, 2, 1, 4, 1, 5, 1, 3, 1, 1, 3]
def baseStart_5883065 : Nat := 118140960795 + 5883065 * 2 ^ 59
def prefixEnd_5883065 : Nat := 4983230072969 + 3 ^ 40 * 5883065 * 2
def baseEnd_5883065 : Nat := 3020840066643130214831783

theorem tailTrace_5883065 : CollatzResearch.WordTrace tailWord_5883065 prefixEnd_5883065 3020840066643130214831783 := by
  unfold tailWord_5883065
  simp only [CollatzResearch.WordTrace]
  refine ⟨214573008431667727355074649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143048672287778484903383099 214573008431667727355074649)
  ·
    refine ⟨160929756323750795516305987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214573008431667727355074649 160929756323750795516305987)
    ·
      refine ⟨241394634485626193274458981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160929756323750795516305987 241394634485626193274458981)
      ·
        refine ⟨45261493966054911238961059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241394634485626193274458981 45261493966054911238961059)
        ·
          refine ⟨67892240949082366858441589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45261493966054911238961059 67892240949082366858441589)
          ·
            refine ⟨6364897588976471892978899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67892240949082366858441589 6364897588976471892978899)
            ·
              refine ⟨9547346383464707839468349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6364897588976471892978899 9547346383464707839468349)
              ·
                refine ⟨3580254893799265439800631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9547346383464707839468349 3580254893799265439800631)
                ·
                  refine ⟨5370382340698898159700947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3580254893799265439800631 5370382340698898159700947)
                  ·
                    refine ⟨8055573511048347239551421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5370382340698898159700947 8055573511048347239551421)
                    ·
                      refine ⟨3020840066643130214831783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8055573511048347239551421 3020840066643130214831783)
                      ·
                        rfl

theorem cell23_5883065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_5883065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883065 prefixEnd_5883065 := by exact prefixLift 5883065
  have htrace : WordTrace (prefixWord ++ tailWord_5883065) baseStart_5883065 baseEnd_5883065 := by
    simpa [prefixWord, tailWord_5883065, baseEnd_5883065] using wordTrace_append hprefix tailTrace_5883065
  have hstable : (prefixWord ++ tailWord_5883065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883065).length < 2 ^ (prefixWord ++ tailWord_5883065).sum := by decide
  have hdescent : baseEnd_5883065 < baseStart_5883065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883071 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 5, 2, 2]
def baseStart_5883071 : Nat := 118140960795 + 5883071 * 2 ^ 59
def prefixEnd_5883071 : Nat := 4983230072969 + 3 ^ 40 * 5883071 * 2
def baseEnd_5883071 : Nat := 3020843147527057191356755

theorem tailTrace_5883071 : CollatzResearch.WordTrace tailWord_5883071 prefixEnd_5883071 3020843147527057191356755 := by
  unfold tailWord_5883071
  simp only [CollatzResearch.WordTrace]
  refine ⟨214573227269645990379793067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143048818179763993586528711 214573227269645990379793067)
  ·
    refine ⟨321859840904468985569689601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214573227269645990379793067 321859840904468985569689601)
    ·
      refine ⟨241394880678351739177267201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321859840904468985569689601 241394880678351739177267201)
      ·
        refine ⟨181046160508763804382950401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241394880678351739177267201 181046160508763804382950401)
        ·
          refine ⟨135784620381572853287212801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181046160508763804382950401 135784620381572853287212801)
          ·
            refine ⟨101838465286179639965409601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135784620381572853287212801 101838465286179639965409601)
            ·
              refine ⟨76378848964634729974057201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101838465286179639965409601 76378848964634729974057201)
              ·
                refine ⟨57284136723476047480542901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76378848964634729974057201 57284136723476047480542901)
                ·
                  refine ⟨5370387817825879451300897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57284136723476047480542901 5370387817825879451300897)
                  ·
                    refine ⟨4027790863369409588475673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5370387817825879451300897 4027790863369409588475673)
                    ·
                      refine ⟨3020843147527057191356755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027790863369409588475673 3020843147527057191356755)
                      ·
                        rfl

theorem cell23_5883071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_5883071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883071 prefixEnd_5883071 := by exact prefixLift 5883071
  have htrace : WordTrace (prefixWord ++ tailWord_5883071) baseStart_5883071 baseEnd_5883071 := by
    simpa [prefixWord, tailWord_5883071, baseEnd_5883071] using wordTrace_append hprefix tailTrace_5883071
  have hstable : (prefixWord ++ tailWord_5883071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883071).length < 2 ^ (prefixWord ++ tailWord_5883071).sum := by decide
  have hdescent : baseEnd_5883071 < baseStart_5883071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883097 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_5883097 : Nat := 118140960795 + 5883097 * 2 ^ 59
def prefixEnd_5883097 : Nat := 4983230072969 + 3 ^ 40 * 5883097 * 2
def baseEnd_5883097 : Nat := 3020856498024074089631635

theorem tailTrace_5883097 : CollatzResearch.WordTrace tailWord_5883097 prefixEnd_5883097 3020856498024074089631635 := by
  unfold tailWord_5883097
  simp only [CollatzResearch.WordTrace]
  refine ⟨214574175567551796820239545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143049450378367864546826363 214574175567551796820239545)
  ·
    refine ⟨160930631675663847615179659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214574175567551796820239545 160930631675663847615179659)
    ·
      refine ⟨241395947513495771422769489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160930631675663847615179659 241395947513495771422769489)
      ·
        refine ⟨181046960635121828567077117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241395947513495771422769489 181046960635121828567077117)
        ·
          refine ⟨67892610238170685712653919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181046960635121828567077117 67892610238170685712653919)
          ·
            refine ⟨101838915357256028568980879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67892610238170685712653919 101838915357256028568980879)
            ·
              refine ⟨152758373035884042853471319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101838915357256028568980879 152758373035884042853471319)
              ·
                refine ⟨229137559553826064280206979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152758373035884042853471319 229137559553826064280206979)
                ·
                  refine ⟨343706339330739096420310469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229137559553826064280206979 343706339330739096420310469)
                  ·
                    refine ⟨64444938624513580578808213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 343706339330739096420310469 64444938624513580578808213)
                    ·
                      refine ⟨3020856498024074089631635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64444938624513580578808213 3020856498024074089631635)
                      ·
                        rfl

theorem cell23_5883097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_5883097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883097 prefixEnd_5883097 := by exact prefixLift 5883097
  have htrace : WordTrace (prefixWord ++ tailWord_5883097) baseStart_5883097 baseEnd_5883097 := by
    simpa [prefixWord, tailWord_5883097, baseEnd_5883097] using wordTrace_append hprefix tailTrace_5883097
  have hstable : (prefixWord ++ tailWord_5883097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883097).length < 2 ^ (prefixWord ++ tailWord_5883097).sum := by decide
  have hdescent : baseEnd_5883097 < baseStart_5883097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883127 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_5883127 : Nat := 118140960795 + 5883127 * 2 ^ 59
def prefixEnd_5883127 : Nat := 4983230072969 + 3 ^ 40 * 5883127 * 2
def baseEnd_5883127 : Nat := 3020871902443708972256497

theorem tailTrace_5883127 : CollatzResearch.WordTrace tailWord_5883127 prefixEnd_5883127 3020871902443708972256497 := by
  unfold tailWord_5883127
  simp only [CollatzResearch.WordTrace]
  refine ⟨214575269757443111943831635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143050179838295407962554423 214575269757443111943831635)
  ·
    refine ⟨321862904636164667915747453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214575269757443111943831635 321862904636164667915747453)
    ·
      refine ⟨120698589238561750468405295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321862904636164667915747453 120698589238561750468405295)
      ·
        refine ⟨181047883857842625702607943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120698589238561750468405295 181047883857842625702607943)
        ·
          refine ⟨271571825786763938553911915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181047883857842625702607943 271571825786763938553911915)
          ·
            refine ⟨407357738680145907830867873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271571825786763938553911915 407357738680145907830867873)
            ·
              refine ⟨305518304010109430873150905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407357738680145907830867873 305518304010109430873150905)
              ·
                refine ⟨229138728007582073154863179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305518304010109430873150905 229138728007582073154863179)
                ·
                  refine ⟨343708092011373109732294769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229138728007582073154863179 343708092011373109732294769)
                  ·
                    refine ⟨257781069008529832299221077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 343708092011373109732294769 257781069008529832299221077)
                    ·
                      refine ⟨3020871902443708972256497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 257781069008529832299221077 3020871902443708972256497)
                      ·
                        rfl

theorem cell23_5883127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_5883127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883127 prefixEnd_5883127 := by exact prefixLift 5883127
  have htrace : WordTrace (prefixWord ++ tailWord_5883127) baseStart_5883127 baseEnd_5883127 := by
    simpa [prefixWord, tailWord_5883127, baseEnd_5883127] using wordTrace_append hprefix tailTrace_5883127
  have hstable : (prefixWord ++ tailWord_5883127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883127).length < 2 ^ (prefixWord ++ tailWord_5883127).sum := by decide
  have hdescent : baseEnd_5883127 < baseStart_5883127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883164 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_5883164 : Nat := 118140960795 + 5883164 * 2 ^ 59
def prefixEnd_5883164 : Nat := 4983230072969 + 3 ^ 40 * 5883164 * 2
def baseEnd_5883164 : Nat := 3020890901227925327493827

theorem tailTrace_5883164 : CollatzResearch.WordTrace tailWord_5883164 prefixEnd_5883164 3020890901227925327493827 := by
  unfold tailWord_5883164
  simp only [CollatzResearch.WordTrace]
  refine ⟨107288309629154533631464273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143051079505539378175285697 107288309629154533631464273)
  ·
    refine ⟨80466232221865900223598205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107288309629154533631464273 80466232221865900223598205)
    ·
      refine ⟨30174837083199712583849327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80466232221865900223598205 30174837083199712583849327)
      ·
        refine ⟨45262255624799568875773991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30174837083199712583849327 45262255624799568875773991)
        ·
          refine ⟨67893383437199353313660987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45262255624799568875773991 67893383437199353313660987)
          ·
            refine ⟨101840075155799029970491481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67893383437199353313660987 101840075155799029970491481)
            ·
              refine ⟨76380056366849272477868611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101840075155799029970491481 76380056366849272477868611)
              ·
                refine ⟨114570084550273908716802917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76380056366849272477868611 114570084550273908716802917)
                ·
                  refine ⟨21481890853176357884400547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114570084550273908716802917 21481890853176357884400547)
                  ·
                    refine ⟨32222836279764536826600821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21481890853176357884400547 32222836279764536826600821)
                    ·
                      refine ⟨3020890901227925327493827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32222836279764536826600821 3020890901227925327493827)
                      ·
                        rfl

theorem cell23_5883164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_5883164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883164 prefixEnd_5883164 := by exact prefixLift 5883164
  have htrace : WordTrace (prefixWord ++ tailWord_5883164) baseStart_5883164 baseEnd_5883164 := by
    simpa [prefixWord, tailWord_5883164, baseEnd_5883164] using wordTrace_append hprefix tailTrace_5883164
  have hstable : (prefixWord ++ tailWord_5883164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883164).length < 2 ^ (prefixWord ++ tailWord_5883164).sum := by decide
  have hdescent : baseEnd_5883164 < baseStart_5883164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883201 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 7]
def baseStart_5883201 : Nat := 118140960795 + 5883201 * 2 ^ 59
def prefixEnd_5883201 : Nat := 4983230072969 + 3 ^ 40 * 5883201 * 2
def baseEnd_5883201 : Nat := 335656655556904631414573

theorem tailTrace_5883201 : CollatzResearch.WordTrace tailWord_5883201 prefixEnd_5883201 335656655556904631414573 := by
  unfold tailWord_5883201
  simp only [CollatzResearch.WordTrace]
  refine ⟨214577968759175022582025457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143051979172783348388016971 214577968759175022582025457)
  ·
    refine ⟨160933476569381266936519093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214577968759175022582025457 160933476569381266936519093)
    ·
      refine ⟨15087513428379493775298665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160933476569381266936519093 15087513428379493775298665)
      ·
        refine ⟨11315635071284620331473999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15087513428379493775298665 11315635071284620331473999)
        ·
          refine ⟨16973452606926930497210999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11315635071284620331473999 16973452606926930497210999)
          ·
            refine ⟨25460178910390395745816499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16973452606926930497210999 25460178910390395745816499)
            ·
              refine ⟨38190268365585593618724749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25460178910390395745816499 38190268365585593618724749)
              ·
                refine ⟨14321350637094597607021781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38190268365585593618724749 14321350637094597607021781)
                ·
                  refine ⟨335656655556904631414573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14321350637094597607021781 335656655556904631414573)
                  ·
                    rfl

theorem cell23_5883201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 7].length) (baseStart_5883201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883201 prefixEnd_5883201 := by exact prefixLift 5883201
  have htrace : WordTrace (prefixWord ++ tailWord_5883201) baseStart_5883201 baseEnd_5883201 := by
    simpa [prefixWord, tailWord_5883201, baseEnd_5883201] using wordTrace_append hprefix tailTrace_5883201
  have hstable : (prefixWord ++ tailWord_5883201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883201).length < 2 ^ (prefixWord ++ tailWord_5883201).sum := by decide
  have hdescent : baseEnd_5883201 < baseStart_5883201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883206 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5883206 : Nat := 118140960795 + 5883206 * 2 ^ 59
def prefixEnd_5883206 : Nat := 4983230072969 + 3 ^ 40 * 5883206 * 2
def baseEnd_5883206 : Nat := 3020912467415414163168635

theorem tailTrace_5883206 : CollatzResearch.WordTrace tailWord_5883206 prefixEnd_5883206 3020912467415414163168635 := by
  unfold tailWord_5883206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6705567222629903388623671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143052100749437938957304981 6705567222629903388623671)
  ·
    refine ⟨10058350833944855082935507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6705567222629903388623671 10058350833944855082935507)
    ·
      refine ⟨15087526250917282624403261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10058350833944855082935507 15087526250917282624403261)
      ·
        refine ⟨5657822344093980984151223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15087526250917282624403261 5657822344093980984151223)
        ·
          refine ⟨8486733516140971476226835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657822344093980984151223 8486733516140971476226835)
          ·
            refine ⟨12730100274211457214340253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8486733516140971476226835 12730100274211457214340253)
            ·
              refine ⟨4773787602829296455377595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12730100274211457214340253 4773787602829296455377595)
              ·
                refine ⟨7160681404243944683066393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773787602829296455377595 7160681404243944683066393)
                ·
                  refine ⟨5370511053182958512299795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7160681404243944683066393 5370511053182958512299795)
                  ·
                    refine ⟨8055766579774437768449693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5370511053182958512299795 8055766579774437768449693)
                    ·
                      refine ⟨3020912467415414163168635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8055766579774437768449693 3020912467415414163168635)
                      ·
                        rfl

theorem cell23_5883206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5883206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883206 prefixEnd_5883206 := by exact prefixLift 5883206
  have htrace : WordTrace (prefixWord ++ tailWord_5883206) baseStart_5883206 baseEnd_5883206 := by
    simpa [prefixWord, tailWord_5883206, baseEnd_5883206] using wordTrace_append hprefix tailTrace_5883206
  have hstable : (prefixWord ++ tailWord_5883206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883206).length < 2 ^ (prefixWord ++ tailWord_5883206).sum := by decide
  have hdescent : baseEnd_5883206 < baseStart_5883206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883212 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 2, 2, 2]
def baseStart_5883212 : Nat := 118140960795 + 5883212 * 2 ^ 59
def prefixEnd_5883212 : Nat := 4983230072969 + 3 ^ 40 * 5883212 * 2
def baseEnd_5883212 : Nat := 3020915548299341139693607

theorem tailTrace_5883212 : CollatzResearch.WordTrace tailWord_5883212 prefixEnd_5883212 3020915548299341139693607 := by
  unfold tailWord_5883212
  simp only [CollatzResearch.WordTrace]
  refine ⟨107289184981067585730337945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143052246641423447640450593 107289184981067585730337945)
  ·
    refine ⟨80466888735800689297753459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107289184981067585730337945 80466888735800689297753459)
    ·
      refine ⟨120700333103701033946630189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80466888735800689297753459 120700333103701033946630189)
      ·
        refine ⟨45262624913887887729986321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120700333103701033946630189 45262624913887887729986321)
        ·
          refine ⟨33946968685415915797489741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45262624913887887729986321 33946968685415915797489741)
          ·
            refine ⟨12730113257030968424058653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33946968685415915797489741 12730113257030968424058653)
            ·
              refine ⟨4773792471386613159021995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12730113257030968424058653 4773792471386613159021995)
              ·
                refine ⟨7160688707079919738532993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773792471386613159021995 7160688707079919738532993)
                ·
                  refine ⟨5370516530309939803899745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7160688707079919738532993 5370516530309939803899745)
                  ·
                    refine ⟨4027887397732454852924809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5370516530309939803899745 4027887397732454852924809)
                    ·
                      refine ⟨3020915548299341139693607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027887397732454852924809 3020915548299341139693607)
                      ·
                        rfl

theorem cell23_5883212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_5883212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883212 prefixEnd_5883212 := by exact prefixLift 5883212
  have htrace : WordTrace (prefixWord ++ tailWord_5883212) baseStart_5883212 baseEnd_5883212 := by
    simpa [prefixWord, tailWord_5883212, baseEnd_5883212] using wordTrace_append hprefix tailTrace_5883212
  have hstable : (prefixWord ++ tailWord_5883212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883212).length < 2 ^ (prefixWord ++ tailWord_5883212).sum := by decide
  have hdescent : baseEnd_5883212 < baseStart_5883212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883214 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_5883214 : Nat := 118140960795 + 5883214 * 2 ^ 59
def prefixEnd_5883214 : Nat := 4983230072969 + 3 ^ 40 * 5883214 * 2
def baseEnd_5883214 : Nat := 1006972191753550043956199

theorem tailTrace_5883214 : CollatzResearch.WordTrace tailWord_5883214 prefixEnd_5883214 1006972191753550043956199 := by
  unfold tailWord_5883214
  simp only [CollatzResearch.WordTrace]
  refine ⟨26822305363515990725281087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143052295272085283868165797 26822305363515990725281087)
  ·
    refine ⟨40233458045273986087921631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26822305363515990725281087 40233458045273986087921631)
    ·
      refine ⟨60350187067910979131882447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40233458045273986087921631 60350187067910979131882447)
      ·
        refine ⟨90525280601866468697823671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60350187067910979131882447 90525280601866468697823671)
        ·
          refine ⟨135787920902799703046735507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90525280601866468697823671 135787920902799703046735507)
          ·
            refine ⟨203681881354199554570103261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135787920902799703046735507 203681881354199554570103261)
            ·
              refine ⟨76380705507824832963788723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203681881354199554570103261 76380705507824832963788723)
              ·
                refine ⟨114571058261737249445683085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76380705507824832963788723 114571058261737249445683085)
                ·
                  refine ⟨42964146848151468542131157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114571058261737249445683085 42964146848151468542131157)
                  ·
                    refine ⟨1006972191753550043956199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42964146848151468542131157 1006972191753550043956199)
                    ·
                      rfl

theorem cell23_5883214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_5883214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883214 prefixEnd_5883214 := by exact prefixLift 5883214
  have htrace : WordTrace (prefixWord ++ tailWord_5883214) baseStart_5883214 baseEnd_5883214 := by
    simpa [prefixWord, tailWord_5883214, baseEnd_5883214] using wordTrace_append hprefix tailTrace_5883214
  have hstable : (prefixWord ++ tailWord_5883214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883214).length < 2 ^ (prefixWord ++ tailWord_5883214).sum := by decide
  have hdescent : baseEnd_5883214 < baseStart_5883214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883264 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_5883264 : Nat := 118140960795 + 5883264 * 2 ^ 59
def prefixEnd_5883264 : Nat := 4983230072969 + 3 ^ 40 * 5883264 * 2
def baseEnd_5883264 : Nat := 3020942249293374936243367

theorem tailTrace_5883264 : CollatzResearch.WordTrace tailWord_5883264 prefixEnd_5883264 3020942249293374936243367 := by
  unfold tailWord_5883264
  simp only [CollatzResearch.WordTrace]
  refine ⟨107290133278973392170784423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143053511038631189561045897 107290133278973392170784423)
  ·
    refine ⟨160935199918460088256176635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107290133278973392170784423 160935199918460088256176635)
    ·
      refine ⟨241402799877690132384264953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160935199918460088256176635 241402799877690132384264953)
      ·
        refine ⟨181052099908267599288198715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241402799877690132384264953 181052099908267599288198715)
        ·
          refine ⟨271578149862401398932298073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181052099908267599288198715 271578149862401398932298073)
          ·
            refine ⟨203683612396801049199223555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271578149862401398932298073 203683612396801049199223555)
            ·
              refine ⟨305525418595201573798835333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203683612396801049199223555 305525418595201573798835333)
              ·
                refine ⟨57286015986600295087281625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305525418595201573798835333 57286015986600295087281625)
                ·
                  refine ⟨42964511989950221315461219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57286015986600295087281625 42964511989950221315461219)
                  ·
                    refine ⟨64446767984925331973191829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42964511989950221315461219 64446767984925331973191829)
                    ·
                      refine ⟨3020942249293374936243367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64446767984925331973191829 3020942249293374936243367)
                      ·
                        rfl

theorem cell23_5883264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_5883264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883264 prefixEnd_5883264 := by exact prefixLift 5883264
  have htrace : WordTrace (prefixWord ++ tailWord_5883264) baseStart_5883264 baseEnd_5883264 := by
    simpa [prefixWord, tailWord_5883264, baseEnd_5883264] using wordTrace_append hprefix tailTrace_5883264
  have hstable : (prefixWord ++ tailWord_5883264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883264).length < 2 ^ (prefixWord ++ tailWord_5883264).sum := by decide
  have hdescent : baseEnd_5883264 < baseStart_5883264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883328 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 4, 3, 2]
def baseStart_5883328 : Nat := 118140960795 + 5883328 * 2 ^ 59
def prefixEnd_5883328 : Nat := 4983230072969 + 3 ^ 40 * 5883328 * 2
def baseEnd_5883328 : Nat := 3020975112055262685843073

theorem tailTrace_5883328 : CollatzResearch.WordTrace tailWord_5883328 prefixEnd_5883328 3020975112055262685843073 := by
  unfold tailWord_5883328
  simp only [CollatzResearch.WordTrace]
  refine ⟨107291300414857461635949319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143055067219809948847932425 107291300414857461635949319)
  ·
    refine ⟨160936950622286192453923979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107291300414857461635949319 160936950622286192453923979)
    ·
      refine ⟨241405425933429288680885969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160936950622286192453923979 241405425933429288680885969)
      ·
        refine ⟨181054069450071966510664477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241405425933429288680885969 181054069450071966510664477)
        ·
          refine ⟨67895276043776987441499179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181054069450071966510664477 67895276043776987441499179)
          ·
            refine ⟨101842914065665481162248769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67895276043776987441499179 101842914065665481162248769)
            ·
              refine ⟨76382185549249110871686577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101842914065665481162248769 76382185549249110871686577)
              ·
                refine ⟨57286639161936833153764933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76382185549249110871686577 57286639161936833153764933)
                ·
                  refine ⟨10741244842863156216330925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57286639161936833153764933 10741244842863156216330925)
                  ·
                    refine ⟨4027966816073683581124097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10741244842863156216330925 4027966816073683581124097)
                    ·
                      refine ⟨3020975112055262685843073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027966816073683581124097 3020975112055262685843073)
                      ·
                        rfl

theorem cell23_5883328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_5883328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883328 prefixEnd_5883328 := by exact prefixLift 5883328
  have htrace : WordTrace (prefixWord ++ tailWord_5883328) baseStart_5883328 baseEnd_5883328 := by
    simpa [prefixWord, tailWord_5883328, baseEnd_5883328] using wordTrace_append hprefix tailTrace_5883328
  have hstable : (prefixWord ++ tailWord_5883328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883328).length < 2 ^ (prefixWord ++ tailWord_5883328).sum := by decide
  have hdescent : baseEnd_5883328 < baseStart_5883328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883368 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 4, 4]
def baseStart_5883368 : Nat := 118140960795 + 5883368 * 2 ^ 59
def prefixEnd_5883368 : Nat := 4983230072969 + 3 ^ 40 * 5883368 * 2
def baseEnd_5883368 : Nat := 1006998550427147509780963

theorem tailTrace_5883368 : CollatzResearch.WordTrace tailWord_5883368 prefixEnd_5883368 1006998550427147509780963 := by
  unfold tailWord_5883368
  simp only [CollatzResearch.WordTrace]
  refine ⟨107292029874785005051677379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143056039833046673402236505 107292029874785005051677379)
  ·
    refine ⟨160938044812177507577516069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107292029874785005051677379 160938044812177507577516069)
    ·
      refine ⟨30175883402283282670784263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160938044812177507577516069 30175883402283282670784263)
      ·
        refine ⟨45263825103424924006176395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30175883402283282670784263 45263825103424924006176395)
        ·
          refine ⟨67895737655137386009264593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45263825103424924006176395 67895737655137386009264593)
          ·
            refine ⟨50921803241353039506948445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67895737655137386009264593 50921803241353039506948445)
            ·
              refine ⟨19095676215507389815105667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50921803241353039506948445 19095676215507389815105667)
              ·
                refine ⟨28643514323261084722658501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19095676215507389815105667 28643514323261084722658501)
                ·
                  refine ⟨5370658935611453385498469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28643514323261084722658501 5370658935611453385498469)
                  ·
                    refine ⟨1006998550427147509780963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5370658935611453385498469 1006998550427147509780963)
                    ·
                      rfl

theorem cell23_5883368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_5883368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883368 prefixEnd_5883368 := by exact prefixLift 5883368
  have htrace : WordTrace (prefixWord ++ tailWord_5883368) baseStart_5883368 baseEnd_5883368 := by
    simpa [prefixWord, tailWord_5883368, baseEnd_5883368] using wordTrace_append hprefix tailTrace_5883368
  have hstable : (prefixWord ++ tailWord_5883368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883368).length < 2 ^ (prefixWord ++ tailWord_5883368).sum := by decide
  have hdescent : baseEnd_5883368 < baseStart_5883368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883375 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 3, 2, 2]
def baseStart_5883375 : Nat := 118140960795 + 5883375 * 2 ^ 59
def prefixEnd_5883375 : Nat := 4983230072969 + 3 ^ 40 * 5883375 * 2
def baseEnd_5883375 : Nat := 3020999245646024001955357

theorem tailTrace_5883375 : CollatzResearch.WordTrace tailWord_5883375 prefixEnd_5883375 3020999245646024001955357 := by
  unfold tailWord_5883375
  simp only [CollatzResearch.WordTrace]
  refine ⟨214584315060544650298859579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143056210040363100199239719 214584315060544650298859579)
  ·
    refine ⟨321876472590816975448289369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214584315060544650298859579 321876472590816975448289369)
    ·
      refine ⟨241407354443112731586217027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321876472590816975448289369 241407354443112731586217027)
      ·
        refine ⟨362111031664669097379325541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241407354443112731586217027 362111031664669097379325541)
        ·
          refine ⟨67895818437125455758623539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362111031664669097379325541 67895818437125455758623539)
          ·
            refine ⟨101843727655688183637935309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67895818437125455758623539 101843727655688183637935309)
            ·
              refine ⟨38191397870883068864225741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101843727655688183637935309 38191397870883068864225741)
              ·
                refine ⟨14321774201581150824084653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38191397870883068864225741 14321774201581150824084653)
                ·
                  refine ⟨5370665325592931559031745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14321774201581150824084653 5370665325592931559031745)
                  ·
                    refine ⟨4027998994194698669273809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5370665325592931559031745 4027998994194698669273809)
                    ·
                      refine ⟨3020999245646024001955357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4027998994194698669273809 3020999245646024001955357)
                      ·
                        rfl

theorem cell23_5883375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 2, 2].length) (baseStart_5883375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883375 prefixEnd_5883375 := by exact prefixLift 5883375
  have htrace : WordTrace (prefixWord ++ tailWord_5883375) baseStart_5883375 baseEnd_5883375 := by
    simpa [prefixWord, tailWord_5883375, baseEnd_5883375] using wordTrace_append hprefix tailTrace_5883375
  have hstable : (prefixWord ++ tailWord_5883375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883375).length < 2 ^ (prefixWord ++ tailWord_5883375).sum := by decide
  have hdescent : baseEnd_5883375 < baseStart_5883375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883378 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5883378 : Nat := 118140960795 + 5883378 * 2 ^ 59
def prefixEnd_5883378 : Nat := 4983230072969 + 3 ^ 40 * 5883378 * 2
def baseEnd_5883378 : Nat := 3021000786087987490217843

theorem tailTrace_5883378 : CollatzResearch.WordTrace tailWord_5883378 prefixEnd_5883378 3021000786087987490217843 := by
  unfold tailWord_5883378
  simp only [CollatzResearch.WordTrace]
  refine ⟨53646106119883445452804697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143056282986355854540812525 53646106119883445452804697)
  ·
    refine ⟨40234579589912584089603523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53646106119883445452804697 40234579589912584089603523)
    ·
      refine ⟨60351869384868876134405285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40234579589912584089603523 60351869384868876134405285)
      ·
        refine ⟨11315975509662914275200991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60351869384868876134405285 11315975509662914275200991)
        ·
          refine ⟨16973963264494371412801487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11315975509662914275200991 16973963264494371412801487)
          ·
            refine ⟨25460944896741557119202231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16973963264494371412801487 25460944896741557119202231)
            ·
              refine ⟨38191417345112335678803347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25460944896741557119202231 38191417345112335678803347)
              ·
                refine ⟨57287126017668503518205021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38191417345112335678803347 57287126017668503518205021)
                ·
                  refine ⟨21482672256625688819326883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57287126017668503518205021 21482672256625688819326883)
                  ·
                    refine ⟨32224008384938533228990325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21482672256625688819326883 32224008384938533228990325)
                    ·
                      refine ⟨3021000786087987490217843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32224008384938533228990325 3021000786087987490217843)
                      ·
                        rfl

theorem cell23_5883378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5883378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883378 prefixEnd_5883378 := by exact prefixLift 5883378
  have htrace : WordTrace (prefixWord ++ tailWord_5883378) baseStart_5883378 baseEnd_5883378 := by
    simpa [prefixWord, tailWord_5883378, baseEnd_5883378] using wordTrace_append hprefix tailTrace_5883378
  have hstable : (prefixWord ++ tailWord_5883378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883378).length < 2 ^ (prefixWord ++ tailWord_5883378).sum := by decide
  have hdescent : baseEnd_5883378 < baseStart_5883378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883388 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_5883388 : Nat := 118140960795 + 5883388 * 2 ^ 59
def prefixEnd_5883388 : Nat := 4983230072969 + 3 ^ 40 * 5883388 * 2
def baseEnd_5883388 : Nat := 3021005920894532451092797

theorem tailTrace_5883388 : CollatzResearch.WordTrace tailWord_5883388 prefixEnd_5883388 3021005920894532451092797 := by
  unfold tailWord_5883388
  simp only [CollatzResearch.WordTrace]
  refine ⟨107292394604748776759541409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143056526139665035679388545 107292394604748776759541409)
  ·
    refine ⟨80469295953561582569656057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107292394604748776759541409 80469295953561582569656057)
    ·
      refine ⟨60351971965171186927242043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80469295953561582569656057 60351971965171186927242043)
      ·
        refine ⟨90527957947756780390863065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60351971965171186927242043 90527957947756780390863065)
        ·
          refine ⟨67895968460817585293147299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90527957947756780390863065 67895968460817585293147299)
          ·
            refine ⟨101843952691226377939720949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67895968460817585293147299 101843952691226377939720949)
            ·
              refine ⟨9547870564802472931848839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101843952691226377939720949 9547870564802472931848839)
              ·
                refine ⟨14321805847203709397773259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9547870564802472931848839 14321805847203709397773259)
                ·
                  refine ⟨21482708770805564096659889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14321805847203709397773259 21482708770805564096659889)
                  ·
                    refine ⟨16112031578104173072494917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21482708770805564096659889 16112031578104173072494917)
                    ·
                      refine ⟨3021005920894532451092797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16112031578104173072494917 3021005920894532451092797)
                      ·
                        rfl

theorem cell23_5883388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_5883388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883388 prefixEnd_5883388 := by exact prefixLift 5883388
  have htrace : WordTrace (prefixWord ++ tailWord_5883388) baseStart_5883388 baseEnd_5883388 := by
    simpa [prefixWord, tailWord_5883388, baseEnd_5883388] using wordTrace_append hprefix tailTrace_5883388
  have hstable : (prefixWord ++ tailWord_5883388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883388).length < 2 ^ (prefixWord ++ tailWord_5883388).sum := by decide
  have hdescent : baseEnd_5883388 < baseStart_5883388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883412 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_5883412 : Nat := 118140960795 + 5883412 * 2 ^ 59
def prefixEnd_5883412 : Nat := 4983230072969 + 3 ^ 40 * 5883412 * 2
def baseEnd_5883412 : Nat := 3021018244430240357192687

theorem tailTrace_5883412 : CollatzResearch.WordTrace tailWord_5883412 prefixEnd_5883412 3021018244430240357192687 := by
  unfold tailWord_5883412
  simp only [CollatzResearch.WordTrace]
  refine ⟨107292832280705302808978245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143057109707607070411970993 107292832280705302808978245)
  ·
    refine ⟨20117406052632244276683421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107292832280705302808978245 20117406052632244276683421)
    ·
      refine ⟨7544027269737091603756283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20117406052632244276683421 7544027269737091603756283)
      ·
        refine ⟨11316040904605637405634425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7544027269737091603756283 11316040904605637405634425)
        ·
          refine ⟨8487030678454228054225819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11316040904605637405634425 8487030678454228054225819)
          ·
            refine ⟨12730546017681342081338729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487030678454228054225819 12730546017681342081338729)
            ·
              refine ⟨9547909513261006561004047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12730546017681342081338729 9547909513261006561004047)
              ·
                refine ⟨14321864269891509841506071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9547909513261006561004047 14321864269891509841506071)
                ·
                  refine ⟨21482796404837264762259107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14321864269891509841506071 21482796404837264762259107)
                  ·
                    refine ⟨32224194607255897143388661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21482796404837264762259107 32224194607255897143388661)
                    ·
                      refine ⟨3021018244430240357192687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32224194607255897143388661 3021018244430240357192687)
                      ·
                        rfl

theorem cell23_5883412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_5883412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883412 prefixEnd_5883412 := by exact prefixLift 5883412
  have htrace : WordTrace (prefixWord ++ tailWord_5883412) baseStart_5883412 baseEnd_5883412 := by
    simpa [prefixWord, tailWord_5883412, baseEnd_5883412] using wordTrace_append hprefix tailTrace_5883412
  have hstable : (prefixWord ++ tailWord_5883412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883412).length < 2 ^ (prefixWord ++ tailWord_5883412).sum := by decide
  have hdescent : baseEnd_5883412 < baseStart_5883412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883425 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_5883425 : Nat := 118140960795 + 5883425 * 2 ^ 59
def prefixEnd_5883425 : Nat := 4983230072969 + 3 ^ 40 * 5883425 * 2
def baseEnd_5883425 : Nat := 3021024919678748806330127

theorem tailTrace_5883425 : CollatzResearch.WordTrace tailWord_5883425 prefixEnd_5883425 3021024919678748806330127 := by
  unfold tailWord_5883425
  simp only [CollatzResearch.WordTrace]
  refine ⟨214586138710363508838179729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143057425806909005892119819 214586138710363508838179729)
  ·
    refine ⟨160939604032772631628634797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214586138710363508838179729 160939604032772631628634797)
    ·
      refine ⟨60352351512289736860738049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160939604032772631628634797 60352351512289736860738049)
      ·
        refine ⟨45264263634217302645553537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60352351512289736860738049 45264263634217302645553537)
        ·
          refine ⟨33948197725662976984165153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45264263634217302645553537 33948197725662976984165153)
          ·
            refine ⟨25461148294247232738123865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33948197725662976984165153 25461148294247232738123865)
            ·
              refine ⟨19095861220685424553592899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25461148294247232738123865 19095861220685424553592899)
              ·
                refine ⟨28643791831028136830389349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19095861220685424553592899 28643791831028136830389349)
                ·
                  refine ⟨5370710968317775655698003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28643791831028136830389349 5370710968317775655698003)
                  ·
                    refine ⟨8056066452476663483547005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5370710968317775655698003 8056066452476663483547005)
                    ·
                      refine ⟨3021024919678748806330127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8056066452476663483547005 3021024919678748806330127)
                      ·
                        rfl

theorem cell23_5883425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_5883425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883425 prefixEnd_5883425 := by exact prefixLift 5883425
  have htrace : WordTrace (prefixWord ++ tailWord_5883425) baseStart_5883425 baseEnd_5883425 := by
    simpa [prefixWord, tailWord_5883425, baseEnd_5883425] using wordTrace_append hprefix tailTrace_5883425
  have hstable : (prefixWord ++ tailWord_5883425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883425).length < 2 ^ (prefixWord ++ tailWord_5883425).sum := by decide
  have hdescent : baseEnd_5883425 < baseStart_5883425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883441 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 1, 8]
def baseStart_5883441 : Nat := 118140960795 + 5883441 * 2 ^ 59
def prefixEnd_5883441 : Nat := 4983230072969 + 3 ^ 40 * 5883441 * 2
def baseEnd_5883441 : Nat := 1007011045123073581243351

theorem tailTrace_5883441 : CollatzResearch.WordTrace tailWord_5883441 prefixEnd_5883441 1007011045123073581243351 := by
  unfold tailWord_5883441
  simp only [CollatzResearch.WordTrace]
  refine ⟨214586722278305543570762177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143057814852203695713841451 214586722278305543570762177)
  ·
    refine ⟨160940041708729157678071633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214586722278305543570762177 160940041708729157678071633)
    ·
      refine ⟨120705031281546868258553725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160940041708729157678071633 120705031281546868258553725)
      ·
        refine ⟨45264386730580075596957647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120705031281546868258553725 45264386730580075596957647)
        ·
          refine ⟨67896580095870113395436471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45264386730580075596957647 67896580095870113395436471)
          ·
            refine ⟨101844870143805170093154707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67896580095870113395436471 101844870143805170093154707)
            ·
              refine ⟨152767305215707755139732061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101844870143805170093154707 152767305215707755139732061)
              ·
                refine ⟨57287739455890408177399523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152767305215707755139732061 57287739455890408177399523)
                ·
                  refine ⟨85931609183835612266099285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57287739455890408177399523 85931609183835612266099285)
                  ·
                    refine ⟨1007011045123073581243351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85931609183835612266099285 1007011045123073581243351)
                    ·
                      rfl

theorem cell23_5883441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_5883441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883441 prefixEnd_5883441 := by exact prefixLift 5883441
  have htrace : WordTrace (prefixWord ++ tailWord_5883441) baseStart_5883441 baseEnd_5883441 := by
    simpa [prefixWord, tailWord_5883441, baseEnd_5883441] using wordTrace_append hprefix tailTrace_5883441
  have hstable : (prefixWord ++ tailWord_5883441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883441).length < 2 ^ (prefixWord ++ tailWord_5883441).sum := by decide
  have hdescent : baseEnd_5883441 < baseStart_5883441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883446 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_5883446 : Nat := 118140960795 + 5883446 * 2 ^ 59
def prefixEnd_5883446 : Nat := 4983230072969 + 3 ^ 40 * 5883446 * 2
def baseEnd_5883446 : Nat := 3021035702772493224167531

theorem tailTrace_5883446 : CollatzResearch.WordTrace tailWord_5883446 prefixEnd_5883446 3021035702772493224167531 := by
  unfold tailWord_5883446
  simp only [CollatzResearch.WordTrace]
  refine ⟨13411681540205464339043387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143057936428858286283129461 13411681540205464339043387)
  ·
    refine ⟨20117522310308196508565081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13411681540205464339043387 20117522310308196508565081)
    ·
      refine ⟨15088141732731147381423811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20117522310308196508565081 15088141732731147381423811)
      ·
        refine ⟨22632212599096721072135717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15088141732731147381423811 22632212599096721072135717)
        ·
          refine ⟨4243539862330635201025447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22632212599096721072135717 4243539862330635201025447)
          ·
            refine ⟨6365309793495952801538171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243539862330635201025447 6365309793495952801538171)
            ·
              refine ⟨9547964690243929202307257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365309793495952801538171 9547964690243929202307257)
              ·
                refine ⟨7160973517682946901730443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9547964690243929202307257 7160973517682946901730443)
                ·
                  refine ⟨10741460276524420352595665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7160973517682946901730443 10741460276524420352595665)
                  ·
                    refine ⟨8056095207393315264446749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10741460276524420352595665 8056095207393315264446749)
                    ·
                      refine ⟨3021035702772493224167531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8056095207393315264446749 3021035702772493224167531)
                      ·
                        rfl

theorem cell23_5883446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_5883446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883446 prefixEnd_5883446 := by exact prefixLift 5883446
  have htrace : WordTrace (prefixWord ++ tailWord_5883446) baseStart_5883446 baseEnd_5883446 := by
    simpa [prefixWord, tailWord_5883446, baseEnd_5883446] using wordTrace_append hprefix tailTrace_5883446
  have hstable : (prefixWord ++ tailWord_5883446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883446).length < 2 ^ (prefixWord ++ tailWord_5883446).sum := by decide
  have hdescent : baseEnd_5883446 < baseStart_5883446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883452 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_5883452 : Nat := 118140960795 + 5883452 * 2 ^ 59
def prefixEnd_5883452 : Nat := 4983230072969 + 3 ^ 40 * 5883452 * 2
def baseEnd_5883452 : Nat := 3021038783656420200692503

theorem tailTrace_5883452 : CollatzResearch.WordTrace tailWord_5883452 prefixEnd_5883452 3021038783656420200692503 := by
  unfold tailWord_5883452
  simp only [CollatzResearch.WordTrace]
  refine ⟨107293561740632846224706305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143058082320843794966275073 107293561740632846224706305)
  ·
    refine ⟨80470171305474634668529729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107293561740632846224706305 80470171305474634668529729)
    ·
      refine ⟨60352628479105976001397297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80470171305474634668529729 60352628479105976001397297)
      ·
        refine ⟨45264471359329482001047973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60352628479105976001397297 45264471359329482001047973)
        ·
          refine ⟨8487088379874277875196495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45264471359329482001047973 8487088379874277875196495)
          ·
            refine ⟨12730632569811416812794743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487088379874277875196495 12730632569811416812794743)
            ·
              refine ⟨19095948854717125219192115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12730632569811416812794743 19095948854717125219192115)
              ·
                refine ⟨28643923282075687828788173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19095948854717125219192115 28643923282075687828788173)
                ·
                  refine ⟨10741471230778382935795565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28643923282075687828788173 10741471230778382935795565)
                  ·
                    refine ⟨4028051711541893600923337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10741471230778382935795565 4028051711541893600923337)
                    ·
                      refine ⟨3021038783656420200692503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028051711541893600923337 3021038783656420200692503)
                      ·
                        rfl

theorem cell23_5883452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_5883452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883452 prefixEnd_5883452 := by exact prefixLift 5883452
  have htrace : WordTrace (prefixWord ++ tailWord_5883452) baseStart_5883452 baseEnd_5883452 := by
    simpa [prefixWord, tailWord_5883452, baseEnd_5883452] using wordTrace_append hprefix tailTrace_5883452
  have hstable : (prefixWord ++ tailWord_5883452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883452).length < 2 ^ (prefixWord ++ tailWord_5883452).sum := by decide
  have hdescent : baseEnd_5883452 < baseStart_5883452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883465 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 6, 2, 2]
def baseStart_5883465 : Nat := 118140960795 + 5883465 * 2 ^ 59
def prefixEnd_5883465 : Nat := 4983230072969 + 3 ^ 40 * 5883465 * 2
def baseEnd_5883465 : Nat := 3021045458904928649829943

theorem tailTrace_5883465 : CollatzResearch.WordTrace tailWord_5883465 prefixEnd_5883465 3021045458904928649829943 := by
  unfold tailWord_5883465
  simp only [CollatzResearch.WordTrace]
  refine ⟨214587597630218595669635849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143058398420145730446423899 214587597630218595669635849)
  ·
    refine ⟨160940698222663946752226887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214587597630218595669635849 160940698222663946752226887)
    ·
      refine ⟨241411047333995920128340331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160940698222663946752226887 241411047333995920128340331)
      ·
        refine ⟨362116571000993880192510497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241411047333995920128340331 362116571000993880192510497)
        ·
          refine ⟨271587428250745410144382873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362116571000993880192510497 271587428250745410144382873)
          ·
            refine ⟨203690571188059057608287155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271587428250745410144382873 203690571188059057608287155)
            ·
              refine ⟨305535856782088586412430733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203690571188059057608287155 305535856782088586412430733)
              ·
                refine ⟨114575946293283219904661525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305535856782088586412430733 114575946293283219904661525)
                ·
                  refine ⟨5370747482497650933031009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114575946293283219904661525 5370747482497650933031009)
                  ·
                    refine ⟨4028060611873238199773257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5370747482497650933031009 4028060611873238199773257)
                    ·
                      refine ⟨3021045458904928649829943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028060611873238199773257 3021045458904928649829943)
                      ·
                        rfl

theorem cell23_5883465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 2, 2].length) (baseStart_5883465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883465 prefixEnd_5883465 := by exact prefixLift 5883465
  have htrace : WordTrace (prefixWord ++ tailWord_5883465) baseStart_5883465 baseEnd_5883465 := by
    simpa [prefixWord, tailWord_5883465, baseEnd_5883465] using wordTrace_append hprefix tailTrace_5883465
  have hstable : (prefixWord ++ tailWord_5883465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883465).length < 2 ^ (prefixWord ++ tailWord_5883465).sum := by decide
  have hdescent : baseEnd_5883465 < baseStart_5883465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883468 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_5883468 : Nat := 118140960795 + 5883468 * 2 ^ 59
def prefixEnd_5883468 : Nat := 4983230072969 + 3 ^ 40 * 5883468 * 2
def baseEnd_5883468 : Nat := 3021046999346892138092429

theorem tailTrace_5883468 : CollatzResearch.WordTrace tailWord_5883468 prefixEnd_5883468 3021046999346892138092429 := by
  unfold tailWord_5883468
  simp only [CollatzResearch.WordTrace]
  refine ⟨107293853524603863590997529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143058471366138484787996705 107293853524603863590997529)
  ·
    refine ⟨80470390143452897693248147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107293853524603863590997529 80470390143452897693248147)
    ·
      refine ⟨120705585215179346539872221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80470390143452897693248147 120705585215179346539872221)
      ·
        refine ⟨45264594455692254952452083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120705585215179346539872221 45264594455692254952452083)
        ·
          refine ⟨67896891683538382428678125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45264594455692254952452083 67896891683538382428678125)
          ·
            refine ⟨25461334381326893410754297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67896891683538382428678125 25461334381326893410754297)
            ·
              refine ⟨19096000785995170058065723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25461334381326893410754297 19096000785995170058065723)
              ·
                refine ⟨28644001178992755087098585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19096000785995170058065723 28644001178992755087098585)
                ·
                  refine ⟨21483000884244566315323939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28644001178992755087098585 21483000884244566315323939)
                  ·
                    refine ⟨32224501326366849472985909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21483000884244566315323939 32224501326366849472985909)
                    ·
                      refine ⟨3021046999346892138092429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32224501326366849472985909 3021046999346892138092429)
                      ·
                        rfl

theorem cell23_5883468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_5883468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883468 prefixEnd_5883468 := by exact prefixLift 5883468
  have htrace : WordTrace (prefixWord ++ tailWord_5883468) baseStart_5883468 baseEnd_5883468 := by
    simpa [prefixWord, tailWord_5883468, baseEnd_5883468] using wordTrace_append hprefix tailTrace_5883468
  have hstable : (prefixWord ++ tailWord_5883468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883468).length < 2 ^ (prefixWord ++ tailWord_5883468).sum := by decide
  have hdescent : baseEnd_5883468 < baseStart_5883468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883481 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_5883481 : Nat := 118140960795 + 5883481 * 2 ^ 59
def prefixEnd_5883481 : Nat := 4983230072969 + 3 ^ 40 * 5883481 * 2
def baseEnd_5883481 : Nat := 3021053674595400587229869

theorem tailTrace_5883481 : CollatzResearch.WordTrace tailWord_5883481 prefixEnd_5883481 3021053674595400587229869 := by
  unfold tailWord_5883481
  simp only [CollatzResearch.WordTrace]
  refine ⟨214588181198160630402218297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143058787465440420268145531 214588181198160630402218297)
  ·
    refine ⟨160941135898620472801663723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214588181198160630402218297 160941135898620472801663723)
    ·
      refine ⟨241411703847930709202495585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160941135898620472801663723 241411703847930709202495585)
      ·
        refine ⟨181058777885948031901871689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241411703847930709202495585 181058777885948031901871689)
        ·
          refine ⟨135794083414461023926403767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181058777885948031901871689 135794083414461023926403767)
          ·
            refine ⟨203691125121691535889605651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135794083414461023926403767 203691125121691535889605651)
            ·
              refine ⟨305536687682537303834408477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203691125121691535889605651 305536687682537303834408477)
              ·
                refine ⟨114576257880951488937903179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305536687682537303834408477 114576257880951488937903179)
                ·
                  refine ⟨171864386821427233406854769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114576257880951488937903179 171864386821427233406854769)
                  ·
                    refine ⟨128898290116070425055141077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 171864386821427233406854769 128898290116070425055141077)
                    ·
                      refine ⟨3021053674595400587229869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128898290116070425055141077 3021053674595400587229869)
                      ·
                        rfl

theorem cell23_5883481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_5883481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883481 prefixEnd_5883481 := by exact prefixLift 5883481
  have htrace : WordTrace (prefixWord ++ tailWord_5883481) baseStart_5883481 baseEnd_5883481 := by
    simpa [prefixWord, tailWord_5883481, baseEnd_5883481] using wordTrace_append hprefix tailTrace_5883481
  have hstable : (prefixWord ++ tailWord_5883481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883481).length < 2 ^ (prefixWord ++ tailWord_5883481).sum := by decide
  have hdescent : baseEnd_5883481 < baseStart_5883481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883555 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 2, 4, 2]
def baseStart_5883555 : Nat := 118140960795 + 5883555 * 2 ^ 59
def prefixEnd_5883555 : Nat := 4983230072969 + 3 ^ 40 * 5883555 * 2
def baseEnd_5883555 : Nat := 3021091672163833297704529

theorem tailTrace_5883555 : CollatzResearch.WordTrace tailWord_5883555 prefixEnd_5883555 3021091672163833297704529 := by
  unfold tailWord_5883555
  simp only [CollatzResearch.WordTrace]
  refine ⟨214590880199892541040412119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143060586799928360693608079 214590880199892541040412119)
  ·
    refine ⟨321886320299838811560618179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214590880199892541040412119 321886320299838811560618179)
    ·
      refine ⟨482829480449758217340927269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321886320299838811560618179 482829480449758217340927269)
      ·
        refine ⟨90530527584329665751423863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 482829480449758217340927269 90530527584329665751423863)
        ·
          refine ⟨135795791376494498627135795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90530527584329665751423863 135795791376494498627135795)
          ·
            refine ⟨203693687064741747940703693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135795791376494498627135795 203693687064741747940703693)
            ·
              refine ⟨76385132649278155477763885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203693687064741747940703693 76385132649278155477763885)
              ·
                refine ⟨28644424743479308304161457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76385132649278155477763885 28644424743479308304161457)
                ·
                  refine ⟨21483318557609481228121093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28644424743479308304161457 21483318557609481228121093)
                  ·
                    refine ⟨4028122229551777730272705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21483318557609481228121093 4028122229551777730272705)
                    ·
                      refine ⟨3021091672163833297704529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028122229551777730272705 3021091672163833297704529)
                      ·
                        rfl

theorem cell23_5883555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_5883555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883555 prefixEnd_5883555 := by exact prefixLift 5883555
  have htrace : WordTrace (prefixWord ++ tailWord_5883555) baseStart_5883555 baseEnd_5883555 := by
    simpa [prefixWord, tailWord_5883555, baseEnd_5883555] using wordTrace_append hprefix tailTrace_5883555
  have hstable : (prefixWord ++ tailWord_5883555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883555).length < 2 ^ (prefixWord ++ tailWord_5883555).sum := by decide
  have hdescent : baseEnd_5883555 < baseStart_5883555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883575 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_5883575 : Nat := 118140960795 + 5883575 * 2 ^ 59
def prefixEnd_5883575 : Nat := 4983230072969 + 3 ^ 40 * 5883575 * 2
def baseEnd_5883575 : Nat := 3021101941776923219454437

theorem tailTrace_5883575 : CollatzResearch.WordTrace tailWord_5883575 prefixEnd_5883575 3021101941776923219454437 := by
  unfold tailWord_5883575
  simp only [CollatzResearch.WordTrace]
  refine ⟨214591609659820084456140179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143061073106546722970760119 214591609659820084456140179)
  ·
    refine ⟨321887414489730126684210269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214591609659820084456140179 321887414489730126684210269)
    ·
      refine ⟨120707780433648797506578851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321887414489730126684210269 120707780433648797506578851)
      ·
        refine ⟨181061670650473196259868277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120707780433648797506578851 181061670650473196259868277)
        ·
          refine ⟨16974531623481862149362651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181061670650473196259868277 16974531623481862149362651)
          ·
            refine ⟨25461797435222793224043977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16974531623481862149362651 25461797435222793224043977)
            ·
              refine ⟨19096348076417094918032983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25461797435222793224043977 19096348076417094918032983)
              ·
                refine ⟨28644522114625642377049475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19096348076417094918032983 28644522114625642377049475)
                ·
                  refine ⟨42966783171938463565574213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28644522114625642377049475 42966783171938463565574213)
                  ·
                    refine ⟨8056271844738461918545165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42966783171938463565574213 8056271844738461918545165)
                    ·
                      refine ⟨3021101941776923219454437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8056271844738461918545165 3021101941776923219454437)
                      ·
                        rfl

theorem cell23_5883575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_5883575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883575 prefixEnd_5883575 := by exact prefixLift 5883575
  have htrace : WordTrace (prefixWord ++ tailWord_5883575) baseStart_5883575 baseEnd_5883575 := by
    simpa [prefixWord, tailWord_5883575, baseEnd_5883575] using wordTrace_append hprefix tailTrace_5883575
  have hstable : (prefixWord ++ tailWord_5883575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883575).length < 2 ^ (prefixWord ++ tailWord_5883575).sum := by decide
  have hdescent : baseEnd_5883575 < baseStart_5883575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883578 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 8]
def baseStart_5883578 : Nat := 118140960795 + 5883578 * 2 ^ 59
def prefixEnd_5883578 : Nat := 4983230072969 + 3 ^ 40 * 5883578 * 2
def baseEnd_5883578 : Nat := 335678164690987411968547

theorem tailTrace_5883578 : CollatzResearch.WordTrace tailWord_5883578 prefixEnd_5883578 335678164690987411968547 := by
  unfold tailWord_5883578
  simp only [CollatzResearch.WordTrace]
  refine ⟨53647929769702303992124847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143061146052539477312332925 53647929769702303992124847)
  ·
    refine ⟨80471894654553455988187271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53647929769702303992124847 80471894654553455988187271)
    ·
      refine ⟨120707841981830183982280907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80471894654553455988187271 120707841981830183982280907)
      ·
        refine ⟨181061762972745275973421361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120707841981830183982280907 181061762972745275973421361)
        ·
          refine ⟨135796322229558956980066021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181061762972745275973421361 135796322229558956980066021)
          ·
            refine ⟨25461810418042304433762379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135796322229558956980066021 25461810418042304433762379)
            ·
              refine ⟨38192715627063456650643569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25461810418042304433762379 38192715627063456650643569)
              ·
                refine ⟨28644536720297592487982677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38192715627063456650643569 28644536720297592487982677)
                ·
                  refine ⟨335678164690987411968547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28644536720297592487982677 335678164690987411968547)
                  ·
                    rfl

theorem cell23_5883578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_5883578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883578 prefixEnd_5883578 := by exact prefixLift 5883578
  have htrace : WordTrace (prefixWord ++ tailWord_5883578) baseStart_5883578 baseEnd_5883578 := by
    simpa [prefixWord, tailWord_5883578, baseEnd_5883578] using wordTrace_append hprefix tailTrace_5883578
  have hstable : (prefixWord ++ tailWord_5883578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883578).length < 2 ^ (prefixWord ++ tailWord_5883578).sum := by decide
  have hdescent : baseEnd_5883578 < baseStart_5883578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883586 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_5883586 : Nat := 118140960795 + 5883586 * 2 ^ 59
def prefixEnd_5883586 : Nat := 4983230072969 + 3 ^ 40 * 5883586 * 2
def baseEnd_5883586 : Nat := 1007035863354707558805629

theorem tailTrace_5883586 : CollatzResearch.WordTrace tailWord_5883586 prefixEnd_5883586 1007035863354707558805629 := by
  unfold tailWord_5883586
  simp only [CollatzResearch.WordTrace]
  refine ⟨53648002715695058333697653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143061340575186822223193741 53648002715695058333697653)
  ·
    refine ⟨5029500254596411718784155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53648002715695058333697653 5029500254596411718784155)
    ·
      refine ⟨7544250381894617578176233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5029500254596411718784155 7544250381894617578176233)
      ·
        refine ⟨5658187786420963183632175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7544250381894617578176233 5658187786420963183632175)
        ·
          refine ⟨8487281679631444775448263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658187786420963183632175 8487281679631444775448263)
          ·
            refine ⟨12730922519447167163172395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487281679631444775448263 12730922519447167163172395)
            ·
              refine ⟨19096383779170750744758593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12730922519447167163172395 19096383779170750744758593)
              ·
                refine ⟨14322287834378063058568945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19096383779170750744758593 14322287834378063058568945)
                ·
                  refine ⟨10741715875783547293926709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14322287834378063058568945 10741715875783547293926709)
                  ·
                    refine ⟨1007035863354707558805629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10741715875783547293926709 1007035863354707558805629)
                    ·
                      rfl

theorem cell23_5883586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_5883586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883586 prefixEnd_5883586 := by exact prefixLift 5883586
  have htrace : WordTrace (prefixWord ++ tailWord_5883586) baseStart_5883586 baseEnd_5883586 := by
    simpa [prefixWord, tailWord_5883586, baseEnd_5883586] using wordTrace_append hprefix tailTrace_5883586
  have hstable : (prefixWord ++ tailWord_5883586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883586).length < 2 ^ (prefixWord ++ tailWord_5883586).sum := by decide
  have hdescent : baseEnd_5883586 < baseStart_5883586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883672 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 2, 4]
def baseStart_5883672 : Nat := 118140960795 + 5883672 * 2 ^ 59
def prefixEnd_5883672 : Nat := 4983230072969 + 3 ^ 40 * 5883672 * 2
def baseEnd_5883672 : Nat := 1007050583133469779980497

theorem tailTrace_5883672 : CollatzResearch.WordTrace tailWord_5883672 prefixEnd_5883672 1007050583133469779980497 := by
  unfold tailWord_5883672
  simp only [CollatzResearch.WordTrace]
  refine ⟨107297573770234335011210635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143063431693645780014947513 107297573770234335011210635)
  ·
    refine ⟨160946360655351502516815953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107297573770234335011210635 160946360655351502516815953)
    ·
      refine ⟨120709770491513626887611965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160946360655351502516815953 120709770491513626887611965)
      ·
        refine ⟨45266163934317610082854487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120709770491513626887611965 45266163934317610082854487)
        ·
          refine ⟨67899245901476415124281731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45266163934317610082854487 67899245901476415124281731)
          ·
            refine ⟨101848868852214622686422597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67899245901476415124281731 101848868852214622686422597)
            ·
              refine ⟨19096662909790241753704237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101848868852214622686422597 19096662909790241753704237)
              ·
                refine ⟨7161248591171340657639089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19096662909790241753704237 7161248591171340657639089)
                ·
                  refine ⟨5370936443378505493229317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7161248591171340657639089 5370936443378505493229317)
                  ·
                    refine ⟨1007050583133469779980497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5370936443378505493229317 1007050583133469779980497)
                    ·
                      rfl

theorem cell23_5883672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_5883672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883672 prefixEnd_5883672 := by exact prefixLift 5883672
  have htrace : WordTrace (prefixWord ++ tailWord_5883672) baseStart_5883672 baseEnd_5883672 := by
    simpa [prefixWord, tailWord_5883672, baseEnd_5883672] using wordTrace_append hprefix tailTrace_5883672
  have hstable : (prefixWord ++ tailWord_5883672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883672).length < 2 ^ (prefixWord ++ tailWord_5883672).sum := by decide
  have hdescent : baseEnd_5883672 < baseStart_5883672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883679 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 3, 2, 2]
def baseStart_5883679 : Nat := 118140960795 + 5883679 * 2 ^ 59
def prefixEnd_5883679 : Nat := 4983230072969 + 3 ^ 40 * 5883679 * 2
def baseEnd_5883679 : Nat := 3021155343764990812553959

theorem tailTrace_5883679 : CollatzResearch.WordTrace tailWord_5883679 prefixEnd_5883679 3021155343764990812553959 := by
  unfold tailWord_5883679
  simp only [CollatzResearch.WordTrace]
  refine ⟨214595402851443310217926091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143063601900962206811950727 214595402851443310217926091)
  ·
    refine ⟨321893104277164965326889137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214595402851443310217926091 321893104277164965326889137)
    ·
      refine ⟨241419828207873723995166853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321893104277164965326889137 241419828207873723995166853)
      ·
        refine ⟨45266217788976323249093785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241419828207873723995166853 45266217788976323249093785)
        ·
          refine ⟨33949663341732242436820339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45266217788976323249093785 33949663341732242436820339)
          ·
            refine ⟨50924495012598363655230509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33949663341732242436820339 50924495012598363655230509)
            ·
              refine ⟨19096685629724386370711441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50924495012598363655230509 19096685629724386370711441)
              ·
                refine ⟨14322514222293289778033581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19096685629724386370711441 14322514222293289778033581)
                ·
                  refine ⟨5370942833359983666762593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14322514222293289778033581 5370942833359983666762593)
                  ·
                    refine ⟨4028207125019987750071945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5370942833359983666762593 4028207125019987750071945)
                    ·
                      refine ⟨3021155343764990812553959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028207125019987750071945 3021155343764990812553959)
                      ·
                        rfl

theorem cell23_5883679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_5883679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883679 prefixEnd_5883679 := by exact prefixLift 5883679
  have htrace : WordTrace (prefixWord ++ tailWord_5883679) baseStart_5883679 baseEnd_5883679 := by
    simpa [prefixWord, tailWord_5883679, baseEnd_5883679] using wordTrace_append hprefix tailTrace_5883679
  have hstable : (prefixWord ++ tailWord_5883679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883679).length < 2 ^ (prefixWord ++ tailWord_5883679).sum := by decide
  have hdescent : baseEnd_5883679 < baseStart_5883679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883682 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_5883682 : Nat := 118140960795 + 5883682 * 2 ^ 59
def prefixEnd_5883682 : Nat := 4983230072969 + 3 ^ 40 * 5883682 * 2
def baseEnd_5883682 : Nat := 3021156884206954300816445

theorem tailTrace_5883682 : CollatzResearch.WordTrace tailWord_5883682 prefixEnd_5883682 3021156884206954300816445 := by
  unfold tailWord_5883682
  simp only [CollatzResearch.WordTrace]
  refine ⟨53648878067608110432571325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143063674846954961153523533 53648878067608110432571325)
  ·
    refine ⟨20118329275353041412214247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53648878067608110432571325 20118329275353041412214247)
    ·
      refine ⟨30177493913029562118321371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20118329275353041412214247 30177493913029562118321371)
      ·
        refine ⟨45266240869544343177482057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30177493913029562118321371 45266240869544343177482057)
        ·
          refine ⟨33949680652158257383111543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45266240869544343177482057 33949680652158257383111543)
          ·
            refine ⟨50924520978237386074667315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33949680652158257383111543 50924520978237386074667315)
            ·
              refine ⟨76386781467356079112000973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50924520978237386074667315 76386781467356079112000973)
              ·
                refine ⟨28645043050258529667000365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76386781467356079112000973 28645043050258529667000365)
                ·
                  refine ⟨10741891143846948625125137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28645043050258529667000365 10741891143846948625125137)
                  ·
                    refine ⟨8056418357885211468843853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10741891143846948625125137 8056418357885211468843853)
                    ·
                      refine ⟨3021156884206954300816445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8056418357885211468843853 3021156884206954300816445)
                      ·
                        rfl

theorem cell23_5883682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_5883682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883682 prefixEnd_5883682 := by exact prefixLift 5883682
  have htrace : WordTrace (prefixWord ++ tailWord_5883682) baseStart_5883682 baseEnd_5883682 := by
    simpa [prefixWord, tailWord_5883682, baseEnd_5883682] using wordTrace_append hprefix tailTrace_5883682
  have hstable : (prefixWord ++ tailWord_5883682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883682).length < 2 ^ (prefixWord ++ tailWord_5883682).sum := by decide
  have hdescent : baseEnd_5883682 < baseStart_5883682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883699 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 3]
def baseStart_5883699 : Nat := 118140960795 + 5883699 * 2 ^ 59
def prefixEnd_5883699 : Nat := 4983230072969 + 3 ^ 40 * 5883699 * 2
def baseEnd_5883699 : Nat := 3021165613378080734303867

theorem tailTrace_5883699 : CollatzResearch.WordTrace tailWord_5883699 prefixEnd_5883699 3021165613378080734303867 := by
  unfold tailWord_5883699
  simp only [CollatzResearch.WordTrace]
  refine ⟨214596132311370853633654151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143064088207580569089102767 214596132311370853633654151)
  ·
    refine ⟨321894198467056280450481227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214596132311370853633654151 321894198467056280450481227)
    ·
      refine ⟨482841297700584420675721841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321894198467056280450481227 482841297700584420675721841)
      ·
        refine ⟨362130973275438315506791381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482841297700584420675721841 362130973275438315506791381)
        ·
          refine ⟨8487444686143085519690423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 362130973275438315506791381 8487444686143085519690423)
          ·
            refine ⟨12731167029214628279535635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487444686143085519690423 12731167029214628279535635)
            ·
              refine ⟨19096750543821942419303453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12731167029214628279535635 19096750543821942419303453)
              ·
                refine ⟨7161281453933228407238795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19096750543821942419303453 7161281453933228407238795)
                ·
                  refine ⟨10741922180899842610858193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7161281453933228407238795 10741922180899842610858193)
                  ·
                    refine ⟨8056441635674881958143645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10741922180899842610858193 8056441635674881958143645)
                    ·
                      refine ⟨3021165613378080734303867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8056441635674881958143645 3021165613378080734303867)
                      ·
                        rfl

theorem cell23_5883699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 3].length) (baseStart_5883699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883699 prefixEnd_5883699 := by exact prefixLift 5883699
  have htrace : WordTrace (prefixWord ++ tailWord_5883699) baseStart_5883699 baseEnd_5883699 := by
    simpa [prefixWord, tailWord_5883699, baseEnd_5883699] using wordTrace_append hprefix tailTrace_5883699
  have hstable : (prefixWord ++ tailWord_5883699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883699).length < 2 ^ (prefixWord ++ tailWord_5883699).sum := by decide
  have hdescent : baseEnd_5883699 < baseStart_5883699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883702 : List Nat := [5, 1, 2, 2, 1, 2, 10]
def baseStart_5883702 : Nat := 118140960795 + 5883702 * 2 ^ 59
def prefixEnd_5883702 : Nat := 4983230072969 + 3 ^ 40 * 5883702 * 2
def baseEnd_5883702 : Nat := 37298359923704249661313

theorem tailTrace_5883702 : CollatzResearch.WordTrace tailWord_5883702 prefixEnd_5883702 37298359923704249661313 := by
  unfold tailWord_5883702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13412265108147499071625835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143064161153573323430675573 13412265108147499071625835)
  ·
    refine ⟨20118397662221248607438753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13412265108147499071625835 20118397662221248607438753)
    ·
      refine ⟨15088798246665936455579065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20118397662221248607438753 15088798246665936455579065)
      ·
        refine ⟨11316598684999452341684299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15088798246665936455579065 11316598684999452341684299)
        ·
          refine ⟨16974898027499178512526449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11316598684999452341684299 16974898027499178512526449)
          ·
            refine ⟨12731173520624383884394837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16974898027499178512526449 12731173520624383884394837)
            ·
              refine ⟨37298359923704249661313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12731173520624383884394837 37298359923704249661313)
              ·
                rfl

theorem cell23_5883702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 10].length) (baseStart_5883702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883702 prefixEnd_5883702 := by exact prefixLift 5883702
  have htrace : WordTrace (prefixWord ++ tailWord_5883702) baseStart_5883702 baseEnd_5883702 := by
    simpa [prefixWord, tailWord_5883702, baseEnd_5883702] using wordTrace_append hprefix tailTrace_5883702
  have hstable : (prefixWord ++ tailWord_5883702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883702).length < 2 ^ (prefixWord ++ tailWord_5883702).sum := by decide
  have hdescent : baseEnd_5883702 < baseStart_5883702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883729 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 3]
def baseStart_5883729 : Nat := 118140960795 + 5883729 * 2 ^ 59
def prefixEnd_5883729 : Nat := 4983230072969 + 3 ^ 40 * 5883729 * 2
def baseEnd_5883729 : Nat := 3021181017797715616928729

theorem tailTrace_5883729 : CollatzResearch.WordTrace tailWord_5883729 prefixEnd_5883729 3021181017797715616928729 := by
  unfold tailWord_5883729
  simp only [CollatzResearch.WordTrace]
  refine ⟨214597226501262168757246241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143064817667508112504830827 214597226501262168757246241)
  ·
    refine ⟨160947919875946626567934681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214597226501262168757246241 160947919875946626567934681)
    ·
      refine ⟨120710939906959969925951011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160947919875946626567934681 120710939906959969925951011)
      ·
        refine ⟨181066409860439954888926517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120710939906959969925951011 181066409860439954888926517)
        ·
          refine ⟨16974975924416245770836861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181066409860439954888926517 16974975924416245770836861)
          ·
            refine ⟨6365615971656092164063823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16974975924416245770836861 6365615971656092164063823)
            ·
              refine ⟨9548423957484138246095735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365615971656092164063823 9548423957484138246095735)
              ·
                refine ⟨14322635936226207369143603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9548423957484138246095735 14322635936226207369143603)
                ·
                  refine ⟨21483953904339311053715405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14322635936226207369143603 21483953904339311053715405)
                  ·
                    refine ⟨8056482714127241645143277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21483953904339311053715405 8056482714127241645143277)
                    ·
                      refine ⟨3021181017797715616928729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8056482714127241645143277 3021181017797715616928729)
                      ·
                        rfl

theorem cell23_5883729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_5883729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883729 prefixEnd_5883729 := by exact prefixLift 5883729
  have htrace : WordTrace (prefixWord ++ tailWord_5883729) baseStart_5883729 baseEnd_5883729 := by
    simpa [prefixWord, tailWord_5883729, baseEnd_5883729] using wordTrace_append hprefix tailTrace_5883729
  have hstable : (prefixWord ++ tailWord_5883729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883729).length < 2 ^ (prefixWord ++ tailWord_5883729).sum := by decide
  have hdescent : baseEnd_5883729 < baseStart_5883729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883755 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 3]
def baseStart_5883755 : Nat := 118140960795 + 5883755 * 2 ^ 59
def prefixEnd_5883755 : Nat := 4983230072969 + 3 ^ 40 * 5883755 * 2
def baseEnd_5883755 : Nat := 3021194368294732515203609

theorem tailTrace_5883755 : CollatzResearch.WordTrace tailWord_5883755 prefixEnd_5883755 3021194368294732515203609 := by
  unfold tailWord_5883755
  simp only [CollatzResearch.WordTrace]
  refine ⟨214598174799167975197692719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143065449866111983465128479 214598174799167975197692719)
  ·
    refine ⟨321897262198751962796539079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214598174799167975197692719 321897262198751962796539079)
    ·
      refine ⟨482845893298127944194808619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321897262198751962796539079 482845893298127944194808619)
      ·
        refine ⟨724268839947191916292212929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482845893298127944194808619 724268839947191916292212929)
        ·
          refine ⟨543201629960393937219159697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724268839947191916292212929 543201629960393937219159697)
          ·
            refine ⟨407401222470295452914369773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543201629960393937219159697 407401222470295452914369773)
            ·
              refine ⟨152775458426360794842888665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407401222470295452914369773 152775458426360794842888665)
              ·
                refine ⟨114581593819770596132166499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152775458426360794842888665 114581593819770596132166499)
                ·
                  refine ⟨171872390729655894198249749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114581593819770596132166499 171872390729655894198249749)
                  ·
                    refine ⟨8056518315452620040542957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 171872390729655894198249749 8056518315452620040542957)
                    ·
                      refine ⟨3021194368294732515203609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8056518315452620040542957 3021194368294732515203609)
                      ·
                        rfl

theorem cell23_5883755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 3].length) (baseStart_5883755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883755 prefixEnd_5883755 := by exact prefixLift 5883755
  have htrace : WordTrace (prefixWord ++ tailWord_5883755) baseStart_5883755 baseEnd_5883755 := by
    simpa [prefixWord, tailWord_5883755, baseEnd_5883755] using wordTrace_append hprefix tailTrace_5883755
  have hstable : (prefixWord ++ tailWord_5883755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883755).length < 2 ^ (prefixWord ++ tailWord_5883755).sum := by decide
  have hdescent : baseEnd_5883755 < baseStart_5883755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883769 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 4, 2, 2]
def baseStart_5883769 : Nat := 118140960795 + 5883769 * 2 ^ 59
def prefixEnd_5883769 : Nat := 4983230072969 + 3 ^ 40 * 5883769 * 2
def baseEnd_5883769 : Nat := 3021201557023895460428545

theorem tailTrace_5883769 : CollatzResearch.WordTrace tailWord_5883769 prefixEnd_5883769 3021201557023895460428545 := by
  unfold tailWord_5883769
  simp only [CollatzResearch.WordTrace]
  refine ⟨214598685421117255588702361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143065790280744837059134907 214598685421117255588702361)
  ·
    refine ⟨160949014065837941691526771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214598685421117255588702361 160949014065837941691526771)
    ·
      refine ⟨241423521098756912537290157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160949014065837941691526771 241423521098756912537290157)
      ·
        refine ⟨90533820412033842201483809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241423521098756912537290157 90533820412033842201483809)
        ·
          refine ⟨67900365309025381651112857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90533820412033842201483809 67900365309025381651112857)
          ·
            refine ⟨50925273981769036238334643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67900365309025381651112857 50925273981769036238334643)
            ·
              refine ⟨76387910972653554357501965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50925273981769036238334643 76387910972653554357501965)
              ·
                refine ⟨28645466614745082884063237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76387910972653554357501965 28645466614745082884063237)
                ·
                  refine ⟨5371024990264703040761857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28645466614745082884063237 5371024990264703040761857)
                  ·
                    refine ⟨4028268742698527280571393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5371024990264703040761857 4028268742698527280571393)
                    ·
                      refine ⟨3021201557023895460428545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028268742698527280571393 3021201557023895460428545)
                      ·
                        rfl

theorem cell23_5883769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_5883769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883769 prefixEnd_5883769 := by exact prefixLift 5883769
  have htrace : WordTrace (prefixWord ++ tailWord_5883769) baseStart_5883769 baseEnd_5883769 := by
    simpa [prefixWord, tailWord_5883769, baseEnd_5883769] using wordTrace_append hprefix tailTrace_5883769
  have hstable : (prefixWord ++ tailWord_5883769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883769).length < 2 ^ (prefixWord ++ tailWord_5883769).sum := by decide
  have hdescent : baseEnd_5883769 < baseStart_5883769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883790 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5883790 : Nat := 118140960795 + 5883790 * 2 ^ 59
def prefixEnd_5883790 : Nat := 4983230072969 + 3 ^ 40 * 5883790 * 2
def baseEnd_5883790 : Nat := 3021212340117639878265949

theorem tailTrace_5883790 : CollatzResearch.WordTrace tailWord_5883790 prefixEnd_5883790 3021212340117639878265949 := by
  unfold tailWord_5883790
  simp only [CollatzResearch.WordTrace]
  refine ⟨26824931419255147021902103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143066300902694117450144549 26824931419255147021902103)
  ·
    refine ⟨40237397128882720532853155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26824931419255147021902103 40237397128882720532853155)
    ·
      refine ⟨60356095693324080799279733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40237397128882720532853155 60356095693324080799279733)
      ·
        refine ⟨5658383971249132574932475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60356095693324080799279733 5658383971249132574932475)
        ·
          refine ⟨8487575956873698862398713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658383971249132574932475 8487575956873698862398713)
          ·
            refine ⟨6365681967655274146799035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8487575956873698862398713 6365681967655274146799035)
            ·
              refine ⟨9548522951482911220198553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365681967655274146799035 9548522951482911220198553)
              ·
                refine ⟨7161392213612183415148915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9548522951482911220198553 7161392213612183415148915)
                ·
                  refine ⟨10742088320418275122723373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7161392213612183415148915 10742088320418275122723373)
                  ·
                    refine ⟨4028283120156853171021265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10742088320418275122723373 4028283120156853171021265)
                    ·
                      refine ⟨3021212340117639878265949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028283120156853171021265 3021212340117639878265949)
                      ·
                        rfl

theorem cell23_5883790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5883790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883790 prefixEnd_5883790 := by exact prefixLift 5883790
  have htrace : WordTrace (prefixWord ++ tailWord_5883790) baseStart_5883790 baseEnd_5883790 := by
    simpa [prefixWord, tailWord_5883790, baseEnd_5883790] using wordTrace_append hprefix tailTrace_5883790
  have hstable : (prefixWord ++ tailWord_5883790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883790).length < 2 ^ (prefixWord ++ tailWord_5883790).sum := by decide
  have hdescent : baseEnd_5883790 < baseStart_5883790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883829 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_5883829 : Nat := 118140960795 + 5883829 * 2 ^ 59
def prefixEnd_5883829 : Nat := 4983230072969 + 3 ^ 40 * 5883829 * 2
def baseEnd_5883829 : Nat := 3021232365863165225678269

theorem tailTrace_5883829 : CollatzResearch.WordTrace tailWord_5883829 prefixEnd_5883829 3021232365863165225678269 := by
  unfold tailWord_5883829
  simp only [CollatzResearch.WordTrace]
  refine ⟨214600873800899885835886541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143067249200599923890591027 214600873800899885835886541)
  ·
    refine ⟨80475327675337457188457453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214600873800899885835886541 80475327675337457188457453)
    ·
      refine ⟨30178247878251546445671545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80475327675337457188457453 30178247878251546445671545)
      ·
        refine ⟨22633685908688659834253659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30178247878251546445671545 22633685908688659834253659)
        ·
          refine ⟨33950528863032989751380489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22633685908688659834253659 33950528863032989751380489)
          ·
            refine ⟨25462896647274742313535367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33950528863032989751380489 25462896647274742313535367)
            ·
              refine ⟨38194344970912113470303051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25462896647274742313535367 38194344970912113470303051)
              ·
                refine ⟨57291517456368170205454577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38194344970912113470303051 57291517456368170205454577)
                ·
                  refine ⟨42968638092276127654090933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57291517456368170205454577 42968638092276127654090933)
                  ·
                    refine ⟨4028309821150886967571025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42968638092276127654090933 4028309821150886967571025)
                    ·
                      refine ⟨3021232365863165225678269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028309821150886967571025 3021232365863165225678269)
                      ·
                        rfl

theorem cell23_5883829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_5883829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883829 prefixEnd_5883829 := by exact prefixLift 5883829
  have htrace : WordTrace (prefixWord ++ tailWord_5883829) baseStart_5883829 baseEnd_5883829 := by
    simpa [prefixWord, tailWord_5883829, baseEnd_5883829] using wordTrace_append hprefix tailTrace_5883829
  have hstable : (prefixWord ++ tailWord_5883829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883829).length < 2 ^ (prefixWord ++ tailWord_5883829).sum := by decide
  have hdescent : baseEnd_5883829 < baseStart_5883829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883836 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5883836 : Nat := 118140960795 + 5883836 * 2 ^ 59
def prefixEnd_5883836 : Nat := 4983230072969 + 3 ^ 40 * 5883836 * 2
def baseEnd_5883836 : Nat := 3021235960227746698290737

theorem tailTrace_5883836 : CollatzResearch.WordTrace tailWord_5883836 prefixEnd_5883836 3021235960227746698290737 := by
  unfold tailWord_5883836
  simp only [CollatzResearch.WordTrace]
  refine ⟨107300564555937263015695681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143067419407916350687594241 107300564555937263015695681)
  ·
    refine ⟨80475423416952947261771761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107300564555937263015695681 80475423416952947261771761)
    ·
      refine ⟨60356567562714710446328821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80475423416952947261771761 60356567562714710446328821)
      ·
        refine ⟨5658428209004504104343327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60356567562714710446328821 5658428209004504104343327)
        ·
          refine ⟨8487642313506756156514991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658428209004504104343327 8487642313506756156514991)
          ·
            refine ⟨12731463470260134234772487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487642313506756156514991 12731463470260134234772487)
            ·
              refine ⟨19097195205390201352158731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12731463470260134234772487 19097195205390201352158731)
              ·
                refine ⟨28645792808085302028238097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19097195205390201352158731 28645792808085302028238097)
                ·
                  refine ⟨21484344606063976521178573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28645792808085302028238097 21484344606063976521178573)
                  ·
                    refine ⟨8056629227273991195441965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21484344606063976521178573 8056629227273991195441965)
                    ·
                      refine ⟨3021235960227746698290737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8056629227273991195441965 3021235960227746698290737)
                      ·
                        rfl

theorem cell23_5883836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5883836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883836 prefixEnd_5883836 := by exact prefixLift 5883836
  have htrace : WordTrace (prefixWord ++ tailWord_5883836) baseStart_5883836 baseEnd_5883836 := by
    simpa [prefixWord, tailWord_5883836, baseEnd_5883836] using wordTrace_append hprefix tailTrace_5883836
  have hstable : (prefixWord ++ tailWord_5883836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883836).length < 2 ^ (prefixWord ++ tailWord_5883836).sum := by decide
  have hdescent : baseEnd_5883836 < baseStart_5883836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883882 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 8]
def baseStart_5883882 : Nat := 118140960795 + 5883882 * 2 ^ 59
def prefixEnd_5883882 : Nat := 4983230072969 + 3 ^ 40 * 5883882 * 2
def baseEnd_5883882 : Nat := 335695508926428168701725

theorem tailTrace_5883882 : CollatzResearch.WordTrace tailWord_5883882 prefixEnd_5883882 335695508926428168701725 := by
  unfold tailWord_5883882
  simp only [CollatzResearch.WordTrace]
  refine ⟨53650701717426968971891475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143068537913138583925043933 53650701717426968971891475)
  ·
    refine ⟨80476052576140453457837213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53650701717426968971891475 80476052576140453457837213)
    ·
      refine ⟨30178519716052670046688955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80476052576140453457837213 30178519716052670046688955)
      ·
        refine ⟨45267779574079005070033433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30178519716052670046688955 45267779574079005070033433)
        ·
          refine ⟨33950834680559253802525075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45267779574079005070033433 33950834680559253802525075)
          ·
            refine ⟨50926252020838880703787613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33950834680559253802525075 50926252020838880703787613)
            ·
              refine ⟨19097344507814580263920355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50926252020838880703787613 19097344507814580263920355)
              ·
                refine ⟨28646016761721870395880533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19097344507814580263920355 28646016761721870395880533)
                ·
                  refine ⟨335695508926428168701725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28646016761721870395880533 335695508926428168701725)
                  ·
                    rfl

theorem cell23_5883882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_5883882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883882 prefixEnd_5883882 := by exact prefixLift 5883882
  have htrace : WordTrace (prefixWord ++ tailWord_5883882) baseStart_5883882 baseEnd_5883882 := by
    simpa [prefixWord, tailWord_5883882, baseEnd_5883882] using wordTrace_append hprefix tailTrace_5883882
  have hstable : (prefixWord ++ tailWord_5883882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883882).length < 2 ^ (prefixWord ++ tailWord_5883882).sum := by decide
  have hdescent : baseEnd_5883882 < baseStart_5883882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5883886 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_5883886 : Nat := 118140960795 + 5883886 * 2 ^ 59
def prefixEnd_5883886 : Nat := 4983230072969 + 3 ^ 40 * 5883886 * 2
def baseEnd_5883886 : Nat := 1007087211420157167555169

theorem tailTrace_5883886 : CollatzResearch.WordTrace tailWord_5883886 prefixEnd_5883886 1007087211420157167555169 := by
  unfold tailWord_5883886
  simp only [CollatzResearch.WordTrace]
  refine ⟨26825369095211673071338939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143068635174462256380474341 26825369095211673071338939)
  ·
    refine ⟨40238053642817509607008409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26825369095211673071338939 40238053642817509607008409)
    ·
      refine ⟨30178540232113132205256307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40238053642817509607008409 30178540232113132205256307)
      ·
        refine ⟨45267810348169698307884461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30178540232113132205256307 45267810348169698307884461)
        ·
          refine ⟨16975428880563636865456673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45267810348169698307884461 16975428880563636865456673)
          ·
            refine ⟨12731571660422727649092505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16975428880563636865456673 12731571660422727649092505)
            ·
              refine ⟨9548678745317045736819379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12731571660422727649092505 9548678745317045736819379)
              ·
                refine ⟨14323018117975568605229069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9548678745317045736819379 14323018117975568605229069)
                ·
                  refine ⟨5371131794240838226960901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14323018117975568605229069 5371131794240838226960901)
                  ·
                    refine ⟨1007087211420157167555169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5371131794240838226960901 1007087211420157167555169)
                    ·
                      rfl

theorem cell23_5883886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_5883886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5883886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5883886 prefixEnd_5883886 := by exact prefixLift 5883886
  have htrace : WordTrace (prefixWord ++ tailWord_5883886) baseStart_5883886 baseEnd_5883886 := by
    simpa [prefixWord, tailWord_5883886, baseEnd_5883886] using wordTrace_append hprefix tailTrace_5883886
  have hstable : (prefixWord ++ tailWord_5883886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5883886).length < 2 ^ (prefixWord ++ tailWord_5883886).sum := by decide
  have hdescent : baseEnd_5883886 < baseStart_5883886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5883886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884000 : List Nat := [2, 1, 1, 3, 2, 4, 1, 4, 1, 2, 2]
def baseStart_5884000 : Nat := 118140960795 + 5884000 * 2 ^ 59
def prefixEnd_5884000 : Nat := 4983230072969 + 3 ^ 40 * 5884000 * 2
def baseEnd_5884000 : Nat := 3021320171055084056639983

theorem tailTrace_5884000 : CollatzResearch.WordTrace tailWord_5884000 prefixEnd_5884000 3021320171055084056639983 := by
  unfold tailWord_5884000
  simp only [CollatzResearch.WordTrace]
  refine ⟨107303555341640191020180727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143071407122186921360240969 107303555341640191020180727)
  ·
    refine ⟨160955333012460286530271091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107303555341640191020180727 160955333012460286530271091)
    ·
      refine ⟨241432999518690429795406637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160955333012460286530271091 241432999518690429795406637)
      ·
        refine ⟨90537374819508911173277489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241432999518690429795406637 90537374819508911173277489)
        ·
          refine ⟨67903031114631683379958117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90537374819508911173277489 67903031114631683379958117)
          ·
            refine ⟨12731818333993440633742147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67903031114631683379958117 12731818333993440633742147)
            ·
              refine ⟨19097727500990160950613221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12731818333993440633742147 19097727500990160950613221)
              ·
                refine ⟨3580823906435655178239979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19097727500990160950613221 3580823906435655178239979)
                ·
                  refine ⟨5371235859653482767359969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3580823906435655178239979 5371235859653482767359969)
                  ·
                    refine ⟨4028426894740112075519977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5371235859653482767359969 4028426894740112075519977)
                    ·
                      refine ⟨3021320171055084056639983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028426894740112075519977 3021320171055084056639983)
                      ·
                        rfl

theorem cell23_5884000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_5884000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884000 prefixEnd_5884000 := by exact prefixLift 5884000
  have htrace : WordTrace (prefixWord ++ tailWord_5884000) baseStart_5884000 baseEnd_5884000 := by
    simpa [prefixWord, tailWord_5884000, baseEnd_5884000] using wordTrace_append hprefix tailTrace_5884000
  have hstable : (prefixWord ++ tailWord_5884000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884000).length < 2 ^ (prefixWord ++ tailWord_5884000).sum := by decide
  have hdescent : baseEnd_5884000 < baseStart_5884000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884016 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 3]
def baseStart_5884016 : Nat := 118140960795 + 5884016 * 2 ^ 59
def prefixEnd_5884016 : Nat := 4983230072969 + 3 ^ 40 * 5884016 * 2
def baseEnd_5884016 : Nat := 3021328386745555994039909

theorem tailTrace_5884016 : CollatzResearch.WordTrace tailWord_5884016 prefixEnd_5884016 3021328386745555994039909 := by
  unfold tailWord_5884016
  simp only [CollatzResearch.WordTrace]
  refine ⟨107303847125611208386471951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143071796167481611181962601 107303847125611208386471951)
  ·
    refine ⟨160955770688416812579707927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107303847125611208386471951 160955770688416812579707927)
    ·
      refine ⟨241433656032625218869561891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160955770688416812579707927 241433656032625218869561891)
      ·
        refine ⟨362150484048937828304342837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241433656032625218869561891 362150484048937828304342837)
        ·
          refine ⟨33951607879587921403532141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 362150484048937828304342837 33951607879587921403532141)
          ·
            refine ⟨12731852954845470526324553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33951607879587921403532141 12731852954845470526324553)
            ·
              refine ⟨9548889716134102894743415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12731852954845470526324553 9548889716134102894743415)
              ·
                refine ⟨14323334574201154342115123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9548889716134102894743415 14323334574201154342115123)
                ·
                  refine ⟨21485001861301731513172685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14323334574201154342115123 21485001861301731513172685)
                  ·
                    refine ⟨8056875697988149317439757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21485001861301731513172685 8056875697988149317439757)
                    ·
                      refine ⟨3021328386745555994039909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8056875697988149317439757 3021328386745555994039909)
                      ·
                        rfl

theorem cell23_5884016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_5884016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884016 prefixEnd_5884016 := by exact prefixLift 5884016
  have htrace : WordTrace (prefixWord ++ tailWord_5884016) baseStart_5884016 baseEnd_5884016 := by
    simpa [prefixWord, tailWord_5884016, baseEnd_5884016] using wordTrace_append hprefix tailTrace_5884016
  have hstable : (prefixWord ++ tailWord_5884016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884016).length < 2 ^ (prefixWord ++ tailWord_5884016).sum := by decide
  have hdescent : baseEnd_5884016 < baseStart_5884016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884032 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 3, 8]
def baseStart_5884032 : Nat := 118140960795 + 5884032 * 2 ^ 59
def prefixEnd_5884032 : Nat := 4983230072969 + 3 ^ 40 * 5884032 * 2
def baseEnd_5884032 : Nat := 1007112200812009310479945

theorem tailTrace_5884032 : CollatzResearch.WordTrace tailWord_5884032 prefixEnd_5884032 1007112200812009310479945 := by
  unfold tailWord_5884032
  simp only [CollatzResearch.WordTrace]
  refine ⟨107304138909582225752763175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143072185212776301003684233 107304138909582225752763175)
  ·
    refine ⟨160956208364373338629144763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107304138909582225752763175 160956208364373338629144763)
    ·
      refine ⟨241434312546560007943717145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160956208364373338629144763 241434312546560007943717145)
      ·
        refine ⟨181075734409920005957787859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241434312546560007943717145 181075734409920005957787859)
        ·
          refine ⟨271613601614880008936681789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181075734409920005957787859 271613601614880008936681789)
          ·
            refine ⟨101855100605580003351255671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271613601614880008936681789 101855100605580003351255671)
            ·
              refine ⟨152782650908370005026883507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101855100605580003351255671 152782650908370005026883507)
              ·
                refine ⟨229173976362555007540325261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152782650908370005026883507 229173976362555007540325261)
                ·
                  refine ⟨85940241135958127827621973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229173976362555007540325261 85940241135958127827621973)
                  ·
                    refine ⟨1007112200812009310479945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85940241135958127827621973 1007112200812009310479945)
                    ·
                      rfl

theorem cell23_5884032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_5884032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884032 prefixEnd_5884032 := by exact prefixLift 5884032
  have htrace : WordTrace (prefixWord ++ tailWord_5884032) baseStart_5884032 baseEnd_5884032 := by
    simpa [prefixWord, tailWord_5884032, baseEnd_5884032] using wordTrace_append hprefix tailTrace_5884032
  have hstable : (prefixWord ++ tailWord_5884032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884032).length < 2 ^ (prefixWord ++ tailWord_5884032).sum := by decide
  have hdescent : baseEnd_5884032 < baseStart_5884032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884066 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_5884066 : Nat := 118140960795 + 5884066 * 2 ^ 59
def prefixEnd_5884066 : Nat := 4983230072969 + 3 ^ 40 * 5884066 * 2
def baseEnd_5884066 : Nat := 1007118020259426932804893

theorem tailTrace_5884066 : CollatzResearch.WordTrace tailWord_5884066 prefixEnd_5884066 1007118020259426932804893 := by
  unfold tailWord_5884066
  simp only [CollatzResearch.WordTrace]
  refine ⟨53652379475260318828066013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143073011934027516874842701 53652379475260318828066013)
  ·
    refine ⟨20119642303222619560524755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53652379475260318828066013 20119642303222619560524755)
    ·
      refine ⟨30179463454833929340787133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20119642303222619560524755 30179463454833929340787133)
      ·
        refine ⟨11317298795562723502795175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30179463454833929340787133 11317298795562723502795175)
        ·
          refine ⟨16975948193344085254192763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11317298795562723502795175 16975948193344085254192763)
          ·
            refine ⟨25463922290016127881289145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16975948193344085254192763 25463922290016127881289145)
            ·
              refine ⟨19097941717512095910966859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25463922290016127881289145 19097941717512095910966859)
              ·
                refine ⟨28646912576268143866450289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19097941717512095910966859 28646912576268143866450289)
                ·
                  refine ⟨21485184432201107899837717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28646912576268143866450289 21485184432201107899837717)
                  ·
                    refine ⟨1007118020259426932804893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21485184432201107899837717 1007118020259426932804893)
                    ·
                      rfl

theorem cell23_5884066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_5884066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884066 prefixEnd_5884066 := by exact prefixLift 5884066
  have htrace : WordTrace (prefixWord ++ tailWord_5884066) baseStart_5884066 baseEnd_5884066 := by
    simpa [prefixWord, tailWord_5884066, baseEnd_5884066] using wordTrace_append hprefix tailTrace_5884066
  have hstable : (prefixWord ++ tailWord_5884066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884066).length < 2 ^ (prefixWord ++ tailWord_5884066).sum := by decide
  have hdescent : baseEnd_5884066 < baseStart_5884066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884069 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_5884069 : Nat := 118140960795 + 5884069 * 2 ^ 59
def prefixEnd_5884069 : Nat := 4983230072969 + 3 ^ 40 * 5884069 * 2
def baseEnd_5884069 : Nat := 3021355601220244286677165

theorem tailTrace_5884069 : CollatzResearch.WordTrace tailWord_5884069 prefixEnd_5884069 3021355601220244286677165 := by
  unfold tailWord_5884069
  simp only [CollatzResearch.WordTrace]
  refine ⟨214609627320030406824623261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143073084880020271216415507 214609627320030406824623261)
  ·
    refine ⟨80478610245011402559233723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214609627320030406824623261 80478610245011402559233723)
    ·
      refine ⟨120717915367517103838850585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80478610245011402559233723 120717915367517103838850585)
      ·
        refine ⟨90538436525637827879137939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120717915367517103838850585 90538436525637827879137939)
        ·
          refine ⟨135807654788456741818706909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90538436525637827879137939 135807654788456741818706909)
          ·
            refine ⟨50927870545671278182015091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135807654788456741818706909 50927870545671278182015091)
            ·
              refine ⟨76391805818506917273022637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50927870545671278182015091 76391805818506917273022637)
              ·
                refine ⟨28646927181940093977383489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76391805818506917273022637 28646927181940093977383489)
                ·
                  refine ⟨21485195386455070483037617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28646927181940093977383489 21485195386455070483037617)
                  ·
                    refine ⟨16113896539841302862278213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21485195386455070483037617 16113896539841302862278213)
                    ·
                      refine ⟨3021355601220244286677165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16113896539841302862278213 3021355601220244286677165)
                      ·
                        rfl

theorem cell23_5884069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_5884069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884069 prefixEnd_5884069 := by exact prefixLift 5884069
  have htrace : WordTrace (prefixWord ++ tailWord_5884069) baseStart_5884069 baseEnd_5884069 := by
    simpa [prefixWord, tailWord_5884069, baseEnd_5884069] using wordTrace_append hprefix tailTrace_5884069
  have hstable : (prefixWord ++ tailWord_5884069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884069).length < 2 ^ (prefixWord ++ tailWord_5884069).sum := by decide
  have hdescent : baseEnd_5884069 < baseStart_5884069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884124 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5884124 : Nat := 118140960795 + 5884124 * 2 ^ 59
def prefixEnd_5884124 : Nat := 4983230072969 + 3 ^ 40 * 5884124 * 2
def baseEnd_5884124 : Nat := 3021383842656241571489413

theorem tailTrace_5884124 : CollatzResearch.WordTrace tailWord_5884124 prefixEnd_5884124 3021383842656241571489413 := by
  unfold tailWord_5884124
  simp only [CollatzResearch.WordTrace]
  refine ⟨107305816667415575608937713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143074422223220767478583617 107305816667415575608937713)
  ·
    refine ⟨80479362500561681706703285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107305816667415575608937713 80479362500561681706703285)
    ·
      refine ⟨7544940234427657660003433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80479362500561681706703285 7544940234427657660003433)
      ·
        refine ⟨5658705175820743245002575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7544940234427657660003433 5658705175820743245002575)
        ·
          refine ⟨8488057763731114867503863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658705175820743245002575 8488057763731114867503863)
          ·
            refine ⟨12732086645596672301255795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488057763731114867503863 12732086645596672301255795)
            ·
              refine ⟨19098129968395008451883693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12732086645596672301255795 19098129968395008451883693)
              ·
                refine ⟨7161798738148128169456385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19098129968395008451883693 7161798738148128169456385)
                ·
                  refine ⟨5371349053611096127092289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7161798738148128169456385 5371349053611096127092289)
                  ·
                    refine ⟨4028511790208322095319217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5371349053611096127092289 4028511790208322095319217)
                    ·
                      refine ⟨3021383842656241571489413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028511790208322095319217 3021383842656241571489413)
                      ·
                        rfl

theorem cell23_5884124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5884124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884124 prefixEnd_5884124 := by exact prefixLift 5884124
  have htrace : WordTrace (prefixWord ++ tailWord_5884124) baseStart_5884124 baseEnd_5884124 := by
    simpa [prefixWord, tailWord_5884124, baseEnd_5884124] using wordTrace_append hprefix tailTrace_5884124
  have hstable : (prefixWord ++ tailWord_5884124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884124).length < 2 ^ (prefixWord ++ tailWord_5884124).sum := by decide
  have hdescent : baseEnd_5884124 < baseStart_5884124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884159 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_5884159 : Nat := 118140960795 + 5884159 * 2 ^ 59
def prefixEnd_5884159 : Nat := 4983230072969 + 3 ^ 40 * 5884159 * 2
def baseEnd_5884159 : Nat := 3021401814479148934551751

theorem tailTrace_5884159 : CollatzResearch.WordTrace tailWord_5884159 prefixEnd_5884159 3021401814479148934551751 := by
  unfold tailWord_5884159
  simp only [CollatzResearch.WordTrace]
  refine ⟨214612909889704352195399531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143075273259802901463599687 214612909889704352195399531)
  ·
    refine ⟨321919364834556528293099297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214612909889704352195399531 321919364834556528293099297)
    ·
      refine ⟨241439523625917396219824473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321919364834556528293099297 241439523625917396219824473)
      ·
        refine ⟨181079642719438047164868355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241439523625917396219824473 181079642719438047164868355)
        ·
          refine ⟨271619464079157070747302533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181079642719438047164868355 271619464079157070747302533)
          ·
            refine ⟨50928649514841950765119225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271619464079157070747302533 50928649514841950765119225)
            ·
              refine ⟨38196487136131463073839419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50928649514841950765119225 38196487136131463073839419)
              ·
                refine ⟨57294730704197194610759129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38196487136131463073839419 57294730704197194610759129)
                ·
                  refine ⟨42971048028147895958069347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57294730704197194610759129 42971048028147895958069347)
                  ·
                    refine ⟨64456572042221843937104021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42971048028147895958069347 64456572042221843937104021)
                    ·
                      refine ⟨3021401814479148934551751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64456572042221843937104021 3021401814479148934551751)
                      ·
                        rfl

theorem cell23_5884159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_5884159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884159 prefixEnd_5884159 := by exact prefixLift 5884159
  have htrace : WordTrace (prefixWord ++ tailWord_5884159) baseStart_5884159 baseEnd_5884159 := by
    simpa [prefixWord, tailWord_5884159, baseEnd_5884159] using wordTrace_append hprefix tailTrace_5884159
  have hstable : (prefixWord ++ tailWord_5884159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884159).length < 2 ^ (prefixWord ++ tailWord_5884159).sum := by decide
  have hdescent : baseEnd_5884159 < baseStart_5884159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884190 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_5884190 : Nat := 118140960795 + 5884190 * 2 ^ 59
def prefixEnd_5884190 : Nat := 4983230072969 + 3 ^ 40 * 5884190 * 2
def baseEnd_5884190 : Nat := 1007139244126479437754703

theorem tailTrace_5884190 : CollatzResearch.WordTrace tailWord_5884190 prefixEnd_5884190 1007139244126479437754703 := by
  unfold tailWord_5884190
  simp only [CollatzResearch.WordTrace]
  refine ⟨26826755069074005561222253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143076027035061362993185349 26826755069074005561222253)
  ·
    refine ⟨10060033150902752085458345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26826755069074005561222253 10060033150902752085458345)
    ·
      refine ⟨7545024863177064064093759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10060033150902752085458345 7545024863177064064093759)
      ·
        refine ⟨11317537294765596096140639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7545024863177064064093759 11317537294765596096140639)
        ·
          refine ⟨16976305942148394144210959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11317537294765596096140639 16976305942148394144210959)
          ·
            refine ⟨25464458913222591216316439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16976305942148394144210959 25464458913222591216316439)
            ·
              refine ⟨38196688369833886824474659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25464458913222591216316439 38196688369833886824474659)
              ·
                refine ⟨57295032554750830236711989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38196688369833886824474659 57295032554750830236711989)
                ·
                  refine ⟨5371409302007890334691749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57295032554750830236711989 5371409302007890334691749)
                  ·
                    refine ⟨1007139244126479437754703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5371409302007890334691749 1007139244126479437754703)
                    ·
                      rfl

theorem cell23_5884190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_5884190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884190 prefixEnd_5884190 := by exact prefixLift 5884190
  have htrace : WordTrace (prefixWord ++ tailWord_5884190) baseStart_5884190 baseEnd_5884190 := by
    simpa [prefixWord, tailWord_5884190, baseEnd_5884190] using wordTrace_append hprefix tailTrace_5884190
  have hstable : (prefixWord ++ tailWord_5884190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884190).length < 2 ^ (prefixWord ++ tailWord_5884190).sum := by decide
  have hdescent : baseEnd_5884190 < baseStart_5884190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884213 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_5884213 : Nat := 118140960795 + 5884213 * 2 ^ 59
def prefixEnd_5884213 : Nat := 4983230072969 + 3 ^ 40 * 5884213 * 2
def baseEnd_5884213 : Nat := 3021429542434491723276503

theorem tailTrace_5884213 : CollatzResearch.WordTrace tailWord_5884213 prefixEnd_5884213 3021429542434491723276503 := by
  unfold tailWord_5884213
  simp only [CollatzResearch.WordTrace]
  refine ⟨214614879431508719417865293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143076586287672479611910195 214614879431508719417865293)
  ·
    refine ⟨80480579786815769781699485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214614879431508719417865293 80480579786815769781699485)
    ·
      refine ⟨30180217420055913668137307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80480579786815769781699485 30180217420055913668137307)
      ·
        refine ⟨45270326130083870502205961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30180217420055913668137307 45270326130083870502205961)
        ·
          refine ⟨33952744597562902876654471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45270326130083870502205961 33952744597562902876654471)
          ·
            refine ⟨50929116896344354314981707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33952744597562902876654471 50929116896344354314981707)
            ·
              refine ⟨76393675344516531472472561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50929116896344354314981707 76393675344516531472472561)
              ·
                refine ⟨57295256508387398604354421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76393675344516531472472561 57295256508387398604354421)
                ·
                  refine ⟨5371430297661318619158227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57295256508387398604354421 5371430297661318619158227)
                  ·
                    refine ⟨8057145446491977928737341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5371430297661318619158227 8057145446491977928737341)
                    ·
                      refine ⟨3021429542434491723276503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8057145446491977928737341 3021429542434491723276503)
                      ·
                        rfl

theorem cell23_5884213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_5884213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884213 prefixEnd_5884213 := by exact prefixLift 5884213
  have htrace : WordTrace (prefixWord ++ tailWord_5884213) baseStart_5884213 baseEnd_5884213 := by
    simpa [prefixWord, tailWord_5884213, baseEnd_5884213] using wordTrace_append hprefix tailTrace_5884213
  have hstable : (prefixWord ++ tailWord_5884213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884213).length < 2 ^ (prefixWord ++ tailWord_5884213).sum := by decide
  have hdescent : baseEnd_5884213 < baseStart_5884213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884223 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 4, 3, 2]
def baseStart_5884223 : Nat := 118140960795 + 5884223 * 2 ^ 59
def prefixEnd_5884223 : Nat := 4983230072969 + 3 ^ 40 * 5884223 * 2
def baseEnd_5884223 : Nat := 3021434677241036684151457

theorem tailTrace_5884223 : CollatzResearch.WordTrace tailWord_5884223 prefixEnd_5884223 3021434677241036684151457 := by
  unfold tailWord_5884223
  simp only [CollatzResearch.WordTrace]
  refine ⟨214615244161472491125729323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143076829440981660750486215 214615244161472491125729323)
  ·
    refine ⟨321922866242208736688593985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214615244161472491125729323 321922866242208736688593985)
    ·
      refine ⟨241442149681656552516445489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321922866242208736688593985 241442149681656552516445489)
      ·
        refine ⟨181081612261242414387334117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241442149681656552516445489 181081612261242414387334117)
        ·
          refine ⟨33952802298982952697625147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181081612261242414387334117 33952802298982952697625147)
          ·
            refine ⟨50929203448474429046437721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33952802298982952697625147 50929203448474429046437721)
            ·
              refine ⟨38196902586355821784828291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50929203448474429046437721 38196902586355821784828291)
              ·
                refine ⟨57295353879533732677242437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38196902586355821784828291 57295353879533732677242437)
                ·
                  refine ⟨10742878852412574876982957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57295353879533732677242437 10742878852412574876982957)
                  ·
                    refine ⟨4028579569654715578868609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10742878852412574876982957 4028579569654715578868609)
                    ·
                      refine ⟨3021434677241036684151457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028579569654715578868609 3021434677241036684151457)
                      ·
                        rfl

theorem cell23_5884223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_5884223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884223 prefixEnd_5884223 := by exact prefixLift 5884223
  have htrace : WordTrace (prefixWord ++ tailWord_5884223) baseStart_5884223 baseEnd_5884223 := by
    simpa [prefixWord, tailWord_5884223, baseEnd_5884223] using wordTrace_append hprefix tailTrace_5884223
  have hstable : (prefixWord ++ tailWord_5884223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884223).length < 2 ^ (prefixWord ++ tailWord_5884223).sum := by decide
  have hdescent : baseEnd_5884223 < baseStart_5884223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884229 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_5884229 : Nat := 118140960795 + 5884229 * 2 ^ 59
def prefixEnd_5884229 : Nat := 4983230072969 + 3 ^ 40 * 5884229 * 2
def baseEnd_5884229 : Nat := 1007145919374987886892143

theorem tailTrace_5884229 : CollatzResearch.WordTrace tailWord_5884229 prefixEnd_5884229 1007145919374987886892143 := by
  unfold tailWord_5884229
  simp only [CollatzResearch.WordTrace]
  refine ⟨214615462999450754150447741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143076975332967169433631827 214615462999450754150447741)
  ·
    refine ⟨80480798624794032806417903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214615462999450754150447741 80480798624794032806417903)
    ·
      refine ⟨120721197937191049209626855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80480798624794032806417903 120721197937191049209626855)
      ·
        refine ⟨181081796905786573814440283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120721197937191049209626855 181081796905786573814440283)
        ·
          refine ⟨271622695358679860721660425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181081796905786573814440283 271622695358679860721660425)
          ·
            refine ⟨203717021519009895541245319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271622695358679860721660425 203717021519009895541245319)
            ·
              refine ⟨305575532278514843311867979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203717021519009895541245319 305575532278514843311867979)
              ·
                refine ⟨458363298417772264967801969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305575532278514843311867979 458363298417772264967801969)
                ·
                  refine ⟨343772473813329198725851477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458363298417772264967801969 343772473813329198725851477)
                  ·
                    refine ⟨1007145919374987886892143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 343772473813329198725851477 1007145919374987886892143)
                    ·
                      rfl

theorem cell23_5884229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_5884229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884229 prefixEnd_5884229 := by exact prefixLift 5884229
  have htrace : WordTrace (prefixWord ++ tailWord_5884229) baseStart_5884229 baseEnd_5884229 := by
    simpa [prefixWord, tailWord_5884229, baseEnd_5884229] using wordTrace_append hprefix tailTrace_5884229
  have hstable : (prefixWord ++ tailWord_5884229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884229).length < 2 ^ (prefixWord ++ tailWord_5884229).sum := by decide
  have hdescent : baseEnd_5884229 < baseStart_5884229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884263 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 4, 4]
def baseStart_5884263 : Nat := 118140960795 + 5884263 * 2 ^ 59
def prefixEnd_5884263 : Nat := 4983230072969 + 3 ^ 40 * 5884263 * 2
def baseEnd_5884263 : Nat := 1007151738822405509217091

theorem tailTrace_5884263 : CollatzResearch.WordTrace tailWord_5884263 prefixEnd_5884263 1007151738822405509217091 := by
  unfold tailWord_5884263
  simp only [CollatzResearch.WordTrace]
  refine ⟨214616703081327577957185443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143077802054218385304790295 214616703081327577957185443)
  ·
    refine ⟨321925054621991366935778165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214616703081327577957185443 321925054621991366935778165)
    ·
      refine ⟨30180473870811690650229203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321925054621991366935778165 30180473870811690650229203)
      ·
        refine ⟨45270710806217535975343805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30180473870811690650229203 45270710806217535975343805)
        ·
          refine ⟨16976516552331575990753927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45270710806217535975343805 16976516552331575990753927)
          ·
            refine ⟨25464774828497363986130891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16976516552331575990753927 25464774828497363986130891)
            ·
              refine ⟨38197162242746045979196337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25464774828497363986130891 38197162242746045979196337)
              ·
                refine ⟨28647871682059534484397253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38197162242746045979196337 28647871682059534484397253)
                ·
                  refine ⟨5371475940386162715824485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28647871682059534484397253 5371475940386162715824485)
                  ·
                    refine ⟨1007151738822405509217091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5371475940386162715824485 1007151738822405509217091)
                    ·
                      rfl

theorem cell23_5884263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_5884263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884263 prefixEnd_5884263 := by exact prefixLift 5884263
  have htrace : WordTrace (prefixWord ++ tailWord_5884263) baseStart_5884263 baseEnd_5884263 := by
    simpa [prefixWord, tailWord_5884263, baseEnd_5884263] using wordTrace_append hprefix tailTrace_5884263
  have hstable : (prefixWord ++ tailWord_5884263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884263).length < 2 ^ (prefixWord ++ tailWord_5884263).sum := by decide
  have hdescent : baseEnd_5884263 < baseStart_5884263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884264 : List Nat := [2, 1, 4, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_5884264 : Nat := 118140960795 + 5884264 * 2 ^ 59
def prefixEnd_5884264 : Nat := 4983230072969 + 3 ^ 40 * 5884264 * 2
def baseEnd_5884264 : Nat := 3021455729947871023738769

theorem tailTrace_5884264 : CollatzResearch.WordTrace tailWord_5884264 prefixEnd_5884264 3021455729947871023738769 := by
  unfold tailWord_5884264
  simp only [CollatzResearch.WordTrace]
  refine ⟨107308369777161977563985923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143077826369549303418647897 107308369777161977563985923)
  ·
    refine ⟨160962554665742966345978885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107308369777161977563985923 160962554665742966345978885)
    ·
      refine ⟨30180478999826806189871041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160962554665742966345978885 30180478999826806189871041)
      ·
        refine ⟨22635359249870104642403281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30180478999826806189871041 22635359249870104642403281)
        ·
          refine ⟨16976519437402578481802461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22635359249870104642403281 16976519437402578481802461)
          ·
            refine ⟨6366194789025966930675923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16976519437402578481802461 6366194789025966930675923)
            ·
              refine ⟨9549292183538950396013885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6366194789025966930675923 9549292183538950396013885)
              ·
                refine ⟨3580984568827106398505207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9549292183538950396013885 3580984568827106398505207)
                ·
                  refine ⟨5371476853240659597757811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3580984568827106398505207 5371476853240659597757811)
                  ·
                    refine ⟨8057215279860989396636717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5371476853240659597757811 8057215279860989396636717)
                    ·
                      refine ⟨3021455729947871023738769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8057215279860989396636717 3021455729947871023738769)
                      ·
                        rfl

theorem cell23_5884264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_5884264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884264 prefixEnd_5884264 := by exact prefixLift 5884264
  have htrace : WordTrace (prefixWord ++ tailWord_5884264) baseStart_5884264 baseEnd_5884264 := by
    simpa [prefixWord, tailWord_5884264, baseEnd_5884264] using wordTrace_append hprefix tailTrace_5884264
  have hstable : (prefixWord ++ tailWord_5884264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884264).length < 2 ^ (prefixWord ++ tailWord_5884264).sum := by decide
  have hdescent : baseEnd_5884264 < baseStart_5884264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884296 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5884296 : Nat := 118140960795 + 5884296 * 2 ^ 59
def prefixEnd_5884296 : Nat := 4983230072969 + 3 ^ 40 * 5884296 * 2
def baseEnd_5884296 : Nat := 3021472161328814898538621

theorem tailTrace_5884296 : CollatzResearch.WordTrace tailWord_5884296 prefixEnd_5884296 3021472161328814898538621 := by
  unfold tailWord_5884296
  simp only [CollatzResearch.WordTrace]
  refine ⟨107308953345104012296568371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143078604460138683062091161 107308953345104012296568371)
  ·
    refine ⟨160963430017656018444852557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107308953345104012296568371 160963430017656018444852557)
    ·
      refine ⟨60361286256621006916819709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160963430017656018444852557 60361286256621006916819709)
      ·
        refine ⟨22635482346232877593807391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60361286256621006916819709 22635482346232877593807391)
        ·
          refine ⟨33953223519349316390711087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22635482346232877593807391 33953223519349316390711087)
          ·
            refine ⟨50929835279023974586066631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33953223519349316390711087 50929835279023974586066631)
            ·
              refine ⟨76394752918535961879099947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50929835279023974586066631 76394752918535961879099947)
              ·
                refine ⟨114592129377803942818649921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76394752918535961879099947 114592129377803942818649921)
                ·
                  refine ⟨85944097033352957113987441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114592129377803942818649921 85944097033352957113987441)
                  ·
                    refine ⟨64458072775014717835490581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85944097033352957113987441 64458072775014717835490581)
                    ·
                      refine ⟨3021472161328814898538621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64458072775014717835490581 3021472161328814898538621)
                      ·
                        rfl

theorem cell23_5884296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5884296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884296 prefixEnd_5884296 := by exact prefixLift 5884296
  have htrace : WordTrace (prefixWord ++ tailWord_5884296) baseStart_5884296 baseEnd_5884296 := by
    simpa [prefixWord, tailWord_5884296, baseEnd_5884296] using wordTrace_append hprefix tailTrace_5884296
  have hstable : (prefixWord ++ tailWord_5884296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884296).length < 2 ^ (prefixWord ++ tailWord_5884296).sum := by decide
  have hdescent : baseEnd_5884296 < baseStart_5884296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884297 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 2, 4]
def baseStart_5884297 : Nat := 118140960795 + 5884297 * 2 ^ 59
def prefixEnd_5884297 : Nat := 4983230072969 + 3 ^ 40 * 5884297 * 2
def baseEnd_5884297 : Nat := 1007157558269823131542039

theorem tailTrace_5884297 : CollatzResearch.WordTrace tailWord_5884297 prefixEnd_5884297 1007157558269823131542039 := by
  unfold tailWord_5884297
  simp only [CollatzResearch.WordTrace]
  refine ⟨214617943163204401763923145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143078628775469601175948763 214617943163204401763923145)
  ·
    refine ⟨160963457372403301322942359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214617943163204401763923145 160963457372403301322942359)
    ·
      refine ⟨241445186058604951984413539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160963457372403301322942359 241445186058604951984413539)
      ·
        refine ⟨362167779087907427976620309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241445186058604951984413539 362167779087907427976620309)
        ·
          refine ⟨16976614644745660686404077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 362167779087907427976620309 16976614644745660686404077)
          ·
            refine ⟨6366230491779622757401529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16976614644745660686404077 6366230491779622757401529)
            ·
              refine ⟨4774672868834717068051147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6366230491779622757401529 4774672868834717068051147)
              ·
                refine ⟨7162009303252075602076721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4774672868834717068051147 7162009303252075602076721)
                ·
                  refine ⟨5371506977439056701557541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162009303252075602076721 5371506977439056701557541)
                  ·
                    refine ⟨1007157558269823131542039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5371506977439056701557541 1007157558269823131542039)
                    ·
                      rfl

theorem cell23_5884297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 4].length) (baseStart_5884297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884297 prefixEnd_5884297 := by exact prefixLift 5884297
  have htrace : WordTrace (prefixWord ++ tailWord_5884297) baseStart_5884297 baseEnd_5884297 := by
    simpa [prefixWord, tailWord_5884297, baseEnd_5884297] using wordTrace_append hprefix tailTrace_5884297
  have hstable : (prefixWord ++ tailWord_5884297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884297).length < 2 ^ (prefixWord ++ tailWord_5884297).sum := by decide
  have hdescent : baseEnd_5884297 < baseStart_5884297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884337 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 3]
def baseStart_5884337 : Nat := 118140960795 + 5884337 * 2 ^ 59
def prefixEnd_5884337 : Nat := 4983230072969 + 3 ^ 40 * 5884337 * 2
def baseEnd_5884337 : Nat := 3021493214035649238125933

theorem tailTrace_5884337 : CollatzResearch.WordTrace tailWord_5884337 prefixEnd_5884337 3021493214035649238125933 := by
  unfold tailWord_5884337
  simp only [CollatzResearch.WordTrace]
  refine ⟨214619402083059488595379265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143079601388706325730252843 214619402083059488595379265)
  ·
    refine ⟨160964551562294616446534449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214619402083059488595379265 160964551562294616446534449)
    ·
      refine ⟨120723413671720962334900837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160964551562294616446534449 120723413671720962334900837)
      ·
        refine ⟨22635640063447680437793907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120723413671720962334900837 22635640063447680437793907)
        ·
          refine ⟨33953460095171520656690861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22635640063447680437793907 33953460095171520656690861)
          ·
            refine ⟨12732547535689320246259073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33953460095171520656690861 12732547535689320246259073)
            ·
              refine ⟨9549410651766990184694305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12732547535689320246259073 9549410651766990184694305)
              ·
                refine ⟨7162057988825242638520729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9549410651766990184694305 7162057988825242638520729)
                ·
                  refine ⟨5371543491618931978890547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162057988825242638520729 5371543491618931978890547)
                  ·
                    refine ⟨8057315237428397968335821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5371543491618931978890547 8057315237428397968335821)
                    ·
                      refine ⟨3021493214035649238125933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8057315237428397968335821 3021493214035649238125933)
                      ·
                        rfl

theorem cell23_5884337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_5884337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884337 prefixEnd_5884337 := by exact prefixLift 5884337
  have htrace : WordTrace (prefixWord ++ tailWord_5884337) baseStart_5884337 baseEnd_5884337 := by
    simpa [prefixWord, tailWord_5884337, baseEnd_5884337] using wordTrace_append hprefix tailTrace_5884337
  have hstable : (prefixWord ++ tailWord_5884337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884337).length < 2 ^ (prefixWord ++ tailWord_5884337).sum := by decide
  have hdescent : baseEnd_5884337 < baseStart_5884337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884346 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_5884346 : Nat := 118140960795 + 5884346 * 2 ^ 59
def prefixEnd_5884346 : Nat := 4983230072969 + 3 ^ 40 * 5884346 * 2
def baseEnd_5884346 : Nat := 3021497835361539702913391

theorem tailTrace_5884346 : CollatzResearch.WordTrace tailWord_5884346 prefixEnd_5884346 3021497835361539702913391 := by
  unfold tailWord_5884346
  simp only [CollatzResearch.WordTrace]
  refine ⟨53654932585006720783114223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143079820226684588754971261 53654932585006720783114223)
  ·
    refine ⟨80482398877510081174671335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53654932585006720783114223 80482398877510081174671335)
    ·
      refine ⟨120723598316265121762007003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80482398877510081174671335 120723598316265121762007003)
      ·
        refine ⟨181085397474397682643010505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120723598316265121762007003 181085397474397682643010505)
        ·
          refine ⟨135814048105798261982257879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181085397474397682643010505 135814048105798261982257879)
          ·
            refine ⟨203721072158697392973386819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135814048105798261982257879 203721072158697392973386819)
            ·
              refine ⟨305581608238046089460080229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203721072158697392973386819 305581608238046089460080229)
              ·
                refine ⟨57296551544633641773765043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305581608238046089460080229 57296551544633641773765043)
                ·
                  refine ⟨85944827316950462660647565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57296551544633641773765043 85944827316950462660647565)
                  ·
                    refine ⟨32229310243856423497742837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85944827316950462660647565 32229310243856423497742837)
                    ·
                      refine ⟨3021497835361539702913391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32229310243856423497742837 3021497835361539702913391)
                      ·
                        rfl

theorem cell23_5884346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_5884346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884346 prefixEnd_5884346 := by exact prefixLift 5884346
  have htrace : WordTrace (prefixWord ++ tailWord_5884346) baseStart_5884346 baseEnd_5884346 := by
    simpa [prefixWord, tailWord_5884346, baseEnd_5884346] using wordTrace_append hprefix tailTrace_5884346
  have hstable : (prefixWord ++ tailWord_5884346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884346).length < 2 ^ (prefixWord ++ tailWord_5884346).sum := by decide
  have hdescent : baseEnd_5884346 < baseStart_5884346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884360 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_5884360 : Nat := 118140960795 + 5884360 * 2 ^ 59
def prefixEnd_5884360 : Nat := 4983230072969 + 3 ^ 40 * 5884360 * 2
def baseEnd_5884360 : Nat := 3021505024090702648138327

theorem tailTrace_5884360 : CollatzResearch.WordTrace tailWord_5884360 prefixEnd_5884360 3021505024090702648138327 := by
  unfold tailWord_5884360
  simp only [CollatzResearch.WordTrace]
  refine ⟨107310120480988081761733267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143080160641317442348977689 107310120480988081761733267)
  ·
    refine ⟨160965180721482122642599901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107310120480988081761733267 160965180721482122642599901)
    ·
      refine ⟨60361942770555795990974963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160965180721482122642599901 60361942770555795990974963)
      ·
        refine ⟨90542914155833693986462445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60361942770555795990974963 90542914155833693986462445)
        ·
          refine ⟨33953592808437635244923417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90542914155833693986462445 33953592808437635244923417)
          ·
            refine ⟨25465194606328226433692563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33953592808437635244923417 25465194606328226433692563)
            ·
              refine ⟨38197791909492339650538845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25465194606328226433692563 38197791909492339650538845)
              ·
                refine ⟨14324171966059627368952067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38197791909492339650538845 14324171966059627368952067)
                ·
                  refine ⟨21486257949089441053428101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14324171966059627368952067 21486257949089441053428101)
                  ·
                    refine ⟨4028673365454270197517769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21486257949089441053428101 4028673365454270197517769)
                    ·
                      refine ⟨3021505024090702648138327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028673365454270197517769 3021505024090702648138327)
                      ·
                        rfl

theorem cell23_5884360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_5884360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884360 prefixEnd_5884360 := by exact prefixLift 5884360
  have htrace : WordTrace (prefixWord ++ tailWord_5884360) baseStart_5884360 baseEnd_5884360 := by
    simpa [prefixWord, tailWord_5884360, baseEnd_5884360] using wordTrace_append hprefix tailTrace_5884360
  have hstable : (prefixWord ++ tailWord_5884360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884360).length < 2 ^ (prefixWord ++ tailWord_5884360).sum := by decide
  have hdescent : baseEnd_5884360 < baseStart_5884360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884376 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_5884376 : Nat := 118140960795 + 5884376 * 2 ^ 59
def prefixEnd_5884376 : Nat := 4983230072969 + 3 ^ 40 * 5884376 * 2
def baseEnd_5884376 : Nat := 3021513239781174585538253

theorem tailTrace_5884376 : CollatzResearch.WordTrace tailWord_5884376 prefixEnd_5884376 3021513239781174585538253 := by
  unfold tailWord_5884376
  simp only [CollatzResearch.WordTrace]
  refine ⟨107310412264959099128024491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143080549686612132170699321 107310412264959099128024491)
  ·
    refine ⟨160965618397438648692036737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107310412264959099128024491 160965618397438648692036737)
    ·
      refine ⟨120724213798078986519027553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160965618397438648692036737 120724213798078986519027553)
      ·
        refine ⟨90543160348559239889270665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120724213798078986519027553 90543160348559239889270665)
        ·
          refine ⟨67907370261419429916952999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90543160348559239889270665 67907370261419429916952999)
          ·
            refine ⟨101861055392129144875429499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67907370261419429916952999 101861055392129144875429499)
            ·
              refine ⟨152791583088193717313144249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101861055392129144875429499 152791583088193717313144249)
              ·
                refine ⟨114593687316145287984858187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152791583088193717313144249 114593687316145287984858187)
                ·
                  refine ⟨171890530974217931977287281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114593687316145287984858187 171890530974217931977287281)
                  ·
                    refine ⟨128917898230663448982965461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 171890530974217931977287281 128917898230663448982965461)
                    ·
                      refine ⟨3021513239781174585538253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128917898230663448982965461 3021513239781174585538253)
                      ·
                        rfl

theorem cell23_5884376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_5884376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884376 prefixEnd_5884376 := by exact prefixLift 5884376
  have htrace : WordTrace (prefixWord ++ tailWord_5884376) baseStart_5884376 baseEnd_5884376 := by
    simpa [prefixWord, tailWord_5884376, baseEnd_5884376] using wordTrace_append hprefix tailTrace_5884376
  have hstable : (prefixWord ++ tailWord_5884376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884376).length < 2 ^ (prefixWord ++ tailWord_5884376).sum := by decide
  have hdescent : baseEnd_5884376 < baseStart_5884376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884394 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_5884394 : Nat := 118140960795 + 5884394 * 2 ^ 59
def prefixEnd_5884394 : Nat := 4983230072969 + 3 ^ 40 * 5884394 * 2
def baseEnd_5884394 : Nat := 3021522482432955515113171

theorem tailTrace_5884394 : CollatzResearch.WordTrace tailWord_5884394 prefixEnd_5884394 3021522482432955515113171 := by
  unfold tailWord_5884394
  simp only [CollatzResearch.WordTrace]
  refine ⟨53655370260963246832551059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143080987362568658220136157 53655370260963246832551059)
  ·
    refine ⟨80483055391444870248826589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53655370260963246832551059 80483055391444870248826589)
    ·
      refine ⟨30181145771791826343309971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80483055391444870248826589 30181145771791826343309971)
      ·
        refine ⟨45271718657687739514964957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30181145771791826343309971 45271718657687739514964957)
        ·
          refine ⟨16976894496632902318111859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45271718657687739514964957 16976894496632902318111859)
          ·
            refine ⟨25465341744949353477167789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16976894496632902318111859 25465341744949353477167789)
            ·
              refine ⟨9549503154356007553937921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25465341744949353477167789 9549503154356007553937921)
              ·
                refine ⟨7162127365767005665453441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9549503154356007553937921 7162127365767005665453441)
                ·
                  refine ⟨5371595524325254249090081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162127365767005665453441 5371595524325254249090081)
                  ·
                    refine ⟨4028696643243940686817561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5371595524325254249090081 4028696643243940686817561)
                    ·
                      refine ⟨3021522482432955515113171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028696643243940686817561 3021522482432955515113171)
                      ·
                        rfl

theorem cell23_5884394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_5884394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884394 prefixEnd_5884394 := by exact prefixLift 5884394
  have htrace : WordTrace (prefixWord ++ tailWord_5884394) baseStart_5884394 baseEnd_5884394 := by
    simpa [prefixWord, tailWord_5884394, baseEnd_5884394] using wordTrace_append hprefix tailTrace_5884394
  have hstable : (prefixWord ++ tailWord_5884394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884394).length < 2 ^ (prefixWord ++ tailWord_5884394).sum := by decide
  have hdescent : baseEnd_5884394 < baseStart_5884394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884483 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 3]
def baseStart_5884483 : Nat := 118140960795 + 5884483 * 2 ^ 59
def prefixEnd_5884483 : Nat := 4983230072969 + 3 ^ 40 * 5884483 * 2
def baseEnd_5884483 : Nat := 3021568182211205666900261

theorem tailTrace_5884483 : CollatzResearch.WordTrace tailWord_5884483 prefixEnd_5884483 3021568182211205666900261 := by
  unfold tailWord_5884483
  simp only [CollatzResearch.WordTrace]
  refine ⟨214624727140530555530194103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143083151427020370353462735 214624727140530555530194103)
  ·
    refine ⟨321937090710795833295291155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214624727140530555530194103 321937090710795833295291155)
    ·
      refine ⟨482905636066193749942936733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321937090710795833295291155 482905636066193749942936733)
      ·
        refine ⟨181089613524822656228601275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 482905636066193749942936733 181089613524822656228601275)
        ·
          refine ⟨271634420287233984342901913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181089613524822656228601275 271634420287233984342901913)
          ·
            refine ⟨203725815215425488257176435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271634420287233984342901913 203725815215425488257176435)
            ·
              refine ⟨305588722823138232385764653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203725815215425488257176435 305588722823138232385764653)
              ·
                refine ⟨114595771058676837144661745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305588722823138232385764653 114595771058676837144661745)
                ·
                  refine ⟨85946828294007627858496309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114595771058676837144661745 85946828294007627858496309)
                  ·
                    refine ⟨8057515152563215111734029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85946828294007627858496309 8057515152563215111734029)
                    ·
                      refine ⟨3021568182211205666900261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8057515152563215111734029 3021568182211205666900261)
                      ·
                        rfl

theorem cell23_5884483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_5884483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884483 prefixEnd_5884483 := by exact prefixLift 5884483
  have htrace : WordTrace (prefixWord ++ tailWord_5884483) baseStart_5884483 baseEnd_5884483 := by
    simpa [prefixWord, tailWord_5884483, baseEnd_5884483] using wordTrace_append hprefix tailTrace_5884483
  have hstable : (prefixWord ++ tailWord_5884483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884483).length < 2 ^ (prefixWord ++ tailWord_5884483).sum := by decide
  have hdescent : baseEnd_5884483 < baseStart_5884483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884487 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_5884487 : Nat := 118140960795 + 5884487 * 2 ^ 59
def prefixEnd_5884487 : Nat := 4983230072969 + 3 ^ 40 * 5884487 * 2
def baseEnd_5884487 : Nat := 3021570236133823651250243

theorem tailTrace_5884487 : CollatzResearch.WordTrace tailWord_5884487 prefixEnd_5884487 3021570236133823651250243 := by
  unfold tailWord_5884487
  simp only [CollatzResearch.WordTrace]
  refine ⟨214624873032516064213339715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143083248688344042808893143 214624873032516064213339715)
  ·
    refine ⟨321937309548774096320009573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214624873032516064213339715 321937309548774096320009573)
    ·
      refine ⟨60363245540395143060001795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321937309548774096320009573 60363245540395143060001795)
      ·
        refine ⟨90544868310592714590002693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60363245540395143060001795 90544868310592714590002693)
        ·
          refine ⟨16977162808236133985625505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90544868310592714590002693 16977162808236133985625505)
          ·
            refine ⟨12732872106177100489219129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16977162808236133985625505 12732872106177100489219129)
            ·
              refine ⟨9549654079632825366914347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12732872106177100489219129 9549654079632825366914347)
              ·
                refine ⟨14324481119449238050371521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9549654079632825366914347 14324481119449238050371521)
                ·
                  refine ⟨10743360839586928537778641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14324481119449238050371521 10743360839586928537778641)
                  ·
                    refine ⟨8057520629690196403333981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10743360839586928537778641 8057520629690196403333981)
                    ·
                      refine ⟨3021570236133823651250243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8057520629690196403333981 3021570236133823651250243)
                      ·
                        rfl

theorem cell23_5884487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_5884487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884487 prefixEnd_5884487 := by exact prefixLift 5884487
  have htrace : WordTrace (prefixWord ++ tailWord_5884487) baseStart_5884487 baseEnd_5884487 := by
    simpa [prefixWord, tailWord_5884487, baseEnd_5884487] using wordTrace_append hprefix tailTrace_5884487
  have hstable : (prefixWord ++ tailWord_5884487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884487).length < 2 ^ (prefixWord ++ tailWord_5884487).sum := by decide
  have hdescent : baseEnd_5884487 < baseStart_5884487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884540 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_5884540 : Nat := 118140960795 + 5884540 * 2 ^ 59
def prefixEnd_5884540 : Nat := 4983230072969 + 3 ^ 40 * 5884540 * 2
def baseEnd_5884540 : Nat := 3021597450608511943887499

theorem tailTrace_5884540 : CollatzResearch.WordTrace tailWord_5884540 prefixEnd_5884540 3021597450608511943887499 := by
  unfold tailWord_5884540
  simp only [CollatzResearch.WordTrace]
  refine ⟨107313403050662027132509537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143084537400882702843346049 107313403050662027132509537)
  ·
    refine ⟨80485052287996520349382153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107313403050662027132509537 80485052287996520349382153)
    ·
      refine ⟨60363789215997390262036615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80485052287996520349382153 60363789215997390262036615)
      ·
        refine ⟨90545683823996085393054923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60363789215997390262036615 90545683823996085393054923)
        ·
          refine ⟨135818525735994128089582385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90545683823996085393054923 135818525735994128089582385)
          ·
            refine ⟨101863894301995596067186789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135818525735994128089582385 101863894301995596067186789)
            ·
              refine ⟨19099480181624174262597523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101863894301995596067186789 19099480181624174262597523)
              ·
                refine ⟨28649220272436261393896285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19099480181624174262597523 28649220272436261393896285)
                ·
                  refine ⟨10743457602163598022711107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28649220272436261393896285 10743457602163598022711107)
                  ·
                    refine ⟨16115186403245397034066661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10743457602163598022711107 16115186403245397034066661)
                    ·
                      refine ⟨3021597450608511943887499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16115186403245397034066661 3021597450608511943887499)
                      ·
                        rfl

theorem cell23_5884540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_5884540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884540 prefixEnd_5884540 := by exact prefixLift 5884540
  have htrace : WordTrace (prefixWord ++ tailWord_5884540) baseStart_5884540 baseEnd_5884540 := by
    simpa [prefixWord, tailWord_5884540, baseEnd_5884540] using wordTrace_append hprefix tailTrace_5884540
  have hstable : (prefixWord ++ tailWord_5884540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884540).length < 2 ^ (prefixWord ++ tailWord_5884540).sum := by decide
  have hdescent : baseEnd_5884540 < baseStart_5884540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884543 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_5884543 : Nat := 118140960795 + 5884543 * 2 ^ 59
def prefixEnd_5884543 : Nat := 4983230072969 + 3 ^ 40 * 5884543 * 2
def baseEnd_5884543 : Nat := 3021598991050475432149985

theorem tailTrace_5884543 : CollatzResearch.WordTrace tailWord_5884543 prefixEnd_5884543 3021598991050475432149985 := by
  unfold tailWord_5884543
  simp only [CollatzResearch.WordTrace]
  refine ⟨214626915520313185777378283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143084610346875457184918855 214626915520313185777378283)
  ·
    refine ⟨321940373280469778666067425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214626915520313185777378283 321940373280469778666067425)
    ·
      refine ⟨241455279960352333999550569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321940373280469778666067425 241455279960352333999550569)
      ·
        refine ⟨181091459970264250499662927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241455279960352333999550569 181091459970264250499662927)
        ·
          refine ⟨271637189955396375749494391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181091459970264250499662927 271637189955396375749494391)
          ·
            refine ⟨407455784933094563624241587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271637189955396375749494391 407455784933094563624241587)
            ·
              refine ⟨611183677399641845436362381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407455784933094563624241587 611183677399641845436362381)
              ·
                refine ⟨229193879024865692038635893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611183677399641845436362381 229193879024865692038635893)
                ·
                  refine ⟨21486926158581158628622115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229193879024865692038635893 21486926158581158628622115)
                  ·
                    refine ⟨32230389237871737942933173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21486926158581158628622115 32230389237871737942933173)
                    ·
                      refine ⟨3021598991050475432149985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32230389237871737942933173 3021598991050475432149985)
                      ·
                        rfl

theorem cell23_5884543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_5884543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884543 prefixEnd_5884543 := by exact prefixLift 5884543
  have htrace : WordTrace (prefixWord ++ tailWord_5884543) baseStart_5884543 baseEnd_5884543 := by
    simpa [prefixWord, tailWord_5884543, baseEnd_5884543] using wordTrace_append hprefix tailTrace_5884543
  have hstable : (prefixWord ++ tailWord_5884543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884543).length < 2 ^ (prefixWord ++ tailWord_5884543).sum := by decide
  have hdescent : baseEnd_5884543 < baseStart_5884543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884544 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 2, 3, 2]
def baseStart_5884544 : Nat := 118140960795 + 5884544 * 2 ^ 59
def prefixEnd_5884544 : Nat := 4983230072969 + 3 ^ 40 * 5884544 * 2
def baseEnd_5884544 : Nat := 3021599504531129928237481

theorem tailTrace_5884544 : CollatzResearch.WordTrace tailWord_5884544 prefixEnd_5884544 3021599504531129928237481 := by
  unfold tailWord_5884544
  simp only [CollatzResearch.WordTrace]
  refine ⟨107313475996654781474082343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143084634662206375298776457 107313475996654781474082343)
  ·
    refine ⟨160970213994982172211123515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107313475996654781474082343 160970213994982172211123515)
    ·
      refine ⟨241455320992473258316685273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160970213994982172211123515 241455320992473258316685273)
      ·
        refine ⟨181091490744354943737513955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241455320992473258316685273 181091490744354943737513955)
        ·
          refine ⟨271637236116532415606270933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181091490744354943737513955 271637236116532415606270933)
          ·
            refine ⟨6366497721481228490771975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 271637236116532415606270933 6366497721481228490771975)
            ·
              refine ⟨9549746582221842736157963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6366497721481228490771975 9549746582221842736157963)
              ·
                refine ⟨14324619873332764104236945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9549746582221842736157963 14324619873332764104236945)
                ·
                  refine ⟨10743464904999573078177709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14324619873332764104236945 10743464904999573078177709)
                  ·
                    refine ⟨4028799339374839904316641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10743464904999573078177709 4028799339374839904316641)
                    ·
                      refine ⟨3021599504531129928237481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028799339374839904316641 3021599504531129928237481)
                      ·
                        rfl

theorem cell23_5884544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_5884544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884544 prefixEnd_5884544 := by exact prefixLift 5884544
  have htrace : WordTrace (prefixWord ++ tailWord_5884544) baseStart_5884544 baseEnd_5884544 := by
    simpa [prefixWord, tailWord_5884544, baseEnd_5884544] using wordTrace_append hprefix tailTrace_5884544
  have hstable : (prefixWord ++ tailWord_5884544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884544).length < 2 ^ (prefixWord ++ tailWord_5884544).sum := by decide
  have hdescent : baseEnd_5884544 < baseStart_5884544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884553 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_5884553 : Nat := 118140960795 + 5884553 * 2 ^ 59
def prefixEnd_5884553 : Nat := 4983230072969 + 3 ^ 40 * 5884553 * 2
def baseEnd_5884553 : Nat := 3021604125857020393024939

theorem tailTrace_5884553 : CollatzResearch.WordTrace tailWord_5884553 prefixEnd_5884553 3021604125857020393024939 := by
  unfold tailWord_5884553
  simp only [CollatzResearch.WordTrace]
  refine ⟨214627280250276957485242313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143084853500184638323494875 214627280250276957485242313)
  ·
    refine ⟨160970460187707718113931735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214627280250276957485242313 160970460187707718113931735)
    ·
      refine ⟨241455690281561577170897603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160970460187707718113931735 241455690281561577170897603)
      ·
        refine ⟨362183535422342365756346405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241455690281561577170897603 362183535422342365756346405)
        ·
          refine ⟨67909412891689193579314951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362183535422342365756346405 67909412891689193579314951)
          ·
            refine ⟨101864119337533790368972427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67909412891689193579314951 101864119337533790368972427)
            ·
              refine ⟨152796179006300685553458641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101864119337533790368972427 152796179006300685553458641)
              ·
                refine ⟨114597134254725514165093981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152796179006300685553458641 114597134254725514165093981)
                ·
                  refine ⟨42973925345522067811910243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114597134254725514165093981 42973925345522067811910243)
                  ·
                    refine ⟨64460888018283101717865365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42973925345522067811910243 64460888018283101717865365)
                    ·
                      refine ⟨3021604125857020393024939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64460888018283101717865365 3021604125857020393024939)
                      ·
                        rfl

theorem cell23_5884553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_5884553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884553 prefixEnd_5884553 := by exact prefixLift 5884553
  have htrace : WordTrace (prefixWord ++ tailWord_5884553) baseStart_5884553 baseEnd_5884553 := by
    simpa [prefixWord, tailWord_5884553, baseEnd_5884553] using wordTrace_append hprefix tailTrace_5884553
  have hstable : (prefixWord ++ tailWord_5884553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884553).length < 2 ^ (prefixWord ++ tailWord_5884553).sum := by decide
  have hdescent : baseEnd_5884553 < baseStart_5884553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884577 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_5884577 : Nat := 118140960795 + 5884577 * 2 ^ 59
def prefixEnd_5884577 : Nat := 4983230072969 + 3 ^ 40 * 5884577 * 2
def baseEnd_5884577 : Nat := 3021616449392728299124829

theorem tailTrace_5884577 : CollatzResearch.WordTrace tailWord_5884577 prefixEnd_5884577 3021616449392728299124829 := by
  unfold tailWord_5884577
  simp only [CollatzResearch.WordTrace]
  refine ⟨214628155602190009584115985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143085437068126673056077323 214628155602190009584115985)
  ·
    refine ⟨160971116701642507188086989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214628155602190009584115985 160971116701642507188086989)
    ·
      refine ⟨60364168763115940195532621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160971116701642507188086989 60364168763115940195532621)
      ·
        refine ⟨22636563286168477573324733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60364168763115940195532621 22636563286168477573324733)
        ·
          refine ⟨8488711232313179089996775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22636563286168477573324733 8488711232313179089996775)
          ·
            refine ⟨12733066848469768634995163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488711232313179089996775 12733066848469768634995163)
            ·
              refine ⟨19099600272704652952492745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12733066848469768634995163 19099600272704652952492745)
              ·
                refine ⟨14324700204528489714369559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19099600272704652952492745 14324700204528489714369559)
                ·
                  refine ⟨21487050306792734571554339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14324700204528489714369559 21487050306792734571554339)
                  ·
                    refine ⟨32230575460189101857331509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21487050306792734571554339 32230575460189101857331509)
                    ·
                      refine ⟨3021616449392728299124829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32230575460189101857331509 3021616449392728299124829)
                      ·
                        rfl

theorem cell23_5884577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_5884577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884577 prefixEnd_5884577 := by exact prefixLift 5884577
  have htrace : WordTrace (prefixWord ++ tailWord_5884577) baseStart_5884577 baseEnd_5884577 := by
    simpa [prefixWord, tailWord_5884577, baseEnd_5884577] using wordTrace_append hprefix tailTrace_5884577
  have hstable : (prefixWord ++ tailWord_5884577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884577).length < 2 ^ (prefixWord ++ tailWord_5884577).sum := by decide
  have hdescent : baseEnd_5884577 < baseStart_5884577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884597 : List Nat := [1, 3, 3, 3, 1, 1, 4, 7]
def baseStart_5884597 : Nat := 118140960795 + 5884597 * 2 ^ 59
def prefixEnd_5884597 : Nat := 4983230072969 + 3 ^ 40 * 5884597 * 2
def baseEnd_5884597 : Nat := 111912100703919193365731

theorem tailTrace_5884597 : CollatzResearch.WordTrace tailWord_5884597 prefixEnd_5884597 111912100703919193365731 := by
  unfold tailWord_5884597
  simp only [CollatzResearch.WordTrace]
  refine ⟨214628885062117552999844045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143085923374745035333229363 214628885062117552999844045)
  ·
    refine ⟨80485831898294082374941517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214628885062117552999844045 80485831898294082374941517)
    ·
      refine ⟨30182186961860280890603069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80485831898294082374941517 30182186961860280890603069)
      ·
        refine ⟨11318320110697605333976151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30182186961860280890603069 11318320110697605333976151)
        ·
          refine ⟨16977480166046408000964227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11318320110697605333976151 16977480166046408000964227)
          ·
            refine ⟨25466220249069612001446341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16977480166046408000964227 25466220249069612001446341)
            ·
              refine ⟨4774916296700552250271189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25466220249069612001446341 4774916296700552250271189)
              ·
                refine ⟨111912100703919193365731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4774916296700552250271189 111912100703919193365731)
                ·
                  rfl

theorem cell23_5884597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 7].length) (baseStart_5884597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884597 prefixEnd_5884597 := by exact prefixLift 5884597
  have htrace : WordTrace (prefixWord ++ tailWord_5884597) baseStart_5884597 baseEnd_5884597 := by
    simpa [prefixWord, tailWord_5884597, baseEnd_5884597] using wordTrace_append hprefix tailTrace_5884597
  have hstable : (prefixWord ++ tailWord_5884597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884597).length < 2 ^ (prefixWord ++ tailWord_5884597).sum := by decide
  have hdescent : baseEnd_5884597 < baseStart_5884597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884607 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 3]
def baseStart_5884607 : Nat := 118140960795 + 5884607 * 2 ^ 59
def prefixEnd_5884607 : Nat := 4983230072969 + 3 ^ 40 * 5884607 * 2
def baseEnd_5884607 : Nat := 3021631853812363181749691

theorem tailTrace_5884607 : CollatzResearch.WordTrace tailWord_5884607 prefixEnd_5884607 3021631853812363181749691 := by
  unfold tailWord_5884607
  simp only [CollatzResearch.WordTrace]
  refine ⟨214629249792081324707708075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143086166528054216471805383 214629249792081324707708075)
  ·
    refine ⟨321943874688121987061562113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214629249792081324707708075 321943874688121987061562113)
    ·
      refine ⟨241457906016091490296171585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321943874688121987061562113 241457906016091490296171585)
      ·
        refine ⟨181093429512068617722128689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241457906016091490296171585 181093429512068617722128689)
        ·
          refine ⟨135820072134051463291596517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181093429512068617722128689 135820072134051463291596517)
          ·
            refine ⟨25466263525134649367174347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135820072134051463291596517 25466263525134649367174347)
            ·
              refine ⟨38199395287701974050761521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25466263525134649367174347 38199395287701974050761521)
              ·
                refine ⟨28649546465776480538071141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38199395287701974050761521 28649546465776480538071141)
                ·
                  refine ⟨5371789962333090100888339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28649546465776480538071141 5371789962333090100888339)
                  ·
                    refine ⟨8057684943499635151332509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5371789962333090100888339 8057684943499635151332509)
                    ·
                      refine ⟨3021631853812363181749691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8057684943499635151332509 3021631853812363181749691)
                      ·
                        rfl

theorem cell23_5884607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_5884607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884607 prefixEnd_5884607 := by exact prefixLift 5884607
  have htrace : WordTrace (prefixWord ++ tailWord_5884607) baseStart_5884607 baseEnd_5884607 := by
    simpa [prefixWord, tailWord_5884607, baseEnd_5884607] using wordTrace_append hprefix tailTrace_5884607
  have hstable : (prefixWord ++ tailWord_5884607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884607).length < 2 ^ (prefixWord ++ tailWord_5884607).sum := by decide
  have hdescent : baseEnd_5884607 < baseStart_5884607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884608 : List Nat := [2, 1, 1, 2, 4, 4, 1, 3, 1, 2, 2]
def baseStart_5884608 : Nat := 118140960795 + 5884608 * 2 ^ 59
def prefixEnd_5884608 : Nat := 4983230072969 + 3 ^ 40 * 5884608 * 2
def baseEnd_5884608 : Nat := 3021632367293017677837187

theorem tailTrace_5884608 : CollatzResearch.WordTrace tailWord_5884608 prefixEnd_5884608 3021632367293017677837187 := by
  unfold tailWord_5884608
  simp only [CollatzResearch.WordTrace]
  refine ⟨107314643132538850939247239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143086190843385134585662985 107314643132538850939247239)
  ·
    refine ⟨160971964698808276408870859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107314643132538850939247239 160971964698808276408870859)
    ·
      refine ⟨241457947048212414613306289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160971964698808276408870859 241457947048212414613306289)
      ·
        refine ⟨181093460286159310959979717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241457947048212414613306289 181093460286159310959979717)
        ·
          refine ⟨33955023803654870804996197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181093460286159310959979717 33955023803654870804996197)
          ·
            refine ⟨6366566963185288275936787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33955023803654870804996197 6366566963185288275936787)
            ·
              refine ⟨9549850444777932413905181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6366566963185288275936787 9549850444777932413905181)
              ·
                refine ⟨3581193916791724655214443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9549850444777932413905181 3581193916791724655214443)
                ·
                  refine ⟨5371790875187586982821665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581193916791724655214443 5371790875187586982821665)
                  ·
                    refine ⟨4028843156390690237116249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5371790875187586982821665 4028843156390690237116249)
                    ·
                      refine ⟨3021632367293017677837187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028843156390690237116249 3021632367293017677837187)
                      ·
                        rfl

theorem cell23_5884608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 2, 2].length) (baseStart_5884608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884608 prefixEnd_5884608 := by exact prefixLift 5884608
  have htrace : WordTrace (prefixWord ++ tailWord_5884608) baseStart_5884608 baseEnd_5884608 := by
    simpa [prefixWord, tailWord_5884608, baseEnd_5884608] using wordTrace_append hprefix tailTrace_5884608
  have hstable : (prefixWord ++ tailWord_5884608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884608).length < 2 ^ (prefixWord ++ tailWord_5884608).sum := by decide
  have hdescent : baseEnd_5884608 < baseStart_5884608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884641 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_5884641 : Nat := 118140960795 + 5884641 * 2 ^ 59
def prefixEnd_5884641 : Nat := 4983230072969 + 3 ^ 40 * 5884641 * 2
def baseEnd_5884641 : Nat := 3021649312154616048724535

theorem tailTrace_5884641 : CollatzResearch.WordTrace tailWord_5884641 prefixEnd_5884641 3021649312154616048724535 := by
  unfold tailWord_5884641
  simp only [CollatzResearch.WordTrace]
  refine ⟨214630489873958148514445777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143086993249305432342963851 214630489873958148514445777)
  ·
    refine ⟨160972867405468611385834333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214630489873958148514445777 160972867405468611385834333)
    ·
      refine ⟨60364825277050729269687875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160972867405468611385834333 60364825277050729269687875)
      ·
        refine ⟨90547237915576093904531813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60364825277050729269687875 90547237915576093904531813)
        ·
          refine ⟨16977607109170517607099715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90547237915576093904531813 16977607109170517607099715)
          ·
            refine ⟨25466410663755776410649573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16977607109170517607099715 25466410663755776410649573)
            ·
              refine ⟨4774951999454208076996795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25466410663755776410649573 4774951999454208076996795)
              ·
                refine ⟨7162427999181312115495193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4774951999454208076996795 7162427999181312115495193)
                ·
                  refine ⟨5371820999385984086621395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162427999181312115495193 5371820999385984086621395)
                  ·
                    refine ⟨8057731499078976129932093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5371820999385984086621395 8057731499078976129932093)
                    ·
                      refine ⟨3021649312154616048724535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8057731499078976129932093 3021649312154616048724535)
                      ·
                        rfl

theorem cell23_5884641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_5884641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884641 prefixEnd_5884641 := by exact prefixLift 5884641
  have htrace : WordTrace (prefixWord ++ tailWord_5884641) baseStart_5884641 baseEnd_5884641 := by
    simpa [prefixWord, tailWord_5884641, baseEnd_5884641] using wordTrace_append hprefix tailTrace_5884641
  have hstable : (prefixWord ++ tailWord_5884641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884641).length < 2 ^ (prefixWord ++ tailWord_5884641).sum := by decide
  have hdescent : baseEnd_5884641 < baseStart_5884641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884687 : List Nat := [1, 1, 2, 1, 1, 1, 7, 4, 5]
def baseStart_5884687 : Nat := 118140960795 + 5884687 * 2 ^ 59
def prefixEnd_5884687 : Nat := 4983230072969 + 3 ^ 40 * 5884687 * 2
def baseEnd_5884687 : Nat := 335741436918302540972147

theorem tailTrace_5884687 : CollatzResearch.WordTrace tailWord_5884687 prefixEnd_5884687 335741436918302540972147 := by
  unfold tailWord_5884687
  simp only [CollatzResearch.WordTrace]
  refine ⟨214632167631791498370620315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143088111754527665580413543 214632167631791498370620315)
  ·
    refine ⟨321948251447687247555930473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214632167631791498370620315 321948251447687247555930473)
    ·
      refine ⟨241461188585765435666947855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321948251447687247555930473 241461188585765435666947855)
      ·
        refine ⟨362191782878648153500421783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241461188585765435666947855 362191782878648153500421783)
        ·
          refine ⟨543287674317972230250632675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362191782878648153500421783 543287674317972230250632675)
          ·
            refine ⟨814931511476958345375949013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543287674317972230250632675 814931511476958345375949013)
            ·
              refine ⟨19099957300241211219748805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 814931511476958345375949013 19099957300241211219748805)
              ·
                refine ⟨3581241993795227103702901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19099957300241211219748805 3581241993795227103702901)
                ·
                  refine ⟨335741436918302540972147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3581241993795227103702901 335741436918302540972147)
                  ·
                    rfl

theorem cell23_5884687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 5].length) (baseStart_5884687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884687 prefixEnd_5884687 := by exact prefixLift 5884687
  have htrace : WordTrace (prefixWord ++ tailWord_5884687) baseStart_5884687 baseEnd_5884687 := by
    simpa [prefixWord, tailWord_5884687, baseEnd_5884687] using wordTrace_append hprefix tailTrace_5884687
  have hstable : (prefixWord ++ tailWord_5884687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884687).length < 2 ^ (prefixWord ++ tailWord_5884687).sum := by decide
  have hdescent : baseEnd_5884687 < baseStart_5884687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884707 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 4, 5, 2]
def baseStart_5884707 : Nat := 118140960795 + 5884707 * 2 ^ 59
def prefixEnd_5884707 : Nat := 4983230072969 + 3 ^ 40 * 5884707 * 2
def baseEnd_5884707 : Nat := 3021683201877812790499231

theorem tailTrace_5884707 : CollatzResearch.WordTrace tailWord_5884707 prefixEnd_5884707 3021683201877812790499231 := by
  unfold tailWord_5884707
  simp only [CollatzResearch.WordTrace]
  refine ⟨214632897091719041786348375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143088598061146027857565583 214632897091719041786348375)
  ·
    refine ⟨321949345637578562679522563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214632897091719041786348375 321949345637578562679522563)
    ·
      refine ⟨482924018456367844019283845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321949345637578562679522563 482924018456367844019283845)
      ·
        refine ⟨90548253460568970753615721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 482924018456367844019283845 90548253460568970753615721)
        ·
          refine ⟨67911190095426728065211791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90548253460568970753615721 67911190095426728065211791)
          ·
            refine ⟨101866785143140092097817687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67911190095426728065211791 101866785143140092097817687)
            ·
              refine ⟨152800177714710138146726531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101866785143140092097817687 152800177714710138146726531)
              ·
                refine ⟨229200266572065207220089797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152800177714710138146726531 229200266572065207220089797)
                ·
                  refine ⟨42975049982262226353766837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229200266572065207220089797 42975049982262226353766837)
                  ·
                    refine ⟨4028910935837083720665641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42975049982262226353766837 4028910935837083720665641)
                    ·
                      refine ⟨3021683201877812790499231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028910935837083720665641 3021683201877812790499231)
                      ·
                        rfl

theorem cell23_5884707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_5884707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884707 prefixEnd_5884707 := by exact prefixLift 5884707
  have htrace : WordTrace (prefixWord ++ tailWord_5884707) baseStart_5884707 baseEnd_5884707 := by
    simpa [prefixWord, tailWord_5884707, baseEnd_5884707] using wordTrace_append hprefix tailTrace_5884707
  have hstable : (prefixWord ++ tailWord_5884707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884707).length < 2 ^ (prefixWord ++ tailWord_5884707).sum := by decide
  have hdescent : baseEnd_5884707 < baseStart_5884707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884754 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_5884754 : Nat := 118140960795 + 5884754 * 2 ^ 59
def prefixEnd_5884754 : Nat := 4983230072969 + 3 ^ 40 * 5884754 * 2
def baseEnd_5884754 : Nat := 3021707335468574106611515

theorem tailTrace_5884754 : CollatzResearch.WordTrace tailWord_5884754 prefixEnd_5884754 3021707335468574106611515 := by
  unfold tailWord_5884754
  simp only [CollatzResearch.WordTrace]
  refine ⟨53658652830637192203327329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143089740881699179208872877 53658652830637192203327329)
  ·
    refine ⟨40243989622977894152495497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53658652830637192203327329 40243989622977894152495497)
    ·
      refine ⟨30182992217233420614371623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40243989622977894152495497 30182992217233420614371623)
      ·
        refine ⟨45274488325850130921557435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30182992217233420614371623 45274488325850130921557435)
        ·
          refine ⟨67911732488775196382336153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45274488325850130921557435 67911732488775196382336153)
          ·
            refine ⟨50933799366581397286752115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67911732488775196382336153 50933799366581397286752115)
            ·
              refine ⟨76400699049872095930128173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50933799366581397286752115 76400699049872095930128173)
              ·
                refine ⟨28650262143702035973798065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76400699049872095930128173 28650262143702035973798065)
                ·
                  refine ⟨21487696607776526980348549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28650262143702035973798065 21487696607776526980348549)
                  ·
                    refine ⟨4028943113958098808815353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21487696607776526980348549 4028943113958098808815353)
                    ·
                      refine ⟨3021707335468574106611515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028943113958098808815353 3021707335468574106611515)
                      ·
                        rfl

theorem cell23_5884754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_5884754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884754 prefixEnd_5884754 := by exact prefixLift 5884754
  have htrace : WordTrace (prefixWord ++ tailWord_5884754) baseStart_5884754 baseEnd_5884754 := by
    simpa [prefixWord, tailWord_5884754, baseEnd_5884754] using wordTrace_append hprefix tailTrace_5884754
  have hstable : (prefixWord ++ tailWord_5884754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884754).length < 2 ^ (prefixWord ++ tailWord_5884754).sum := by decide
  have hdescent : baseEnd_5884754 < baseStart_5884754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884757 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_5884757 : Nat := 118140960795 + 5884757 * 2 ^ 59
def prefixEnd_5884757 : Nat := 4983230072969 + 3 ^ 40 * 5884757 * 2
def baseEnd_5884757 : Nat := 3021708875910537594874001

theorem tailTrace_5884757 : CollatzResearch.WordTrace tailWord_5884757 prefixEnd_5884757 3021708875910537594874001 := by
  unfold tailWord_5884757
  simp only [CollatzResearch.WordTrace]
  refine ⟨214634720741537900325668525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143089813827691933550445683 214634720741537900325668525)
  ·
    refine ⟨80488020278076712622125697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214634720741537900325668525 80488020278076712622125697)
    ·
      refine ⟨60366015208557534466594273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80488020278076712622125697 60366015208557534466594273)
      ·
        refine ⟨45274511406418150849945705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60366015208557534466594273 45274511406418150849945705)
        ·
          refine ⟨33955883554813613137459279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45274511406418150849945705 33955883554813613137459279)
          ·
            refine ⟨50933825332220419706188919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33955883554813613137459279 50933825332220419706188919)
            ·
              refine ⟨76400737998330629559283379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50933825332220419706188919 76400737998330629559283379)
              ·
                refine ⟨114601106997495944338925069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76400737998330629559283379 114601106997495944338925069)
                ·
                  refine ⟨42975415124060979127096901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114601106997495944338925069 42975415124060979127096901)
                  ·
                    refine ⟨8057890335761433586330669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42975415124060979127096901 8057890335761433586330669)
                    ·
                      refine ⟨3021708875910537594874001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8057890335761433586330669 3021708875910537594874001)
                      ·
                        rfl

theorem cell23_5884757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_5884757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884757 prefixEnd_5884757 := by exact prefixLift 5884757
  have htrace : WordTrace (prefixWord ++ tailWord_5884757) baseStart_5884757 baseEnd_5884757 := by
    simpa [prefixWord, tailWord_5884757, baseEnd_5884757] using wordTrace_append hprefix tailTrace_5884757
  have hstable : (prefixWord ++ tailWord_5884757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884757).length < 2 ^ (prefixWord ++ tailWord_5884757).sum := by decide
  have hdescent : baseEnd_5884757 < baseStart_5884757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884831 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 2, 3, 2]
def baseStart_5884831 : Nat := 118140960795 + 5884831 * 2 ^ 59
def prefixEnd_5884831 : Nat := 4983230072969 + 3 ^ 40 * 5884831 * 2
def baseEnd_5884831 : Nat := 3021746873478970305348661

theorem tailTrace_5884831 : CollatzResearch.WordTrace tailWord_5884831 prefixEnd_5884831 3021746873478970305348661 := by
  unfold tailWord_5884831
  simp only [CollatzResearch.WordTrace]
  refine ⟨214637419743269810963862347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143091613162179873975908231 214637419743269810963862347)
  ·
    refine ⟨321956129614904716445793521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214637419743269810963862347 321956129614904716445793521)
    ·
      refine ⟨241467097211178537334345141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321956129614904716445793521 241467097211178537334345141)
      ·
        refine ⟨22637540363547987875094857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241467097211178537334345141 22637540363547987875094857)
        ·
          refine ⟨16978155272660990906321143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22637540363547987875094857 16978155272660990906321143)
          ·
            refine ⟨25467232908991486359481715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16978155272660990906321143 25467232908991486359481715)
            ·
              refine ⟨38200849363487229539222573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25467232908991486359481715 38200849363487229539222573)
              ·
                refine ⟨14325318511307711077208465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38200849363487229539222573 14325318511307711077208465)
                ·
                  refine ⟨10743988883480783307906349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14325318511307711077208465 10743988883480783307906349)
                  ·
                    refine ⟨4028995831305293740464881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10743988883480783307906349 4028995831305293740464881)
                    ·
                      refine ⟨3021746873478970305348661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4028995831305293740464881 3021746873478970305348661)
                      ·
                        rfl

theorem cell23_5884831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_5884831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884831 prefixEnd_5884831 := by exact prefixLift 5884831
  have htrace : WordTrace (prefixWord ++ tailWord_5884831) baseStart_5884831 baseEnd_5884831 := by
    simpa [prefixWord, tailWord_5884831, baseEnd_5884831] using wordTrace_append hprefix tailTrace_5884831
  have hstable : (prefixWord ++ tailWord_5884831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884831).length < 2 ^ (prefixWord ++ tailWord_5884831).sum := by decide
  have hdescent : baseEnd_5884831 < baseStart_5884831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884847 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_5884847 : Nat := 118140960795 + 5884847 * 2 ^ 59
def prefixEnd_5884847 : Nat := 4983230072969 + 3 ^ 40 * 5884847 * 2
def baseEnd_5884847 : Nat := 3021755089169442242748587

theorem tailTrace_5884847 : CollatzResearch.WordTrace tailWord_5884847 prefixEnd_5884847 3021755089169442242748587 := by
  unfold tailWord_5884847
  simp only [CollatzResearch.WordTrace]
  refine ⟨214638003311211845696444795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143092002207474563797629863 214638003311211845696444795)
  ·
    refine ⟨321957004966817768544667193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214638003311211845696444795 321957004966817768544667193)
    ·
      refine ⟨241467753725113326408500395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321957004966817768544667193 241467753725113326408500395)
      ·
        refine ⟨362201630587669989612750593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241467753725113326408500395 362201630587669989612750593)
        ·
          refine ⟨271651222940752492209562945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362201630587669989612750593 271651222940752492209562945)
          ·
            refine ⟨203738417205564369157172209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271651222940752492209562945 203738417205564369157172209)
            ·
              refine ⟨152803812904173276867879157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203738417205564369157172209 152803812904173276867879157)
              ·
                refine ⟨14325357459766244706363671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152803812904173276867879157 14325357459766244706363671)
                ·
                  refine ⟨21488036189649367059545507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14325357459766244706363671 21488036189649367059545507)
                  ·
                    refine ⟨32232054284474050589318261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21488036189649367059545507 32232054284474050589318261)
                    ·
                      refine ⟨3021755089169442242748587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32232054284474050589318261 3021755089169442242748587)
                      ·
                        rfl

theorem cell23_5884847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_5884847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884847 prefixEnd_5884847 := by exact prefixLift 5884847
  have htrace : WordTrace (prefixWord ++ tailWord_5884847) baseStart_5884847 baseEnd_5884847 := by
    simpa [prefixWord, tailWord_5884847, baseEnd_5884847] using wordTrace_append hprefix tailTrace_5884847
  have hstable : (prefixWord ++ tailWord_5884847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884847).length < 2 ^ (prefixWord ++ tailWord_5884847).sum := by decide
  have hdescent : baseEnd_5884847 < baseStart_5884847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884864 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 3]
def baseStart_5884864 : Nat := 118140960795 + 5884864 * 2 ^ 59
def prefixEnd_5884864 : Nat := 4983230072969 + 3 ^ 40 * 5884864 * 2
def baseEnd_5884864 : Nat := 3021763818340568676236009

theorem tailTrace_5884864 : CollatzResearch.WordTrace tailWord_5884864 prefixEnd_5884864 3021763818340568676236009 := by
  unfold tailWord_5884864
  simp only [CollatzResearch.WordTrace]
  refine ⟨107319311676075128799906823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143092415568100171733209097 107319311676075128799906823)
  ·
    refine ⟨160978967514112693199860235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107319311676075128799906823 160978967514112693199860235)
    ·
      refine ⟨241468451271169039799790353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160978967514112693199860235 241468451271169039799790353)
      ·
        refine ⟨181101338453376779849842765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241468451271169039799790353 181101338453376779849842765)
        ·
          refine ⟨67913001920016292443691037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181101338453376779849842765 67913001920016292443691037)
          ·
            refine ⟨25467375720006109666384139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67913001920016292443691037 25467375720006109666384139)
            ·
              refine ⟨38201063580009164499576209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25467375720006109666384139 38201063580009164499576209)
              ·
                refine ⟨28650797685006873374682157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38201063580009164499576209 28650797685006873374682157)
                ·
                  refine ⟨10744049131877577515505809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28650797685006873374682157 10744049131877577515505809)
                  ·
                    refine ⟨8058036848908183136629357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10744049131877577515505809 8058036848908183136629357)
                    ·
                      refine ⟨3021763818340568676236009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8058036848908183136629357 3021763818340568676236009)
                      ·
                        rfl

theorem cell23_5884864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_5884864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884864 prefixEnd_5884864 := by exact prefixLift 5884864
  have htrace : WordTrace (prefixWord ++ tailWord_5884864) baseStart_5884864 baseEnd_5884864 := by
    simpa [prefixWord, tailWord_5884864, baseEnd_5884864] using wordTrace_append hprefix tailTrace_5884864
  have hstable : (prefixWord ++ tailWord_5884864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884864).length < 2 ^ (prefixWord ++ tailWord_5884864).sum := by decide
  have hdescent : baseEnd_5884864 < baseStart_5884864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884878 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_5884878 : Nat := 118140960795 + 5884878 * 2 ^ 59
def prefixEnd_5884878 : Nat := 4983230072969 + 3 ^ 40 * 5884878 * 2
def baseEnd_5884878 : Nat := 3021771007069731621460945

theorem tailTrace_5884878 : CollatzResearch.WordTrace tailWord_5884878 prefixEnd_5884878 3021771007069731621460945 := by
  unfold tailWord_5884878
  simp only [CollatzResearch.WordTrace]
  refine ⟨26829891746762442248852911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143092755982733025327215525 26829891746762442248852911)
  ·
    refine ⟨40244837620143663373279367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26829891746762442248852911 40244837620143663373279367)
    ·
      refine ⟨60367256430215495059919051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40244837620143663373279367 60367256430215495059919051)
      ·
        refine ⟨90550884645323242589878577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60367256430215495059919051 90550884645323242589878577)
        ·
          refine ⟨67913163483992431942408933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90550884645323242589878577 67913163483992431942408933)
          ·
            refine ⟨12733718153248580989201675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67913163483992431942408933 12733718153248580989201675)
            ·
              refine ⟨19100577229872871483802513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12733718153248580989201675 19100577229872871483802513)
              ·
                refine ⟨14325432922404653612851885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19100577229872871483802513 14325432922404653612851885)
                ·
                  refine ⟨5372037345901745104819457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14325432922404653612851885 5372037345901745104819457)
                  ·
                    refine ⟨4029028009426308828614593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5372037345901745104819457 4029028009426308828614593)
                    ·
                      refine ⟨3021771007069731621460945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029028009426308828614593 3021771007069731621460945)
                      ·
                        rfl

theorem cell23_5884878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_5884878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884878 prefixEnd_5884878 := by exact prefixLift 5884878
  have htrace : WordTrace (prefixWord ++ tailWord_5884878) baseStart_5884878 baseEnd_5884878 := by
    simpa [prefixWord, tailWord_5884878, baseEnd_5884878] using wordTrace_append hprefix tailTrace_5884878
  have hstable : (prefixWord ++ tailWord_5884878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884878).length < 2 ^ (prefixWord ++ tailWord_5884878).sum := by decide
  have hdescent : baseEnd_5884878 < baseStart_5884878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884895 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 1, 1, 4]
def baseStart_5884895 : Nat := 118140960795 + 5884895 * 2 ^ 59
def prefixEnd_5884895 : Nat := 4983230072969 + 3 ^ 40 * 5884895 * 2
def baseEnd_5884895 : Nat := 3021779736240858054948367

theorem tailTrace_5884895 : CollatzResearch.WordTrace tailWord_5884895 prefixEnd_5884895 3021779736240858054948367 := by
  unfold tailWord_5884895
  simp only [CollatzResearch.WordTrace]
  refine ⟨214639754015037949894192139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143093169343358633262794759 214639754015037949894192139)
  ·
    refine ⟨321959631022556924841288209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214639754015037949894192139 321959631022556924841288209)
    ·
      refine ⟨241469723266917693630966157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321959631022556924841288209 241469723266917693630966157)
      ·
        refine ⟨90551146225094135111612309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241469723266917693630966157 90551146225094135111612309)
        ·
          refine ⟨4244584979301287583356827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90551146225094135111612309 4244584979301287583356827)
          ·
            refine ⟨6366877468951931375035241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4244584979301287583356827 6366877468951931375035241)
            ·
              refine ⟨4775158101713948531276431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6366877468951931375035241 4775158101713948531276431)
              ·
                refine ⟨7162737152570922796914647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775158101713948531276431 7162737152570922796914647)
                ·
                  refine ⟨10744105728856384195371971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7162737152570922796914647 10744105728856384195371971)
                  ·
                    refine ⟨16116158593284576293057957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10744105728856384195371971 16116158593284576293057957)
                    ·
                      refine ⟨3021779736240858054948367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16116158593284576293057957 3021779736240858054948367)
                      ·
                        rfl

theorem cell23_5884895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_5884895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884895 prefixEnd_5884895 := by exact prefixLift 5884895
  have htrace : WordTrace (prefixWord ++ tailWord_5884895) baseStart_5884895 baseEnd_5884895 := by
    simpa [prefixWord, tailWord_5884895, baseEnd_5884895] using wordTrace_append hprefix tailTrace_5884895
  have hstable : (prefixWord ++ tailWord_5884895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884895).length < 2 ^ (prefixWord ++ tailWord_5884895).sum := by decide
  have hdescent : baseEnd_5884895 < baseStart_5884895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884911 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 3]
def baseStart_5884911 : Nat := 118140960795 + 5884911 * 2 ^ 59
def prefixEnd_5884911 : Nat := 4983230072969 + 3 ^ 40 * 5884911 * 2
def baseEnd_5884911 : Nat := 3021787951931329992348293

theorem tailTrace_5884911 : CollatzResearch.WordTrace tailWord_5884911 prefixEnd_5884911 3021787951931329992348293 := by
  unfold tailWord_5884911
  simp only [CollatzResearch.WordTrace]
  refine ⟨214640337582979984626774587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143093558388653323084516391 214640337582979984626774587)
  ·
    refine ⟨321960506374469976940161881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214640337582979984626774587 321960506374469976940161881)
    ·
      refine ⟨241470379780852482705121411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321960506374469976940161881 241470379780852482705121411)
      ·
        refine ⟨362205569671278724057682117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241470379780852482705121411 362205569671278724057682117)
        ·
          refine ⟨67913544313364760760815397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362205569671278724057682117 67913544313364760760815397)
          ·
            refine ⟨12733789558755892642652887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67913544313364760760815397 12733789558755892642652887)
            ·
              refine ⟨19100684338133838963979331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12733789558755892642652887 19100684338133838963979331)
              ·
                refine ⟨28651026507200758445968997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19100684338133838963979331 28651026507200758445968997)
                ·
                  refine ⟨5372067470100142208619187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28651026507200758445968997 5372067470100142208619187)
                  ·
                    refine ⟨8058101205150213312928781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5372067470100142208619187 8058101205150213312928781)
                    ·
                      refine ⟨3021787951931329992348293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8058101205150213312928781 3021787951931329992348293)
                      ·
                        rfl

theorem cell23_5884911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 3].length) (baseStart_5884911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884911 prefixEnd_5884911 := by exact prefixLift 5884911
  have htrace : WordTrace (prefixWord ++ tailWord_5884911) baseStart_5884911 baseEnd_5884911 := by
    simpa [prefixWord, tailWord_5884911, baseEnd_5884911] using wordTrace_append hprefix tailTrace_5884911
  have hstable : (prefixWord ++ tailWord_5884911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884911).length < 2 ^ (prefixWord ++ tailWord_5884911).sum := by decide
  have hdescent : baseEnd_5884911 < baseStart_5884911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884937 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_5884937 : Nat := 118140960795 + 5884937 * 2 ^ 59
def prefixEnd_5884937 : Nat := 4983230072969 + 3 ^ 40 * 5884937 * 2
def baseEnd_5884937 : Nat := 3021801302428346890623173

theorem tailTrace_5884937 : CollatzResearch.WordTrace tailWord_5884937 prefixEnd_5884937 3021801302428346890623173 := by
  unfold tailWord_5884937
  simp only [CollatzResearch.WordTrace]
  refine ⟨214641285880885791067221065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143094190587257194044814043 214641285880885791067221065)
  ·
    refine ⟨160980964410664343300415799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214641285880885791067221065 160980964410664343300415799)
    ·
      refine ⟨241471446615996514950623699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160980964410664343300415799 241471446615996514950623699)
      ·
        refine ⟨362207169923994772425935549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241471446615996514950623699 362207169923994772425935549)
        ·
          refine ⟨135827688721498039659725831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362207169923994772425935549 135827688721498039659725831)
          ·
            refine ⟨203741533082247059489588747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135827688721498039659725831 203741533082247059489588747)
            ·
              refine ⟨305612299623370589234383121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203741533082247059489588747 305612299623370589234383121)
              ·
                refine ⟨229209224717527941925787341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305612299623370589234383121 229209224717527941925787341)
                ·
                  refine ⟨85953459269072978222170253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229209224717527941925787341 85953459269072978222170253)
                  ·
                    refine ⟨32232547225902366833313845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85953459269072978222170253 32232547225902366833313845)
                    ·
                      refine ⟨3021801302428346890623173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32232547225902366833313845 3021801302428346890623173)
                      ·
                        rfl

theorem cell23_5884937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_5884937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884937 prefixEnd_5884937 := by exact prefixLift 5884937
  have htrace : WordTrace (prefixWord ++ tailWord_5884937) baseStart_5884937 baseEnd_5884937 := by
    simpa [prefixWord, tailWord_5884937, baseEnd_5884937] using wordTrace_append hprefix tailTrace_5884937
  have hstable : (prefixWord ++ tailWord_5884937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884937).length < 2 ^ (prefixWord ++ tailWord_5884937).sum := by decide
  have hdescent : baseEnd_5884937 < baseStart_5884937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884938 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_5884938 : Nat := 118140960795 + 5884938 * 2 ^ 59
def prefixEnd_5884938 : Nat := 4983230072969 + 3 ^ 40 * 5884938 * 2
def baseEnd_5884938 : Nat := 3021801815909001386710669

theorem tailTrace_5884938 : CollatzResearch.WordTrace tailWord_5884938 prefixEnd_5884938 3021801815909001386710669 := by
  unfold tailWord_5884938
  simp only [CollatzResearch.WordTrace]
  refine ⟨53660330588470542059501867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143094214902588112158671645 53660330588470542059501867)
  ·
    refine ⟨80490495882705813089252801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53660330588470542059501867 80490495882705813089252801)
    ·
      refine ⟨60367871912029359816939601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80490495882705813089252801 60367871912029359816939601)
      ·
        refine ⟨45275903934022019862704701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60367871912029359816939601 45275903934022019862704701)
        ·
          refine ⟨16978463975258257448514263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45275903934022019862704701 16978463975258257448514263)
          ·
            refine ⟨25467695962887386172771395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16978463975258257448514263 25467695962887386172771395)
            ·
              refine ⟨38201543944331079259157093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25467695962887386172771395 38201543944331079259157093)
              ·
                refine ⟨7162789489562077361091955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38201543944331079259157093 7162789489562077361091955)
                ·
                  refine ⟨10744184234343116041637933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7162789489562077361091955 10744184234343116041637933)
                  ·
                    refine ⟨4029069087878668515614225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10744184234343116041637933 4029069087878668515614225)
                    ·
                      refine ⟨3021801815909001386710669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029069087878668515614225 3021801815909001386710669)
                      ·
                        rfl

theorem cell23_5884938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_5884938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884938 prefixEnd_5884938 := by exact prefixLift 5884938
  have htrace : WordTrace (prefixWord ++ tailWord_5884938) baseStart_5884938 baseEnd_5884938 := by
    simpa [prefixWord, tailWord_5884938, baseEnd_5884938] using wordTrace_append hprefix tailTrace_5884938
  have hstable : (prefixWord ++ tailWord_5884938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884938).length < 2 ^ (prefixWord ++ tailWord_5884938).sum := by decide
  have hdescent : baseEnd_5884938 < baseStart_5884938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884954 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_5884954 : Nat := 118140960795 + 5884954 * 2 ^ 59
def prefixEnd_5884954 : Nat := 4983230072969 + 3 ^ 40 * 5884954 * 2
def baseEnd_5884954 : Nat := 3021810031599473324110595

theorem tailTrace_5884954 : CollatzResearch.WordTrace tailWord_5884954 prefixEnd_5884954 3021810031599473324110595 := by
  unfold tailWord_5884954
  simp only [CollatzResearch.WordTrace]
  refine ⟨53660476480456050742647479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143094603947882801980393277 53660476480456050742647479)
  ·
    refine ⟨80490714720684076113971219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53660476480456050742647479 80490714720684076113971219)
    ·
      refine ⟨120736072081026114170956829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80490714720684076113971219 120736072081026114170956829)
      ·
        refine ⟨45276027030384792814108811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120736072081026114170956829 45276027030384792814108811)
        ·
          refine ⟨67914040545577189221163217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45276027030384792814108811 67914040545577189221163217)
          ·
            refine ⟨50935530409182891915872413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67914040545577189221163217 50935530409182891915872413)
            ·
              refine ⟨19100823903443584468452155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50935530409182891915872413 19100823903443584468452155)
              ·
                refine ⟨28651235855165376702678233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19100823903443584468452155 28651235855165376702678233)
                ·
                  refine ⟨21488426891374032527008675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28651235855165376702678233 21488426891374032527008675)
                  ·
                    refine ⟨32232640337061048790513013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21488426891374032527008675 32232640337061048790513013)
                    ·
                      refine ⟨3021810031599473324110595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32232640337061048790513013 3021810031599473324110595)
                      ·
                        rfl

theorem cell23_5884954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_5884954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884954 prefixEnd_5884954 := by exact prefixLift 5884954
  have htrace : WordTrace (prefixWord ++ tailWord_5884954) baseStart_5884954 baseEnd_5884954 := by
    simpa [prefixWord, tailWord_5884954, baseEnd_5884954] using wordTrace_append hprefix tailTrace_5884954
  have hstable : (prefixWord ++ tailWord_5884954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884954).length < 2 ^ (prefixWord ++ tailWord_5884954).sum := by decide
  have hdescent : baseEnd_5884954 < baseStart_5884954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5884985 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 2, 2, 2]
def baseStart_5884985 : Nat := 118140960795 + 5884985 * 2 ^ 59
def prefixEnd_5884985 : Nat := 4983230072969 + 3 ^ 40 * 5884985 * 2
def baseEnd_5884985 : Nat := 3021825949499762702822953

theorem tailTrace_5884985 : CollatzResearch.WordTrace tailWord_5884985 prefixEnd_5884985 3021825949499762702822953 := by
  unfold tailWord_5884985
  simp only [CollatzResearch.WordTrace]
  refine ⟨214643036584711895264968409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143095357723141263509978939 214643036584711895264968409)
  ·
    refine ⟨160982277438533921448726307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214643036584711895264968409 160982277438533921448726307)
    ·
      refine ⟨241473416157800882173089461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160982277438533921448726307 241473416157800882173089461)
      ·
        refine ⟨22638132764793832703727137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241473416157800882173089461 22638132764793832703727137)
        ·
          refine ⟨16978599573595374527795353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22638132764793832703727137 16978599573595374527795353)
          ·
            refine ⟨12733949680196530895846515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16978599573595374527795353 12733949680196530895846515)
            ·
              refine ⟨19100924520294796343769773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12733949680196530895846515 19100924520294796343769773)
              ·
                refine ⟨7162846695110548628913665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19100924520294796343769773 7162846695110548628913665)
                ·
                  refine ⟨5372135021332911471685249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162846695110548628913665 5372135021332911471685249)
                  ·
                    refine ⟨4029101265999683603763937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5372135021332911471685249 4029101265999683603763937)
                    ·
                      refine ⟨3021825949499762702822953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4029101265999683603763937 3021825949499762702822953)
                      ·
                        rfl

theorem cell23_5884985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_5884985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5884985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5884985 prefixEnd_5884985 := by exact prefixLift 5884985
  have htrace : WordTrace (prefixWord ++ tailWord_5884985) baseStart_5884985 baseEnd_5884985 := by
    simpa [prefixWord, tailWord_5884985, baseEnd_5884985] using wordTrace_append hprefix tailTrace_5884985
  have hstable : (prefixWord ++ tailWord_5884985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5884985).length < 2 ^ (prefixWord ++ tailWord_5884985).sum := by decide
  have hdescent : baseEnd_5884985 < baseStart_5884985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5884985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885151 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_5885151 : Nat := 118140960795 + 5885151 * 2 ^ 59
def prefixEnd_5885151 : Nat := 4983230072969 + 3 ^ 40 * 5885151 * 2
def baseEnd_5885151 : Nat := 3021911187288409053347189

theorem tailTrace_5885151 : CollatzResearch.WordTrace tailWord_5885151 prefixEnd_5885151 3021911187288409053347189 := by
  unfold tailWord_5885151
  simp only [CollatzResearch.WordTrace]
  refine ⟨214649091102110505615511307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143099394068073670410340871 214649091102110505615511307)
  ·
    refine ⟨321973636653165758423266961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214649091102110505615511307 321973636653165758423266961)
    ·
      refine ⟨241480227489874318817450221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321973636653165758423266961 241480227489874318817450221)
      ·
        refine ⟨90555085308702869556543833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241480227489874318817450221 90555085308702869556543833)
        ·
          refine ⟨67916313981527152167407875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90555085308702869556543833 67916313981527152167407875)
          ·
            refine ⟨101874470972290728251111813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67916313981527152167407875 101874470972290728251111813)
            ·
              refine ⟨19101463307304511547083465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101874470972290728251111813 19101463307304511547083465)
              ·
                refine ⟨14326097480478383660312599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19101463307304511547083465 14326097480478383660312599)
                ·
                  refine ⟨21489146220717575490468899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14326097480478383660312599 21489146220717575490468899)
                  ·
                    refine ⟨32233719331076363235703349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21489146220717575490468899 32233719331076363235703349)
                    ·
                      refine ⟨3021911187288409053347189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32233719331076363235703349 3021911187288409053347189)
                      ·
                        rfl

theorem cell23_5885151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_5885151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885151 prefixEnd_5885151 := by exact prefixLift 5885151
  have htrace : WordTrace (prefixWord ++ tailWord_5885151) baseStart_5885151 baseEnd_5885151 := by
    simpa [prefixWord, tailWord_5885151, baseEnd_5885151] using wordTrace_append hprefix tailTrace_5885151
  have hstable : (prefixWord ++ tailWord_5885151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885151).length < 2 ^ (prefixWord ++ tailWord_5885151).sum := by decide
  have hdescent : baseEnd_5885151 < baseStart_5885151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885165 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_5885165 : Nat := 118140960795 + 5885165 * 2 ^ 59
def prefixEnd_5885165 : Nat := 4983230072969 + 3 ^ 40 * 5885165 * 2
def baseEnd_5885165 : Nat := 3021918376017571998572125

theorem tailTrace_5885165 : CollatzResearch.WordTrace tailWord_5885165 prefixEnd_5885165 3021918376017571998572125 := by
  unfold tailWord_5885165
  simp only [CollatzResearch.WordTrace]
  refine ⟨214649601724059786006520949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143099734482706524004347299 214649601724059786006520949)
  ·
    refine ⟨20123400161630604938111339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214649601724059786006520949 20123400161630604938111339)
    ·
      refine ⟨30185100242445907407167009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20123400161630604938111339 30185100242445907407167009)
      ·
        refine ⟨22638825181834430555375257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30185100242445907407167009 22638825181834430555375257)
        ·
          refine ⟨16979118886375822916531443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22638825181834430555375257 16979118886375822916531443)
          ·
            refine ⟨25468678329563734374797165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16979118886375822916531443 25468678329563734374797165)
            ·
              refine ⟨9550754373586400390548937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25468678329563734374797165 9550754373586400390548937)
              ·
                refine ⟨7163065780189800292911703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9550754373586400390548937 7163065780189800292911703)
                ·
                  refine ⟨10744598670284700439367555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7163065780189800292911703 10744598670284700439367555)
                  ·
                    refine ⟨16116898005427050659051333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10744598670284700439367555 16116898005427050659051333)
                    ·
                      refine ⟨3021918376017571998572125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16116898005427050659051333 3021918376017571998572125)
                      ·
                        rfl

theorem cell23_5885165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_5885165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885165 prefixEnd_5885165 := by exact prefixLift 5885165
  have htrace : WordTrace (prefixWord ++ tailWord_5885165) baseStart_5885165 baseEnd_5885165 := by
    simpa [prefixWord, tailWord_5885165, baseEnd_5885165] using wordTrace_append hprefix tailTrace_5885165
  have hstable : (prefixWord ++ tailWord_5885165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885165).length < 2 ^ (prefixWord ++ tailWord_5885165).sum := by decide
  have hdescent : baseEnd_5885165 < baseStart_5885165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885182 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_5885182 : Nat := 118140960795 + 5885182 * 2 ^ 59
def prefixEnd_5885182 : Nat := 4983230072969 + 3 ^ 40 * 5885182 * 2
def baseEnd_5885182 : Nat := 3021927105188698432059547

theorem tailTrace_5885182 : CollatzResearch.WordTrace tailWord_5885182 prefixEnd_5885182 3021927105188698432059547 := by
  unfold tailWord_5885182
  simp only [CollatzResearch.WordTrace]
  refine ⟨26831277720624774738736225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143100147843332131939926533 26831277720624774738736225)
  ·
    refine ⟨20123458290468581054052169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26831277720624774738736225 20123458290468581054052169)
    ·
      refine ⟨15092593717851435790539127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20123458290468581054052169 15092593717851435790539127)
      ·
        refine ⟨22638890576777153685808691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15092593717851435790539127 22638890576777153685808691)
        ·
          refine ⟨33958335865165730528713037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22638890576777153685808691 33958335865165730528713037)
          ·
            refine ⟨12734375949437148948267389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33958335865165730528713037 12734375949437148948267389)
            ·
              refine ⟨4775390981038930855600271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12734375949437148948267389 4775390981038930855600271)
              ·
                refine ⟨7163086471558396283400407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775390981038930855600271 7163086471558396283400407)
                ·
                  refine ⟨10744629707337594425100611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7163086471558396283400407 10744629707337594425100611)
                  ·
                    refine ⟨16116944561006391637650917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10744629707337594425100611 16116944561006391637650917)
                    ·
                      refine ⟨3021927105188698432059547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16116944561006391637650917 3021927105188698432059547)
                      ·
                        rfl

theorem cell23_5885182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_5885182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885182 prefixEnd_5885182 := by exact prefixLift 5885182
  have htrace : WordTrace (prefixWord ++ tailWord_5885182) baseStart_5885182 baseEnd_5885182 := by
    simpa [prefixWord, tailWord_5885182, baseEnd_5885182] using wordTrace_append hprefix tailTrace_5885182
  have hstable : (prefixWord ++ tailWord_5885182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885182).length < 2 ^ (prefixWord ++ tailWord_5885182).sum := by decide
  have hdescent : baseEnd_5885182 < baseStart_5885182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885215 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 3]
def baseStart_5885215 : Nat := 118140960795 + 5885215 * 2 ^ 59
def prefixEnd_5885215 : Nat := 4983230072969 + 3 ^ 40 * 5885215 * 2
def baseEnd_5885215 : Nat := 3021944050050296802946895

theorem tailTrace_5885215 : CollatzResearch.WordTrace tailWord_5885215 prefixEnd_5885215 3021944050050296802946895 := by
  unfold tailWord_5885215
  simp only [CollatzResearch.WordTrace]
  refine ⟨214651425373878644545841099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143100950249252429697227399 214651425373878644545841099)
  ·
    refine ⟨321977138060817966818761649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214651425373878644545841099 321977138060817966818761649)
    ·
      refine ⟨241482853545613475114071237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321977138060817966818761649 241482853545613475114071237)
      ·
        refine ⟨45278035039802526583888357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241482853545613475114071237 45278035039802526583888357)
        ·
          refine ⟨8489631569962973734479067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45278035039802526583888357 8489631569962973734479067)
          ·
            refine ⟨12734447354944460601718601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8489631569962973734479067 12734447354944460601718601)
            ·
              refine ⟨9550835516208345451288951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12734447354944460601718601 9550835516208345451288951)
              ·
                refine ⟨14326253274312518176933427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9550835516208345451288951 14326253274312518176933427)
                ·
                  refine ⟨21489379911468777265400141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14326253274312518176933427 21489379911468777265400141)
                  ·
                    refine ⟨8058517466800791474525053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21489379911468777265400141 8058517466800791474525053)
                    ·
                      refine ⟨3021944050050296802946895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8058517466800791474525053 3021944050050296802946895)
                      ·
                        rfl

theorem cell23_5885215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_5885215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885215 prefixEnd_5885215 := by exact prefixLift 5885215
  have htrace : WordTrace (prefixWord ++ tailWord_5885215) baseStart_5885215 baseEnd_5885215 := by
    simpa [prefixWord, tailWord_5885215, baseEnd_5885215] using wordTrace_append hprefix tailTrace_5885215
  have hstable : (prefixWord ++ tailWord_5885215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885215).length < 2 ^ (prefixWord ++ tailWord_5885215).sum := by decide
  have hdescent : baseEnd_5885215 < baseStart_5885215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885249 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5885249 : Nat := 118140960795 + 5885249 * 2 ^ 59
def prefixEnd_5885249 : Nat := 4983230072969 + 3 ^ 40 * 5885249 * 2
def baseEnd_5885249 : Nat := 3021961508392549669921739

theorem tailTrace_5885249 : CollatzResearch.WordTrace tailWord_5885249 prefixEnd_5885249 3021961508392549669921739 := by
  unfold tailWord_5885249
  simp only [CollatzResearch.WordTrace]
  refine ⟨214652665455755468352578801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143101776970503645568385867 214652665455755468352578801)
  ·
    refine ⟨160989499091816601264434101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214652665455755468352578801 160989499091816601264434101)
    ·
      refine ⟨15092765539857806368540697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160989499091816601264434101 15092765539857806368540697)
      ·
        refine ⟨11319574154893354776405523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15092765539857806368540697 11319574154893354776405523)
        ·
          refine ⟨16979361232340032164608285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11319574154893354776405523 16979361232340032164608285)
          ·
            refine ⟨6367260462127512061728107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16979361232340032164608285 6367260462127512061728107)
            ·
              refine ⟨9550890693191268092592161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6367260462127512061728107 9550890693191268092592161)
              ·
                refine ⟨7163168019893451069444121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9550890693191268092592161 7163168019893451069444121)
                ·
                  refine ⟨5372376014920088302083091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7163168019893451069444121 5372376014920088302083091)
                  ·
                    refine ⟨8058564022380132453124637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5372376014920088302083091 8058564022380132453124637)
                    ·
                      refine ⟨3021961508392549669921739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8058564022380132453124637 3021961508392549669921739)
                      ·
                        rfl

theorem cell23_5885249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5885249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885249 prefixEnd_5885249 := by exact prefixLift 5885249
  have htrace : WordTrace (prefixWord ++ tailWord_5885249) baseStart_5885249 baseEnd_5885249 := by
    simpa [prefixWord, tailWord_5885249, baseEnd_5885249] using wordTrace_append hprefix tailTrace_5885249
  have hstable : (prefixWord ++ tailWord_5885249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885249).length < 2 ^ (prefixWord ++ tailWord_5885249).sum := by decide
  have hdescent : baseEnd_5885249 < baseStart_5885249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885268 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_5885268 : Nat := 118140960795 + 5885268 * 2 ^ 59
def prefixEnd_5885268 : Nat := 4983230072969 + 3 ^ 40 * 5885268 * 2
def baseEnd_5885268 : Nat := 3021971264524985095584151

theorem tailTrace_5885268 : CollatzResearch.WordTrace tailWord_5885268 prefixEnd_5885268 3021971264524985095584151 := by
  unfold tailWord_5885268
  simp only [CollatzResearch.WordTrace]
  refine ⟨107326679221343317298760229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143102238961791089731680305 107326679221343317298760229)
  ·
    refine ⟨20123752354001871993517543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107326679221343317298760229 20123752354001871993517543)
    ·
      refine ⟨30185628531002807990276315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20123752354001871993517543 30185628531002807990276315)
      ·
        refine ⟨45278442796504211985414473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30185628531002807990276315 45278442796504211985414473)
        ·
          refine ⟨33958832097378158989060855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45278442796504211985414473 33958832097378158989060855)
          ·
            refine ⟨50938248146067238483591283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33958832097378158989060855 50938248146067238483591283)
            ·
              refine ⟨76407372219100857725386925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50938248146067238483591283 76407372219100857725386925)
              ·
                refine ⟨28652764582162821647020097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76407372219100857725386925 28652764582162821647020097)
                ·
                  refine ⟨21489573436622116235265073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28652764582162821647020097 21489573436622116235265073)
                  ·
                    refine ⟨16117180077466587176448805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21489573436622116235265073 16117180077466587176448805)
                    ·
                      refine ⟨3021971264524985095584151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16117180077466587176448805 3021971264524985095584151)
                      ·
                        rfl

theorem cell23_5885268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_5885268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885268 prefixEnd_5885268 := by exact prefixLift 5885268
  have htrace : WordTrace (prefixWord ++ tailWord_5885268) baseStart_5885268 baseEnd_5885268 := by
    simpa [prefixWord, tailWord_5885268, baseEnd_5885268] using wordTrace_append hprefix tailTrace_5885268
  have hstable : (prefixWord ++ tailWord_5885268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885268).length < 2 ^ (prefixWord ++ tailWord_5885268).sum := by decide
  have hdescent : baseEnd_5885268 < baseStart_5885268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5885308 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_5885308 : Nat := 118140960795 + 5885308 * 2 ^ 59
def prefixEnd_5885308 : Nat := 4983230072969 + 3 ^ 40 * 5885308 * 2
def baseEnd_5885308 : Nat := 1007330601250388313027989

theorem tailTrace_5885308 : CollatzResearch.WordTrace tailWord_5885308 prefixEnd_5885308 1007330601250388313027989 := by
  unfold tailWord_5885308
  simp only [CollatzResearch.WordTrace]
  refine ⟨107327408681270860714488289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143103211575027814285984385 107327408681270860714488289)
  ·
    refine ⟨80495556510953145535866217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107327408681270860714488289 80495556510953145535866217)
    ·
      refine ⟨60371667383214859151899663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80495556510953145535866217 60371667383214859151899663)
      ·
        refine ⟨90557501074822288727849495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60371667383214859151899663 90557501074822288727849495)
        ·
          refine ⟨135836251612233433091774243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90557501074822288727849495 135836251612233433091774243)
          ·
            refine ⟨203754377418350149637661365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135836251612233433091774243 203754377418350149637661365)
            ·
              refine ⟨19101972882970326528530753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203754377418350149637661365 19101972882970326528530753)
              ·
                refine ⟨14326479662227744896398065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19101972882970326528530753 14326479662227744896398065)
                ·
                  refine ⟨10744859746670808672298549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14326479662227744896398065 10744859746670808672298549)
                  ·
                    refine ⟨1007330601250388313027989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10744859746670808672298549 1007330601250388313027989)
                    ·
                      rfl

theorem cell23_5885308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_5885308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5885308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5885308 prefixEnd_5885308 := by exact prefixLift 5885308
  have htrace : WordTrace (prefixWord ++ tailWord_5885308) baseStart_5885308 baseEnd_5885308 := by
    simpa [prefixWord, tailWord_5885308, baseEnd_5885308] using wordTrace_append hprefix tailTrace_5885308
  have hstable : (prefixWord ++ tailWord_5885308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5885308).length < 2 ^ (prefixWord ++ tailWord_5885308).sum := by decide
  have hdescent : baseEnd_5885308 < baseStart_5885308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5885308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
