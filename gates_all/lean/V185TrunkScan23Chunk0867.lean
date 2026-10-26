import V185TrunkScan23Chunk0866

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5131287 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5131287 : Nat := 118140960795 + 5131287 * 2 ^ 59
def prefixEnd_5131287 : Nat := 4983230072969 + 3 ^ 40 * 5131287 * 2
def baseEnd_5131287 : Nat := 2634816607167370549714147

theorem tailTrace_5131287 : CollatzResearch.WordTrace tailWord_5131287 prefixEnd_5131287 2634816607167370549714147 := by
  unfold tailWord_5131287
  simp only [CollatzResearch.WordTrace]
  refine ⟨187153412161231027894600115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124768941440820685263066743 187153412161231027894600115)
  ·
    refine ⟨280730118241846541841900173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187153412161231027894600115 280730118241846541841900173)
    ·
      refine ⟨105273794340692453190712565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280730118241846541841900173 105273794340692453190712565)
      ·
        refine ⟨9869418219439917486629303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105273794340692453190712565 9869418219439917486629303)
        ·
          refine ⟨14804127329159876229943955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9869418219439917486629303 14804127329159876229943955)
          ·
            refine ⟨22206190993739814344915933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14804127329159876229943955 22206190993739814344915933)
            ·
              refine ⟨8327321622652430379343475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22206190993739814344915933 8327321622652430379343475)
              ·
                refine ⟨12490982433978645569015213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327321622652430379343475 12490982433978645569015213)
                ·
                  refine ⟨4684118412741992088380705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12490982433978645569015213 4684118412741992088380705)
                  ·
                    refine ⟨3513088809556494066285529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4684118412741992088380705 3513088809556494066285529)
                    ·
                      refine ⟨2634816607167370549714147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513088809556494066285529 2634816607167370549714147)
                      ·
                        rfl

theorem cell23_5131287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5131287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131287 prefixEnd_5131287 := by exact prefixLift 5131287
  have htrace : WordTrace (prefixWord ++ tailWord_5131287) baseStart_5131287 baseEnd_5131287 := by
    simpa [prefixWord, tailWord_5131287, baseEnd_5131287] using wordTrace_append hprefix tailTrace_5131287
  have hstable : (prefixWord ++ tailWord_5131287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131287).length < 2 ^ (prefixWord ++ tailWord_5131287).sum := by decide
  have hdescent : baseEnd_5131287 < baseStart_5131287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131293 : List Nat := [1, 4, 2, 2, 3, 1, 2, 8]
def baseStart_5131293 : Nat := 118140960795 + 5131293 * 2 ^ 59
def prefixEnd_5131293 : Nat := 4983230072969 + 3 ^ 40 * 5131293 * 2
def baseEnd_5131293 : Nat := 97585914372270278749597

theorem tailTrace_5131293 : CollatzResearch.WordTrace tailWord_5131293 prefixEnd_5131293 97585914372270278749597 := by
  unfold tailWord_5131293
  simp only [CollatzResearch.WordTrace]
  refine ⟨187153630999209290919318533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124769087332806193946212355 187153630999209290919318533)
  ·
    refine ⟨35091305812351742047372225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187153630999209290919318533 35091305812351742047372225)
    ·
      refine ⟨26318479359263806535529169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35091305812351742047372225 26318479359263806535529169)
      ·
        refine ⟨19738859519447854901646877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26318479359263806535529169 19738859519447854901646877)
        ·
          refine ⟨7402072319792945588117579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19738859519447854901646877 7402072319792945588117579)
          ·
            refine ⟨11103108479689418382176369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7402072319792945588117579 11103108479689418382176369)
            ·
              refine ⟨8327331359767063786632277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11103108479689418382176369 8327331359767063786632277)
              ·
                refine ⟨97585914372270278749597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8327331359767063786632277 97585914372270278749597)
                ·
                  rfl

theorem cell23_5131293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 8].length) (baseStart_5131293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131293 prefixEnd_5131293 := by exact prefixLift 5131293
  have htrace : WordTrace (prefixWord ++ tailWord_5131293) baseStart_5131293 baseEnd_5131293 := by
    simpa [prefixWord, tailWord_5131293, baseEnd_5131293] using wordTrace_append hprefix tailTrace_5131293
  have hstable : (prefixWord ++ tailWord_5131293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131293).length < 2 ^ (prefixWord ++ tailWord_5131293).sum := by decide
  have hdescent : baseEnd_5131293 < baseStart_5131293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131297 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 2, 4]
def baseStart_5131297 : Nat := 118140960795 + 5131297 * 2 ^ 59
def prefixEnd_5131297 : Nat := 4983230072969 + 3 ^ 40 * 5131297 * 2
def baseEnd_5131297 : Nat := 878273913991305170196367

theorem tailTrace_5131297 : CollatzResearch.WordTrace tailWord_5131297 prefixEnd_5131297 878273913991305170196367 := by
  unfold tailWord_5131297
  simp only [CollatzResearch.WordTrace]
  refine ⟨187153776891194799602464145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124769184594129866401642763 187153776891194799602464145)
  ·
    refine ⟨140365332668396099701848109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187153776891194799602464145 140365332668396099701848109)
    ·
      refine ⟨52636999750648537388193041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140365332668396099701848109 52636999750648537388193041)
      ·
        refine ⟨39477749812986403041144781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52636999750648537388193041 39477749812986403041144781)
        ·
          refine ⟨14804156179869901140429293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39477749812986403041144781 14804156179869901140429293)
          ·
            refine ⟨5551558567451212927660985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14804156179869901140429293 5551558567451212927660985)
            ·
              refine ⟨4163668925588409695745739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5551558567451212927660985 4163668925588409695745739)
              ·
                refine ⟨6245503388382614543618609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163668925588409695745739 6245503388382614543618609)
                ·
                  refine ⟨4684127541286960907713957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6245503388382614543618609 4684127541286960907713957)
                  ·
                    refine ⟨878273913991305170196367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4684127541286960907713957 878273913991305170196367)
                    ·
                      rfl

theorem cell23_5131297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_5131297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131297 prefixEnd_5131297 := by exact prefixLift 5131297
  have htrace : WordTrace (prefixWord ++ tailWord_5131297) baseStart_5131297 baseEnd_5131297 := by
    simpa [prefixWord, tailWord_5131297, baseEnd_5131297] using wordTrace_append hprefix tailTrace_5131297
  have hstable : (prefixWord ++ tailWord_5131297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131297).length < 2 ^ (prefixWord ++ tailWord_5131297).sum := by decide
  have hdescent : baseEnd_5131297 < baseStart_5131297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131336 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 2, 6]
def baseStart_5131336 : Nat := 118140960795 + 5131336 * 2 ^ 59
def prefixEnd_5131336 : Nat := 4983230072969 + 3 ^ 40 * 5131336 * 2
def baseEnd_5131336 : Nat := 878280589239813619333807

theorem tailTrace_5131336 : CollatzResearch.WordTrace tailWord_5131336 prefixEnd_5131336 878280589239813619333807 := by
  unfold tailWord_5131336
  simp only [CollatzResearch.WordTrace]
  refine ⟨93577599669026754631566931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124770132892035672842089241 93577599669026754631566931)
  ·
    refine ⟨140366399503540131947350397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93577599669026754631566931 140366399503540131947350397)
    ·
      refine ⟨52637399813827549480256399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140366399503540131947350397 52637399813827549480256399)
      ·
        refine ⟨78956099720741324220384599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52637399813827549480256399 78956099720741324220384599)
        ·
          refine ⟨118434149581111986330576899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78956099720741324220384599 118434149581111986330576899)
          ·
            refine ⟨177651224371667979495865349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118434149581111986330576899 177651224371667979495865349)
            ·
              refine ⟨33309604569687746155474753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177651224371667979495865349 33309604569687746155474753)
              ·
                refine ⟨24982203427265809616606065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33309604569687746155474753 24982203427265809616606065)
                ·
                  refine ⟨18736652570449357212454549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24982203427265809616606065 18736652570449357212454549)
                  ·
                    refine ⟨878280589239813619333807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18736652570449357212454549 878280589239813619333807)
                    ·
                      rfl

theorem cell23_5131336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_5131336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131336 prefixEnd_5131336 := by exact prefixLift 5131336
  have htrace : WordTrace (prefixWord ++ tailWord_5131336) baseStart_5131336 baseEnd_5131336 := by
    simpa [prefixWord, tailWord_5131336, baseEnd_5131336] using wordTrace_append hprefix tailTrace_5131336
  have hstable : (prefixWord ++ tailWord_5131336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131336).length < 2 ^ (prefixWord ++ tailWord_5131336).sum := by decide
  have hdescent : baseEnd_5131336 < baseStart_5131336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131360 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 1, 4, 2]
def baseStart_5131360 : Nat := 118140960795 + 5131360 * 2 ^ 59
def prefixEnd_5131360 : Nat := 4983230072969 + 3 ^ 40 * 5131360 * 2
def baseEnd_5131360 : Nat := 2634854091255148764101311

theorem tailTrace_5131360 : CollatzResearch.WordTrace tailWord_5131360 prefixEnd_5131360 2634854091255148764101311 := by
  unfold tailWord_5131360
  simp only [CollatzResearch.WordTrace]
  refine ⟨93578037344983280681003767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124770716459977707574671689 93578037344983280681003767)
  ·
    refine ⟨140367056017474921021505651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93578037344983280681003767 140367056017474921021505651)
    ·
      refine ⟨210550584026212381532258477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140367056017474921021505651 210550584026212381532258477)
      ·
        refine ⟨78956469009829643074596929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210550584026212381532258477 78956469009829643074596929)
        ·
          refine ⟨59217351757372232305947697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78956469009829643074596929 59217351757372232305947697)
          ·
            refine ⟨44413013818029174229460773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59217351757372232305947697 44413013818029174229460773)
            ·
              refine ⟨8327440090880470168023895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44413013818029174229460773 8327440090880470168023895)
              ·
                refine ⟨12491160136320705252035843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327440090880470168023895 12491160136320705252035843)
                ·
                  refine ⟨18736740204481057878053765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12491160136320705252035843 18736740204481057878053765)
                  ·
                    refine ⟨3513138788340198352135081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18736740204481057878053765 3513138788340198352135081)
                    ·
                      refine ⟨2634854091255148764101311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513138788340198352135081 2634854091255148764101311)
                      ·
                        rfl

theorem cell23_5131360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_5131360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131360 prefixEnd_5131360 := by exact prefixLift 5131360
  have htrace : WordTrace (prefixWord ++ tailWord_5131360) baseStart_5131360 baseEnd_5131360 := by
    simpa [prefixWord, tailWord_5131360, baseEnd_5131360] using wordTrace_append hprefix tailTrace_5131360
  have hstable : (prefixWord ++ tailWord_5131360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131360).length < 2 ^ (prefixWord ++ tailWord_5131360).sum := by decide
  have hdescent : baseEnd_5131360 < baseStart_5131360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131400 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 7]
def baseStart_5131400 : Nat := 118140960795 + 5131400 * 2 ^ 59
def prefixEnd_5131400 : Nat := 4983230072969 + 3 ^ 40 * 5131400 * 2
def baseEnd_5131400 : Nat := 292763847831258734177903

theorem tailTrace_5131400 : CollatzResearch.WordTrace tailWord_5131400 prefixEnd_5131400 292763847831258734177903 := by
  unfold tailWord_5131400
  simp only [CollatzResearch.WordTrace]
  refine ⟨93578766804910824096731827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124771689073214432128975769 93578766804910824096731827)
  ·
    refine ⟨140368150207366236145097741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93578766804910824096731827 140368150207366236145097741)
    ·
      refine ⟨52638056327762338554411653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140368150207366236145097741 52638056327762338554411653)
      ·
        refine ⟨9869635561455438478952185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52638056327762338554411653 9869635561455438478952185)
        ·
          refine ⟨7402226671091578859214139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9869635561455438478952185 7402226671091578859214139)
          ·
            refine ⟨11103340006637368288821209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7402226671091578859214139 11103340006637368288821209)
            ·
              refine ⟨8327505004978026216615907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11103340006637368288821209 8327505004978026216615907)
              ·
                refine ⟨12491257507467039324923861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327505004978026216615907 12491257507467039324923861)
                ·
                  refine ⟨292763847831258734177903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12491257507467039324923861 292763847831258734177903)
                  ·
                    rfl

theorem cell23_5131400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 7].length) (baseStart_5131400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131400 prefixEnd_5131400 := by exact prefixLift 5131400
  have htrace : WordTrace (prefixWord ++ tailWord_5131400) baseStart_5131400 baseEnd_5131400 := by
    simpa [prefixWord, tailWord_5131400, baseEnd_5131400] using wordTrace_append hprefix tailTrace_5131400
  have hstable : (prefixWord ++ tailWord_5131400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131400).length < 2 ^ (prefixWord ++ tailWord_5131400).sum := by decide
  have hdescent : baseEnd_5131400 < baseStart_5131400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131403 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 1, 7, 2]
def baseStart_5131403 : Nat := 118140960795 + 5131403 * 2 ^ 59
def prefixEnd_5131403 : Nat := 4983230072969 + 3 ^ 40 * 5131403 * 2
def baseEnd_5131403 : Nat := 2634876170923292095863613

theorem tailTrace_5131403 : CollatzResearch.WordTrace tailWord_5131403 prefixEnd_5131403 2634876170923292095863613 := by
  unfold tailWord_5131403
  simp only [CollatzResearch.WordTrace]
  refine ⟨187157643028810779705822863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124771762019207186470548575 187157643028810779705822863)
  ·
    refine ⟨280736464543216169558734295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187157643028810779705822863 280736464543216169558734295)
    ·
      refine ⟨421104696814824254338101443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280736464543216169558734295 421104696814824254338101443)
      ·
        refine ⟨631657045222236381507152165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421104696814824254338101443 631657045222236381507152165)
        ·
          refine ⟨118435695979169321532591031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 631657045222236381507152165 118435695979169321532591031)
          ·
            refine ⟨177653543968753982298886547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118435695979169321532591031 177653543968753982298886547)
            ·
              refine ⟨266480315953130973448329821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177653543968753982298886547 266480315953130973448329821)
              ·
                refine ⟨99930118482424115043123683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266480315953130973448329821 99930118482424115043123683)
                ·
                  refine ⟨149895177723636172564685525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99930118482424115043123683 149895177723636172564685525)
                  ·
                    refine ⟨3513168227897722794484817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149895177723636172564685525 3513168227897722794484817)
                    ·
                      refine ⟨2634876170923292095863613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513168227897722794484817 2634876170923292095863613)
                      ·
                        rfl

theorem cell23_5131403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 7, 2].length) (baseStart_5131403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131403 prefixEnd_5131403 := by exact prefixLift 5131403
  have htrace : WordTrace (prefixWord ++ tailWord_5131403) baseStart_5131403 baseEnd_5131403 := by
    simpa [prefixWord, tailWord_5131403, baseEnd_5131403] using wordTrace_append hprefix tailTrace_5131403
  have hstable : (prefixWord ++ tailWord_5131403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131403).length < 2 ^ (prefixWord ++ tailWord_5131403).sum := by decide
  have hdescent : baseEnd_5131403 < baseStart_5131403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131410 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_5131410 : Nat := 118140960795 + 5131410 * 2 ^ 59
def prefixEnd_5131410 : Nat := 4983230072969 + 3 ^ 40 * 5131410 * 2
def baseEnd_5131410 : Nat := 2634879765287873568476081

theorem tailTrace_5131410 : CollatzResearch.WordTrace tailWord_5131410 prefixEnd_5131410 2634879765287873568476081 := by
  unfold tailWord_5131410
  simp only [CollatzResearch.WordTrace]
  refine ⟨46789474584946354975331921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124771932226523613267551789 46789474584946354975331921)
  ·
    refine ⟨35092105938709766231498941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46789474584946354975331921 35092105938709766231498941)
    ·
      refine ⟨13159539727016162336812103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35092105938709766231498941 13159539727016162336812103)
      ·
        refine ⟨19739309590524243505218155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13159539727016162336812103 19739309590524243505218155)
        ·
          refine ⟨29608964385786365257827233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19739309590524243505218155 29608964385786365257827233)
          ·
            refine ⟨22206723289339773943370425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29608964385786365257827233 22206723289339773943370425)
            ·
              refine ⟨16655042467004830457527819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22206723289339773943370425 16655042467004830457527819)
              ·
                refine ⟨24982563700507245686291729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16655042467004830457527819 24982563700507245686291729)
                ·
                  refine ⟨18736922775380434264718797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24982563700507245686291729 18736922775380434264718797)
                  ·
                    refine ⟨7026346040767662849269549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18736922775380434264718797 7026346040767662849269549)
                    ·
                      refine ⟨2634879765287873568476081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7026346040767662849269549 2634879765287873568476081)
                      ·
                        rfl

theorem cell23_5131410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_5131410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131410 prefixEnd_5131410 := by exact prefixLift 5131410
  have htrace : WordTrace (prefixWord ++ tailWord_5131410) baseStart_5131410 baseEnd_5131410 := by
    simpa [prefixWord, tailWord_5131410, baseEnd_5131410] using wordTrace_append hprefix tailTrace_5131410
  have hstable : (prefixWord ++ tailWord_5131410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131410).length < 2 ^ (prefixWord ++ tailWord_5131410).sum := by decide
  have hdescent : baseEnd_5131410 < baseStart_5131410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131434 : List Nat := [3, 1, 5, 1, 1, 3, 1, 3, 5]
def baseStart_5131434 : Nat := 118140960795 + 5131434 * 2 ^ 59
def prefixEnd_5131434 : Nat := 4983230072969 + 3 ^ 40 * 5131434 * 2
def baseEnd_5131434 : Nat := 292765787647064608286219

theorem tailTrace_5131434 : CollatzResearch.WordTrace tailWord_5131434 prefixEnd_5131434 292765787647064608286219 := by
  unfold tailWord_5131434
  simp only [CollatzResearch.WordTrace]
  refine ⟨46789693422924618000050339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124772515794465648000134237 46789693422924618000050339)
  ·
    refine ⟨70184540134386927000075509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46789693422924618000050339 70184540134386927000075509)
    ·
      refine ⟨6579800637598774406257079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70184540134386927000075509 6579800637598774406257079)
      ·
        refine ⟨9869700956398161609385619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6579800637598774406257079 9869700956398161609385619)
        ·
          refine ⟨14804551434597242414078429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9869700956398161609385619 14804551434597242414078429)
          ·
            refine ⟨5551706787973965905279411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14804551434597242414078429 5551706787973965905279411)
            ·
              refine ⟨8327560181960948857919117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551706787973965905279411 8327560181960948857919117)
              ·
                refine ⟨3122835068235355821719669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8327560181960948857919117 3122835068235355821719669)
                ·
                  refine ⟨292765787647064608286219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3122835068235355821719669 292765787647064608286219)
                  ·
                    rfl

theorem cell23_5131434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_5131434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131434 prefixEnd_5131434 := by exact prefixLift 5131434
  have htrace : WordTrace (prefixWord ++ tailWord_5131434) baseStart_5131434 baseEnd_5131434 := by
    simpa [prefixWord, tailWord_5131434, baseEnd_5131434] using wordTrace_append hprefix tailTrace_5131434
  have hstable : (prefixWord ++ tailWord_5131434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131434).length < 2 ^ (prefixWord ++ tailWord_5131434).sum := by decide
  have hdescent : baseEnd_5131434 < baseStart_5131434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131443 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 5, 4]
def baseStart_5131443 : Nat := 118140960795 + 5131443 * 2 ^ 59
def prefixEnd_5131443 : Nat := 4983230072969 + 3 ^ 40 * 5131443 * 2
def baseEnd_5131443 : Nat := 878298903383157313121143

theorem tailTrace_5131443 : CollatzResearch.WordTrace tailWord_5131443 prefixEnd_5131443 878298903383157313121143 := by
  unfold tailWord_5131443
  simp only [CollatzResearch.WordTrace]
  refine ⟨187159101948665866537278983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124772734632443911024852655 187159101948665866537278983)
  ·
    refine ⟨280738652922998799805918475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187159101948665866537278983 280738652922998799805918475)
    ·
      refine ⟨421107979384498199708877713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280738652922998799805918475 421107979384498199708877713)
      ·
        refine ⟨315830984538373649781658285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421107979384498199708877713 315830984538373649781658285)
        ·
          refine ⟨118436619201890118668121857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315830984538373649781658285 118436619201890118668121857)
          ·
            refine ⟨88827464401417589001091393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118436619201890118668121857 88827464401417589001091393)
            ·
              refine ⟨66620598301063191750818545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88827464401417589001091393 66620598301063191750818545)
              ·
                refine ⟨49965448725797393813113909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66620598301063191750818545 49965448725797393813113909)
                ·
                  refine ⟨4684260818043505669979429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49965448725797393813113909 4684260818043505669979429)
                  ·
                    refine ⟨878298903383157313121143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4684260818043505669979429 878298903383157313121143)
                    ·
                      rfl

theorem cell23_5131443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 4].length) (baseStart_5131443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131443 prefixEnd_5131443 := by exact prefixLift 5131443
  have htrace : WordTrace (prefixWord ++ tailWord_5131443) baseStart_5131443 baseEnd_5131443 := by
    simpa [prefixWord, tailWord_5131443, baseEnd_5131443] using wordTrace_append hprefix tailTrace_5131443
  have hstable : (prefixWord ++ tailWord_5131443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131443).length < 2 ^ (prefixWord ++ tailWord_5131443).sum := by decide
  have hdescent : baseEnd_5131443 < baseStart_5131443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131462 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5131462 : Nat := 118140960795 + 5131462 * 2 ^ 59
def prefixEnd_5131462 : Nat := 4983230072969 + 3 ^ 40 * 5131462 * 2
def baseEnd_5131462 : Nat := 2634906466281907365025843

theorem tailTrace_5131462 : CollatzResearch.WordTrace tailWord_5131462 prefixEnd_5131462 2634906466281907365025843 := by
  unfold tailWord_5131462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5848743591737407274444395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124773196623731355188147093 5848743591737407274444395)
  ·
    refine ⟨8773115387606110911666593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5848743591737407274444395 8773115387606110911666593)
    ·
      refine ⟨6579836540704583183749945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8773115387606110911666593 6579836540704583183749945)
      ·
        refine ⟨4934877405528437387812459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6579836540704583183749945 4934877405528437387812459)
        ·
          refine ⟨7402316108292656081718689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934877405528437387812459 7402316108292656081718689)
          ·
            refine ⟨5551737081219492061289017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7402316108292656081718689 5551737081219492061289017)
            ·
              refine ⟨4163802810914619045966763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5551737081219492061289017 4163802810914619045966763)
              ·
                refine ⟨6245704216371928568950145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163802810914619045966763 6245704216371928568950145)
                ·
                  refine ⟨4684278162278946426712609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6245704216371928568950145 4684278162278946426712609)
                  ·
                    refine ⟨3513208621709209820034457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4684278162278946426712609 3513208621709209820034457)
                    ·
                      refine ⟨2634906466281907365025843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513208621709209820034457 2634906466281907365025843)
                      ·
                        rfl

theorem cell23_5131462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5131462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131462 prefixEnd_5131462 := by exact prefixLift 5131462
  have htrace : WordTrace (prefixWord ++ tailWord_5131462) baseStart_5131462 baseEnd_5131462 := by
    simpa [prefixWord, tailWord_5131462, baseEnd_5131462] using wordTrace_append hprefix tailTrace_5131462
  have hstable : (prefixWord ++ tailWord_5131462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131462).length < 2 ^ (prefixWord ++ tailWord_5131462).sum := by decide
  have hdescent : baseEnd_5131462 < baseStart_5131462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131538 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5131538 : Nat := 118140960795 + 5131538 * 2 ^ 59
def prefixEnd_5131538 : Nat := 4983230072969 + 3 ^ 40 * 5131538 * 2
def baseEnd_5131538 : Nat := 2634945490811649067675493

theorem tailTrace_5131538 : CollatzResearch.WordTrace tailWord_5131538 prefixEnd_5131538 2634945490811649067675493 := by
  unfold tailWord_5131538
  simp only [CollatzResearch.WordTrace]
  refine ⟨46790641720830424440496817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124775044588881131841324845 46790641720830424440496817)
  ·
    refine ⟨35092981290622818330372613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46790641720830424440496817 35092981290622818330372613)
    ·
      refine ⟨6579933991991778436944865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35092981290622818330372613 6579933991991778436944865)
      ·
        refine ⟨4934950493993833827708649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6579933991991778436944865 4934950493993833827708649)
        ·
          refine ⟨3701212870495375370781487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4934950493993833827708649 3701212870495375370781487)
          ·
            refine ⟨5551819305743063056172231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701212870495375370781487 5551819305743063056172231)
            ·
              refine ⟨8327728958614594584258347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551819305743063056172231 8327728958614594584258347)
              ·
                refine ⟨12491593437921891876387521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327728958614594584258347 12491593437921891876387521)
                ·
                  refine ⟨9368695078441418907290641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12491593437921891876387521 9368695078441418907290641)
                  ·
                    refine ⟨7026521308831064180467981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9368695078441418907290641 7026521308831064180467981)
                    ·
                      refine ⟨2634945490811649067675493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7026521308831064180467981 2634945490811649067675493)
                      ·
                        rfl

theorem cell23_5131538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5131538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131538 prefixEnd_5131538 := by exact prefixLift 5131538
  have htrace : WordTrace (prefixWord ++ tailWord_5131538) baseStart_5131538 baseEnd_5131538 := by
    simpa [prefixWord, tailWord_5131538, baseEnd_5131538] using wordTrace_append hprefix tailTrace_5131538
  have hstable : (prefixWord ++ tailWord_5131538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131538).length < 2 ^ (prefixWord ++ tailWord_5131538).sum := by decide
  have hdescent : baseEnd_5131538 < baseStart_5131538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131544 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 2, 3, 2]
def baseStart_5131544 : Nat := 118140960795 + 5131544 * 2 ^ 59
def prefixEnd_5131544 : Nat := 4983230072969 + 3 ^ 40 * 5131544 * 2
def baseEnd_5131544 : Nat := 2634948571695576044200465

theorem tailTrace_5131544 : CollatzResearch.WordTrace tailWord_5131544 prefixEnd_5131544 2634948571695576044200465 := by
  unfold tailWord_5131544
  simp only [CollatzResearch.WordTrace]
  refine ⟨93581392860649980393352843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124775190480866640524470457 93581392860649980393352843)
  ·
    refine ⟨140372089290974970590029265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93581392860649980393352843 140372089290974970590029265)
    ·
      refine ⟨105279066968231227942521949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140372089290974970590029265 105279066968231227942521949)
      ·
        refine ⟨39479650113086710478445731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105279066968231227942521949 39479650113086710478445731)
        ·
          refine ⟨59219475169630065717668597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39479650113086710478445731 59219475169630065717668597)
          ·
            refine ⟨5551825797152818661031431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59219475169630065717668597 5551825797152818661031431)
            ·
              refine ⟨8327738695729227991547147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551825797152818661031431 8327738695729227991547147)
              ·
                refine ⟨12491608043593841987320721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327738695729227991547147 12491608043593841987320721)
                ·
                  refine ⟨9368706032695381490490541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12491608043593841987320721 9368706032695381490490541)
                  ·
                    refine ⟨3513264762260768058933953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9368706032695381490490541 3513264762260768058933953)
                    ·
                      refine ⟨2634948571695576044200465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513264762260768058933953 2634948571695576044200465)
                      ·
                        rfl

theorem cell23_5131544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_5131544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131544 prefixEnd_5131544 := by exact prefixLift 5131544
  have htrace : WordTrace (prefixWord ++ tailWord_5131544) baseStart_5131544 baseEnd_5131544 := by
    simpa [prefixWord, tailWord_5131544, baseEnd_5131544] using wordTrace_append hprefix tailTrace_5131544
  have hstable : (prefixWord ++ tailWord_5131544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131544).length < 2 ^ (prefixWord ++ tailWord_5131544).sum := by decide
  have hdescent : baseEnd_5131544 < baseStart_5131544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131551 : List Nat := [1, 1, 2, 4, 4, 1, 2, 3, 1, 1, 3]
def baseStart_5131551 : Nat := 118140960795 + 5131551 * 2 ^ 59
def prefixEnd_5131551 : Nat := 4983230072969 + 3 ^ 40 * 5131551 * 2
def baseEnd_5131551 : Nat := 2634952166060157516812933

theorem tailTrace_5131551 : CollatzResearch.WordTrace tailWord_5131551 prefixEnd_5131551 2634952166060157516812933 := by
  unfold tailWord_5131551
  simp only [CollatzResearch.WordTrace]
  refine ⟨187163041032274600982210507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124775360688183067321473671 187163041032274600982210507)
  ·
    refine ⟨280744561548411901473315761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187163041032274600982210507 280744561548411901473315761)
    ·
      refine ⟨210558421161308926104986821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280744561548411901473315761 210558421161308926104986821)
      ·
        refine ⟨39479703967745423644685029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210558421161308926104986821 39479703967745423644685029)
        ·
          refine ⟨7402444493952266933378443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39479703967745423644685029 7402444493952266933378443)
          ·
            refine ⟨11103666740928400400067665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7402444493952266933378443 11103666740928400400067665)
            ·
              refine ⟨8327750055696300300050749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11103666740928400400067665 8327750055696300300050749)
              ·
                refine ⟨3122906270886112612519031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8327750055696300300050749 3122906270886112612519031)
                ·
                  refine ⟨4684359406329168918778547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122906270886112612519031 4684359406329168918778547)
                  ·
                    refine ⟨7026539109493753378167821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4684359406329168918778547 7026539109493753378167821)
                    ·
                      refine ⟨2634952166060157516812933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7026539109493753378167821 2634952166060157516812933)
                      ·
                        rfl

theorem cell23_5131551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_5131551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131551 prefixEnd_5131551 := by exact prefixLift 5131551
  have htrace : WordTrace (prefixWord ++ tailWord_5131551) baseStart_5131551 baseEnd_5131551 := by
    simpa [prefixWord, tailWord_5131551, baseEnd_5131551] using wordTrace_append hprefix tailTrace_5131551
  have hstable : (prefixWord ++ tailWord_5131551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131551).length < 2 ^ (prefixWord ++ tailWord_5131551).sum := by decide
  have hdescent : baseEnd_5131551 < baseStart_5131551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131553 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_5131553 : Nat := 118140960795 + 5131553 * 2 ^ 59
def prefixEnd_5131553 : Nat := 4983230072969 + 3 ^ 40 * 5131553 * 2
def baseEnd_5131553 : Nat := 2634953193021466508987923

theorem tailTrace_5131553 : CollatzResearch.WordTrace tailWord_5131553 prefixEnd_5131553 2634953193021466508987923 := by
  unfold tailWord_5131553
  simp only [CollatzResearch.WordTrace]
  refine ⟨187163113978267355323783313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124775409318844903549188875 187163113978267355323783313)
  ·
    refine ⟨140372335483700516492837485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187163113978267355323783313 140372335483700516492837485)
    ·
      refine ⟨52639625806387693684814057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140372335483700516492837485 52639625806387693684814057)
      ·
        refine ⟨39479719354790770263610543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52639625806387693684814057 39479719354790770263610543)
        ·
          refine ⟨59219579032186155395415815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39479719354790770263610543 59219579032186155395415815)
          ·
            refine ⟨88829368548279233093123723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59219579032186155395415815 88829368548279233093123723)
            ·
              refine ⟨133244052822418849639685585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88829368548279233093123723 133244052822418849639685585)
              ·
                refine ⟨99933039616814137229764189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133244052822418849639685585 99933039616814137229764189)
                ·
                  refine ⟨37474889856305301461161571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99933039616814137229764189 37474889856305301461161571)
                  ·
                    refine ⟨56212334784457952191742357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37474889856305301461161571 56212334784457952191742357)
                    ·
                      refine ⟨2634953193021466508987923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56212334784457952191742357 2634953193021466508987923)
                      ·
                        rfl

theorem cell23_5131553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_5131553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131553 prefixEnd_5131553 := by exact prefixLift 5131553
  have htrace : WordTrace (prefixWord ++ tailWord_5131553) baseStart_5131553 baseEnd_5131553 := by
    simpa [prefixWord, tailWord_5131553, baseEnd_5131553] using wordTrace_append hprefix tailTrace_5131553
  have hstable : (prefixWord ++ tailWord_5131553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131553).length < 2 ^ (prefixWord ++ tailWord_5131553).sum := by decide
  have hdescent : baseEnd_5131553 < baseStart_5131553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131557 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 4]
def baseStart_5131557 : Nat := 118140960795 + 5131557 * 2 ^ 59
def prefixEnd_5131557 : Nat := 4983230072969 + 3 ^ 40 * 5131557 * 2
def baseEnd_5131557 : Nat := 2634955246944084493337905

theorem tailTrace_5131557 : CollatzResearch.WordTrace tailWord_5131557 prefixEnd_5131557 2634955246944084493337905 := by
  unfold tailWord_5131557
  simp only [CollatzResearch.WordTrace]
  refine ⟨187163259870252864006928925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124775506580168576004619283 187163259870252864006928925)
  ·
    refine ⟨70186222451344824002598347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187163259870252864006928925 70186222451344824002598347)
    ·
      refine ⟨105279333677017236003897521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70186222451344824002598347 105279333677017236003897521)
      ·
        refine ⟨78959500257762927002923141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105279333677017236003897521 78959500257762927002923141)
        ·
          refine ⟨14804906298330548813048089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78959500257762927002923141 14804906298330548813048089)
          ·
            refine ⟨11103679723747911609786067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14804906298330548813048089 11103679723747911609786067)
            ·
              refine ⟨16655519585621867414679101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11103679723747911609786067 16655519585621867414679101)
              ·
                refine ⟨6245819844608200280504663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16655519585621867414679101 6245819844608200280504663)
                ·
                  refine ⟨9368729766912300420756995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6245819844608200280504663 9368729766912300420756995)
                  ·
                    refine ⟨14053094650368450631135493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9368729766912300420756995 14053094650368450631135493)
                    ·
                      refine ⟨2634955246944084493337905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14053094650368450631135493 2634955246944084493337905)
                      ·
                        rfl

theorem cell23_5131557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_5131557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131557 prefixEnd_5131557 := by exact prefixLift 5131557
  have htrace : WordTrace (prefixWord ++ tailWord_5131557) baseStart_5131557 baseEnd_5131557 := by
    simpa [prefixWord, tailWord_5131557, baseEnd_5131557] using wordTrace_append hprefix tailTrace_5131557
  have hstable : (prefixWord ++ tailWord_5131557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131557).length < 2 ^ (prefixWord ++ tailWord_5131557).sum := by decide
  have hdescent : baseEnd_5131557 < baseStart_5131557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131577 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5131577 : Nat := 118140960795 + 5131577 * 2 ^ 59
def prefixEnd_5131577 : Nat := 4983230072969 + 3 ^ 40 * 5131577 * 2
def baseEnd_5131577 : Nat := 2634965516557174415087813

theorem tailTrace_5131577 : CollatzResearch.WordTrace tailWord_5131577 prefixEnd_5131577 2634965516557174415087813 := by
  unfold tailWord_5131577
  simp only [CollatzResearch.WordTrace]
  refine ⟨187163989330180407422656985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124775992886786938281771323 187163989330180407422656985)
  ·
    refine ⟨140372991997635305566992739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187163989330180407422656985 140372991997635305566992739)
    ·
      refine ⟨210559487996452958350489109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140372991997635305566992739 210559487996452958350489109)
      ·
        refine ⟨9869975999833732422679177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 210559487996452958350489109 9869975999833732422679177)
        ·
          refine ⟨7402481999875299317009383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9869975999833732422679177 7402481999875299317009383)
          ·
            refine ⟨11103722999812948975514075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7402481999875299317009383 11103722999812948975514075)
            ·
              refine ⟨16655584499719423463271113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11103722999812948975514075 16655584499719423463271113)
              ·
                refine ⟨12491688374789567597453335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16655584499719423463271113 12491688374789567597453335)
                ·
                  refine ⟨18737532562184351396180003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12491688374789567597453335 18737532562184351396180003)
                  ·
                    refine ⟨28106298843276527094270005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18737532562184351396180003 28106298843276527094270005)
                    ·
                      refine ⟨2634965516557174415087813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28106298843276527094270005 2634965516557174415087813)
                      ·
                        rfl

theorem cell23_5131577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5131577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131577 prefixEnd_5131577 := by exact prefixLift 5131577
  have htrace : WordTrace (prefixWord ++ tailWord_5131577) baseStart_5131577 baseEnd_5131577 := by
    simpa [prefixWord, tailWord_5131577, baseEnd_5131577] using wordTrace_append hprefix tailTrace_5131577
  have hstable : (prefixWord ++ tailWord_5131577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131577).length < 2 ^ (prefixWord ++ tailWord_5131577).sum := by decide
  have hdescent : baseEnd_5131577 < baseStart_5131577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131593 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 2, 7]
def baseStart_5131593 : Nat := 118140960795 + 5131593 * 2 ^ 59
def prefixEnd_5131593 : Nat := 4983230072969 + 3 ^ 40 * 5131593 * 2
def baseEnd_5131593 : Nat := 878324577415882117495913

theorem tailTrace_5131593 : CollatzResearch.WordTrace tailWord_5131593 prefixEnd_5131593 878324577415882117495913 := by
  unfold tailWord_5131593
  simp only [CollatzResearch.WordTrace]
  refine ⟨187164572898122442155239433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124776381932081628103492955 187164572898122442155239433)
  ·
    refine ⟨140373429673591831616429575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187164572898122442155239433 140373429673591831616429575)
    ·
      refine ⟨210560144510387747424644363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140373429673591831616429575 210560144510387747424644363)
      ·
        refine ⟨315840216765581621136966545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210560144510387747424644363 315840216765581621136966545)
        ·
          refine ⟨236880162574186215852724909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315840216765581621136966545 236880162574186215852724909)
          ·
            refine ⟨88830060965319830944771841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236880162574186215852724909 88830060965319830944771841)
            ·
              refine ⟨66622545723989873208578881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88830060965319830944771841 66622545723989873208578881)
              ·
                refine ⟨49966909292992404906434161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66622545723989873208578881 49966909292992404906434161)
                ·
                  refine ⟨37475181969744303679825621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49966909292992404906434161 37475181969744303679825621)
                  ·
                    refine ⟨878324577415882117495913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37475181969744303679825621 878324577415882117495913)
                    ·
                      rfl

theorem cell23_5131593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_5131593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131593 prefixEnd_5131593 := by exact prefixLift 5131593
  have htrace : WordTrace (prefixWord ++ tailWord_5131593) baseStart_5131593 baseEnd_5131593 := by
    simpa [prefixWord, tailWord_5131593, baseEnd_5131593] using wordTrace_append hprefix tailTrace_5131593
  have hstable : (prefixWord ++ tailWord_5131593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131593).length < 2 ^ (prefixWord ++ tailWord_5131593).sum := by decide
  have hdescent : baseEnd_5131593 < baseStart_5131593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131603 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 5]
def baseStart_5131603 : Nat := 118140960795 + 5131603 * 2 ^ 59
def prefixEnd_5131603 : Nat := 4983230072969 + 3 ^ 40 * 5131603 * 2
def baseEnd_5131603 : Nat := 2634978867054191313362693

theorem tailTrace_5131603 : CollatzResearch.WordTrace tailWord_5131603 prefixEnd_5131603 2634978867054191313362693 := by
  unfold tailWord_5131603
  simp only [CollatzResearch.WordTrace]
  refine ⟨187164937628086213863103463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124776625085390809242068975 187164937628086213863103463)
  ·
    refine ⟨280747406442129320794655195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187164937628086213863103463 280747406442129320794655195)
    ·
      refine ⟨421121109663193981191982793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280747406442129320794655195 421121109663193981191982793)
      ·
        refine ⟨315840832247395485893987095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421121109663193981191982793 315840832247395485893987095)
        ·
          refine ⟨473761248371093228840980643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315840832247395485893987095 473761248371093228840980643)
          ·
            refine ⟨710641872556639843261470965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473761248371093228840980643 710641872556639843261470965)
            ·
              refine ⟨66622675552184985305762903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 710641872556639843261470965 66622675552184985305762903)
              ·
                refine ⟨99934013328277477958644355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66622675552184985305762903 99934013328277477958644355)
                ·
                  refine ⟨149901019992416216937966533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99934013328277477958644355 149901019992416216937966533)
                  ·
                    refine ⟨28106441248578040675868725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149901019992416216937966533 28106441248578040675868725)
                    ·
                      refine ⟨2634978867054191313362693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28106441248578040675868725 2634978867054191313362693)
                      ·
                        rfl

theorem cell23_5131603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_5131603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131603 prefixEnd_5131603 := by exact prefixLift 5131603
  have htrace : WordTrace (prefixWord ++ tailWord_5131603) baseStart_5131603 baseEnd_5131603 := by
    simpa [prefixWord, tailWord_5131603, baseEnd_5131603] using wordTrace_append hprefix tailTrace_5131603
  have hstable : (prefixWord ++ tailWord_5131603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131603).length < 2 ^ (prefixWord ++ tailWord_5131603).sum := by decide
  have hdescent : baseEnd_5131603 < baseStart_5131603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131607 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 3]
def baseStart_5131607 : Nat := 118140960795 + 5131607 * 2 ^ 59
def prefixEnd_5131607 : Nat := 4983230072969 + 3 ^ 40 * 5131607 * 2
def baseEnd_5131607 : Nat := 2634980920976809297712675

theorem tailTrace_5131607 : CollatzResearch.WordTrace tailWord_5131607 prefixEnd_5131607 2634980920976809297712675 := by
  unfold tailWord_5131607
  simp only [CollatzResearch.WordTrace]
  refine ⟨187165083520071722546249075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124776722346714481697499383 187165083520071722546249075)
  ·
    refine ⟨280747625280107583819373613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187165083520071722546249075 280747625280107583819373613)
    ·
      refine ⟨105280359480040343932265105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280747625280107583819373613 105280359480040343932265105)
      ·
        refine ⟨78960269610030257949198829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105280359480040343932265105 78960269610030257949198829)
        ·
          refine ⟨29610101103761346730949561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78960269610030257949198829 29610101103761346730949561)
          ·
            refine ⟨22207575827821010048212171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29610101103761346730949561 22207575827821010048212171)
            ·
              refine ⟨33311363741731515072318257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22207575827821010048212171 33311363741731515072318257)
              ·
                refine ⟨24983522806298636304238693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33311363741731515072318257 24983522806298636304238693)
                ·
                  refine ⟨4684410526180994307044755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24983522806298636304238693 4684410526180994307044755)
                  ·
                    refine ⟨7026615789271491460567133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4684410526180994307044755 7026615789271491460567133)
                    ·
                      refine ⟨2634980920976809297712675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7026615789271491460567133 2634980920976809297712675)
                      ·
                        rfl

theorem cell23_5131607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_5131607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131607 prefixEnd_5131607 := by exact prefixLift 5131607
  have htrace : WordTrace (prefixWord ++ tailWord_5131607) baseStart_5131607 baseEnd_5131607 := by
    simpa [prefixWord, tailWord_5131607, baseEnd_5131607] using wordTrace_append hprefix tailTrace_5131607
  have hstable : (prefixWord ++ tailWord_5131607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131607).length < 2 ^ (prefixWord ++ tailWord_5131607).sum := by decide
  have hdescent : baseEnd_5131607 < baseStart_5131607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131651 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 1, 3, 2]
def baseStart_5131651 : Nat := 118140960795 + 5131651 * 2 ^ 59
def prefixEnd_5131651 : Nat := 4983230072969 + 3 ^ 40 * 5131651 * 2
def baseEnd_5131651 : Nat := 2635003514125607125562473

theorem tailTrace_5131651 : CollatzResearch.WordTrace tailWord_5131651 prefixEnd_5131651 2635003514125607125562473 := by
  unfold tailWord_5131651
  simp only [CollatzResearch.WordTrace]
  refine ⟨187166688331912318060850807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124777792221274878707233871 187166688331912318060850807)
  ·
    refine ⟨280750032497868477091276211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187166688331912318060850807 280750032497868477091276211)
    ·
      refine ⟨421125048746802715636914317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280750032497868477091276211 421125048746802715636914317)
      ·
        refine ⟨157921893280051018363842869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421125048746802715636914317 157921893280051018363842869)
        ·
          refine ⟨14805177495004782971610269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157921893280051018363842869 14805177495004782971610269)
          ·
            refine ⟨5551941560626793614353851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14805177495004782971610269 5551941560626793614353851)
            ·
              refine ⟨8327912340940190421530777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551941560626793614353851 8327912340940190421530777)
              ·
                refine ⟨6245934255705142816148083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8327912340940190421530777 6245934255705142816148083)
                ·
                  refine ⟨9368901383557714224222125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6245934255705142816148083 9368901383557714224222125)
                  ·
                    refine ⟨3513338018834142834083297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9368901383557714224222125 3513338018834142834083297)
                    ·
                      refine ⟨2635003514125607125562473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513338018834142834083297 2635003514125607125562473)
                      ·
                        rfl

theorem cell23_5131651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_5131651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131651 prefixEnd_5131651 := by exact prefixLift 5131651
  have htrace : WordTrace (prefixWord ++ tailWord_5131651) baseStart_5131651 baseEnd_5131651 := by
    simpa [prefixWord, tailWord_5131651, baseEnd_5131651] using wordTrace_append hprefix tailTrace_5131651
  have hstable : (prefixWord ++ tailWord_5131651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131651).length < 2 ^ (prefixWord ++ tailWord_5131651).sum := by decide
  have hdescent : baseEnd_5131651 < baseStart_5131651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131668 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_5131668 : Nat := 118140960795 + 5131668 * 2 ^ 59
def prefixEnd_5131668 : Nat := 4983230072969 + 3 ^ 40 * 5131668 * 2
def baseEnd_5131668 : Nat := 2635012243296733559049895

theorem tailTrace_5131668 : CollatzResearch.WordTrace tailWord_5131668 prefixEnd_5131668 2635012243296733559049895 := by
  unfold tailWord_5131668
  simp only [CollatzResearch.WordTrace]
  refine ⟨93583654186425364982109829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124778205581900486642813105 93583654186425364982109829)
  ·
    refine ⟨17546935159954755934145593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93583654186425364982109829 17546935159954755934145593)
    ·
      refine ⟨13160201369966066950609195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17546935159954755934145593 13160201369966066950609195)
      ·
        refine ⟨19740302054949100425913793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13160201369966066950609195 19740302054949100425913793)
        ·
          refine ⟨14805226541211825319435345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19740302054949100425913793 14805226541211825319435345)
          ·
            refine ⟨11103919905908868989576509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14805226541211825319435345 11103919905908868989576509)
            ·
              refine ⟨4163969964715825871091191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11103919905908868989576509 4163969964715825871091191)
              ·
                refine ⟨6245954947073738806636787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163969964715825871091191 6245954947073738806636787)
                ·
                  refine ⟨9368932420610608209955181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6245954947073738806636787 9368932420610608209955181)
                  ·
                    refine ⟨3513349657728978078733193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9368932420610608209955181 3513349657728978078733193)
                    ·
                      refine ⟨2635012243296733559049895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513349657728978078733193 2635012243296733559049895)
                      ·
                        rfl

theorem cell23_5131668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_5131668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131668 prefixEnd_5131668 := by exact prefixLift 5131668
  have htrace : WordTrace (prefixWord ++ tailWord_5131668) baseStart_5131668 baseEnd_5131668 := by
    simpa [prefixWord, tailWord_5131668, baseEnd_5131668] using wordTrace_append hprefix tailTrace_5131668
  have hstable : (prefixWord ++ tailWord_5131668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131668).length < 2 ^ (prefixWord ++ tailWord_5131668).sum := by decide
  have hdescent : baseEnd_5131668 < baseStart_5131668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131697 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_5131697 : Nat := 118140960795 + 5131697 * 2 ^ 59
def prefixEnd_5131697 : Nat := 4983230072969 + 3 ^ 40 * 5131697 * 2
def baseEnd_5131697 : Nat := 2635027134235713945587261

theorem tailTrace_5131697 : CollatzResearch.WordTrace tailWord_5131697 prefixEnd_5131697 2635027134235713945587261 := by
  unfold tailWord_5131697
  simp only [CollatzResearch.WordTrace]
  refine ⟨187168366089745667917025345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124778910726497111944683563 187168366089745667917025345)
  ·
    refine ⟨140376274567309250937769009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187168366089745667917025345 140376274567309250937769009)
    ·
      refine ⟨105282205925481938203326757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140376274567309250937769009 105282205925481938203326757)
      ·
        refine ⟨19740413611027863413123767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105282205925481938203326757 19740413611027863413123767)
        ·
          refine ⟨29610620416541795119685651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19740413611027863413123767 29610620416541795119685651)
          ·
            refine ⟨44415930624812692679528477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29610620416541795119685651 44415930624812692679528477)
            ·
              refine ⟨16655973984304759754823179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44415930624812692679528477 16655973984304759754823179)
              ·
                refine ⟨24983960976457139632234769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16655973984304759754823179 24983960976457139632234769)
                ·
                  refine ⟨18737970732342854724176077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24983960976457139632234769 18737970732342854724176077)
                  ·
                    refine ⟨7026739024628570521566029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18737970732342854724176077 7026739024628570521566029)
                    ·
                      refine ⟨2635027134235713945587261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7026739024628570521566029 2635027134235713945587261)
                      ·
                        rfl

theorem cell23_5131697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_5131697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131697 prefixEnd_5131697 := by exact prefixLift 5131697
  have htrace : WordTrace (prefixWord ++ tailWord_5131697) baseStart_5131697 baseEnd_5131697 := by
    simpa [prefixWord, tailWord_5131697, baseEnd_5131697] using wordTrace_append hprefix tailTrace_5131697
  have hstable : (prefixWord ++ tailWord_5131697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131697).length < 2 ^ (prefixWord ++ tailWord_5131697).sum := by decide
  have hdescent : baseEnd_5131697 < baseStart_5131697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131811 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 6]
def baseStart_5131811 : Nat := 118140960795 + 5131811 * 2 ^ 59
def prefixEnd_5131811 : Nat := 4983230072969 + 3 ^ 40 * 5131811 * 2
def baseEnd_5131811 : Nat := 292787296781147388840193

theorem tailTrace_5131811 : CollatzResearch.WordTrace tailWord_5131811 prefixEnd_5131811 292787296781147388840193 := by
  unfold tailWord_5131811
  simp only [CollatzResearch.WordTrace]
  refine ⟨187172524011332665386675287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124781682674221776924450191 187172524011332665386675287)
  ·
    refine ⟨280758786016998998080012931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187172524011332665386675287 280758786016998998080012931)
    ·
      refine ⟨421138179025498497120019397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280758786016998998080012931 421138179025498497120019397)
      ·
        refine ⟨78963408567280968210003637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 421138179025498497120019397 78963408567280968210003637)
        ·
          refine ⟨7402819553182590769687841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78963408567280968210003637 7402819553182590769687841)
          ·
            refine ⟨5552114664886943077265881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7402819553182590769687841 5552114664886943077265881)
            ·
              refine ⟨4164085998665207307949411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5552114664886943077265881 4164085998665207307949411)
              ·
                refine ⟨6246128997997810961924117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164085998665207307949411 6246128997997810961924117)
                ·
                  refine ⟨292787296781147388840193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6246128997997810961924117 292787296781147388840193)
                  ·
                    rfl

theorem cell23_5131811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 6].length) (baseStart_5131811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131811 prefixEnd_5131811 := by exact prefixLift 5131811
  have htrace : WordTrace (prefixWord ++ tailWord_5131811) baseStart_5131811 baseEnd_5131811 := by
    simpa [prefixWord, tailWord_5131811, baseEnd_5131811] using wordTrace_append hprefix tailTrace_5131811
  have hstable : (prefixWord ++ tailWord_5131811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131811).length < 2 ^ (prefixWord ++ tailWord_5131811).sum := by decide
  have hdescent : baseEnd_5131811 < baseStart_5131811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131831 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 2, 3, 2]
def baseStart_5131831 : Nat := 118140960795 + 5131831 * 2 ^ 59
def prefixEnd_5131831 : Nat := 4983230072969 + 3 ^ 40 * 5131831 * 2
def baseEnd_5131831 : Nat := 2635095940643416421311645

theorem tailTrace_5131831 : CollatzResearch.WordTrace tailWord_5131831 prefixEnd_5131831 2635095940643416421311645 := by
  unfold tailWord_5131831
  simp only [CollatzResearch.WordTrace]
  refine ⟨187173253471260208802403347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124782168980840139201602231 187173253471260208802403347)
  ·
    refine ⟨280759880206890313203605021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187173253471260208802403347 280759880206890313203605021)
    ·
      refine ⟨105284955077583867451351883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280759880206890313203605021 105284955077583867451351883)
      ·
        refine ⟨157927432616375801177027825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105284955077583867451351883 157927432616375801177027825)
        ·
          refine ⟨118445574462281850882770869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157927432616375801177027825 118445574462281850882770869)
          ·
            refine ⟨11104272605838923520259769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118445574462281850882770869 11104272605838923520259769)
            ·
              refine ⟨8328204454379192640194827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11104272605838923520259769 8328204454379192640194827)
              ·
                refine ⟨12492306681568788960292241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8328204454379192640194827 12492306681568788960292241)
                ·
                  refine ⟨9369230011176591720219181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12492306681568788960292241 9369230011176591720219181)
                  ·
                    refine ⟨3513461254191221895082193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9369230011176591720219181 3513461254191221895082193)
                    ·
                      refine ⟨2635095940643416421311645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513461254191221895082193 2635095940643416421311645)
                      ·
                        rfl

theorem cell23_5131831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_5131831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131831 prefixEnd_5131831 := by exact prefixLift 5131831
  have htrace : WordTrace (prefixWord ++ tailWord_5131831) baseStart_5131831 baseEnd_5131831 := by
    simpa [prefixWord, tailWord_5131831, baseEnd_5131831] using wordTrace_append hprefix tailTrace_5131831
  have hstable : (prefixWord ++ tailWord_5131831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131831).length < 2 ^ (prefixWord ++ tailWord_5131831).sum := by decide
  have hdescent : baseEnd_5131831 < baseStart_5131831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131841 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 1, 5]
def baseStart_5131841 : Nat := 118140960795 + 5131841 * 2 ^ 59
def prefixEnd_5131841 : Nat := 4983230072969 + 3 ^ 40 * 5131841 * 2
def baseEnd_5131841 : Nat := 878367025149987127395533

theorem tailTrace_5131841 : CollatzResearch.WordTrace tailWord_5131841 prefixEnd_5131841 878367025149987127395533 := by
  unfold tailWord_5131841
  simp only [CollatzResearch.WordTrace]
  refine ⟨187173618201223980510267377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124782412134149320340178251 187173618201223980510267377)
  ·
    refine ⟨140380213650917985382700533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187173618201223980510267377 140380213650917985382700533)
    ·
      refine ⟨13160645029773561129628175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140380213650917985382700533 13160645029773561129628175)
      ·
        refine ⟨19740967544660341694442263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13160645029773561129628175 19740967544660341694442263)
        ·
          refine ⟨29611451316990512541663395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19740967544660341694442263 29611451316990512541663395)
          ·
            refine ⟨44417176975485768812495093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29611451316990512541663395 44417176975485768812495093)
            ·
              refine ⟨4164110341451790826171415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44417176975485768812495093 4164110341451790826171415)
              ·
                refine ⟨6246165512177686239257123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164110341451790826171415 6246165512177686239257123)
                ·
                  refine ⟨9369248268266529358885685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6246165512177686239257123 9369248268266529358885685)
                  ·
                    refine ⟨878367025149987127395533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9369248268266529358885685 878367025149987127395533)
                    ·
                      rfl

theorem cell23_5131841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_5131841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131841 prefixEnd_5131841 := by exact prefixLift 5131841
  have htrace : WordTrace (prefixWord ++ tailWord_5131841) baseStart_5131841 baseEnd_5131841 := by
    simpa [prefixWord, tailWord_5131841, baseEnd_5131841] using wordTrace_append hprefix tailTrace_5131841
  have hstable : (prefixWord ++ tailWord_5131841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131841).length < 2 ^ (prefixWord ++ tailWord_5131841).sum := by decide
  have hdescent : baseEnd_5131841 < baseStart_5131841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131857 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_5131857 : Nat := 118140960795 + 5131857 * 2 ^ 59
def prefixEnd_5131857 : Nat := 4983230072969 + 3 ^ 40 * 5131857 * 2
def baseEnd_5131857 : Nat := 2635109291140433319586525

theorem tailTrace_5131857 : CollatzResearch.WordTrace tailWord_5131857 prefixEnd_5131857 2635109291140433319586525 := by
  unfold tailWord_5131857
  simp only [CollatzResearch.WordTrace]
  refine ⟨187174201769166015242849825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124782801179444010161899883 187174201769166015242849825)
  ·
    refine ⟨140380651326874511432137369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187174201769166015242849825 140380651326874511432137369)
    ·
      refine ⟨105285488495155883574103027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140380651326874511432137369 105285488495155883574103027)
      ·
        refine ⟨157928232742733825361154541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105285488495155883574103027 157928232742733825361154541)
        ·
          refine ⟨59223087278525184510432953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157928232742733825361154541 59223087278525184510432953)
          ·
            refine ⟨44417315458893888382824715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59223087278525184510432953 44417315458893888382824715)
            ·
              refine ⟨66625973188340832574237073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44417315458893888382824715 66625973188340832574237073)
              ·
                refine ⟨49969479891255624430677805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66625973188340832574237073 49969479891255624430677805)
                ·
                  refine ⟨18738554959220859161504177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49969479891255624430677805 18738554959220859161504177)
                  ·
                    refine ⟨14053916219415644371128133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18738554959220859161504177 14053916219415644371128133)
                    ·
                      refine ⟨2635109291140433319586525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14053916219415644371128133 2635109291140433319586525)
                      ·
                        rfl

theorem cell23_5131857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_5131857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131857 prefixEnd_5131857 := by exact prefixLift 5131857
  have htrace : WordTrace (prefixWord ++ tailWord_5131857) baseStart_5131857 baseEnd_5131857 := by
    simpa [prefixWord, tailWord_5131857, baseEnd_5131857] using wordTrace_append hprefix tailTrace_5131857
  have hstable : (prefixWord ++ tailWord_5131857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131857).length < 2 ^ (prefixWord ++ tailWord_5131857).sum := by decide
  have hdescent : baseEnd_5131857 < baseStart_5131857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131861 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_5131861 : Nat := 118140960795 + 5131861 * 2 ^ 59
def prefixEnd_5131861 : Nat := 4983230072969 + 3 ^ 40 * 5131861 * 2
def baseEnd_5131861 : Nat := 2635111345063051303936507

theorem tailTrace_5131861 : CollatzResearch.WordTrace tailWord_5131861 prefixEnd_5131861 2635111345063051303936507 := by
  unfold tailWord_5131861
  simp only [CollatzResearch.WordTrace]
  refine ⟨187174347661151523925995437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124782898440767682617330291 187174347661151523925995437)
  ·
    refine ⟨70190380372931821472248289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187174347661151523925995437 70190380372931821472248289)
    ·
      refine ⟨52642785279698866104186217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70190380372931821472248289 52642785279698866104186217)
      ·
        refine ⟨39482088959774149578139663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52642785279698866104186217 39482088959774149578139663)
        ·
          refine ⟨59223133439661224367209495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39482088959774149578139663 59223133439661224367209495)
          ·
            refine ⟨88834700159491836550814243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59223133439661224367209495 88834700159491836550814243)
            ·
              refine ⟨133252050239237754826221365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88834700159491836550814243 133252050239237754826221365)
              ·
                refine ⟨12492379709928539514958253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133252050239237754826221365 12492379709928539514958253)
                ·
                  refine ⟨4684642391223202318109345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12492379709928539514958253 4684642391223202318109345)
                  ·
                    refine ⟨3513481793417401738582009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4684642391223202318109345 3513481793417401738582009)
                    ·
                      refine ⟨2635111345063051303936507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513481793417401738582009 2635111345063051303936507)
                      ·
                        rfl

theorem cell23_5131861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_5131861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131861 prefixEnd_5131861 := by exact prefixLift 5131861
  have htrace : WordTrace (prefixWord ++ tailWord_5131861) baseStart_5131861 baseEnd_5131861 := by
    simpa [prefixWord, tailWord_5131861, baseEnd_5131861] using wordTrace_append hprefix tailTrace_5131861
  have hstable : (prefixWord ++ tailWord_5131861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131861).length < 2 ^ (prefixWord ++ tailWord_5131861).sum := by decide
  have hdescent : baseEnd_5131861 < baseStart_5131861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131911 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_5131911 : Nat := 118140960795 + 5131911 * 2 ^ 59
def prefixEnd_5131911 : Nat := 4983230072969 + 3 ^ 40 * 5131911 * 2
def baseEnd_5131911 : Nat := 2635137019095776108311277

theorem tailTrace_5131911 : CollatzResearch.WordTrace tailWord_5131911 prefixEnd_5131911 2635137019095776108311277 := by
  unfold tailWord_5131911
  simp only [CollatzResearch.WordTrace]
  refine ⟨187176171310970382465315587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124784114207313588310210391 187176171310970382465315587)
  ·
    refine ⟨280764256966455573697973381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187176171310970382465315587 280764256966455573697973381)
    ·
      refine ⟨52643298181210420068370009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280764256966455573697973381 52643298181210420068370009)
      ·
        refine ⟨39482473635907815051277507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52643298181210420068370009 39482473635907815051277507)
        ·
          refine ⟨59223710453861722576916261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39482473635907815051277507 59223710453861722576916261)
          ·
            refine ⟨11104445710099072983171799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59223710453861722576916261 11104445710099072983171799)
            ·
              refine ⟨16656668565148609474757699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11104445710099072983171799 16656668565148609474757699)
              ·
                refine ⟨24985002847722914212136549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16656668565148609474757699 24985002847722914212136549)
                ·
                  refine ⟨4684688033948046414775603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24985002847722914212136549 4684688033948046414775603)
                  ·
                    refine ⟨7027032050922069622163405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4684688033948046414775603 7027032050922069622163405)
                    ·
                      refine ⟨2635137019095776108311277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7027032050922069622163405 2635137019095776108311277)
                      ·
                        rfl

theorem cell23_5131911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_5131911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131911 prefixEnd_5131911 := by exact prefixLift 5131911
  have htrace : WordTrace (prefixWord ++ tailWord_5131911) baseStart_5131911 baseEnd_5131911 := by
    simpa [prefixWord, tailWord_5131911, baseEnd_5131911] using wordTrace_append hprefix tailTrace_5131911
  have hstable : (prefixWord ++ tailWord_5131911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131911).length < 2 ^ (prefixWord ++ tailWord_5131911).sum := by decide
  have hdescent : baseEnd_5131911 < baseStart_5131911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131951 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 6, 2, 2]
def baseStart_5131951 : Nat := 118140960795 + 5131951 * 2 ^ 59
def prefixEnd_5131951 : Nat := 4983230072969 + 3 ^ 40 * 5131951 * 2
def baseEnd_5131951 : Nat := 2635157558321955951811093

theorem tailTrace_5131951 : CollatzResearch.WordTrace tailWord_5131951 prefixEnd_5131951 2635157558321955951811093 := by
  unfold tailWord_5131951
  simp only [CollatzResearch.WordTrace]
  refine ⟨187177630230825469296771707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124785086820550312864514471 187177630230825469296771707)
  ·
    refine ⟨280766445346238203945157561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187177630230825469296771707 280766445346238203945157561)
    ·
      refine ⟨210574834009678652958868171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280766445346238203945157561 210574834009678652958868171)
      ·
        refine ⟨315862251014517979438302257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210574834009678652958868171 315862251014517979438302257)
        ·
          refine ⟨236896688260888484578726693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315862251014517979438302257 236896688260888484578726693)
          ·
            refine ⟨44418129048916590858511255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236896688260888484578726693 44418129048916590858511255)
            ·
              refine ⟨66627193573374886287766883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44418129048916590858511255 66627193573374886287766883)
              ·
                refine ⟨99940790360062329431650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66627193573374886287766883 99940790360062329431650325)
                ·
                  refine ⟨4684724548127921692108609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99940790360062329431650325 4684724548127921692108609)
                  ·
                    refine ⟨3513543411095941269081457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4684724548127921692108609 3513543411095941269081457)
                    ·
                      refine ⟨2635157558321955951811093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513543411095941269081457 2635157558321955951811093)
                      ·
                        rfl

theorem cell23_5131951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 2, 2].length) (baseStart_5131951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131951 prefixEnd_5131951 := by exact prefixLift 5131951
  have htrace : WordTrace (prefixWord ++ tailWord_5131951) baseStart_5131951 baseEnd_5131951 := by
    simpa [prefixWord, tailWord_5131951, baseEnd_5131951] using wordTrace_append hprefix tailTrace_5131951
  have hstable : (prefixWord ++ tailWord_5131951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131951).length < 2 ^ (prefixWord ++ tailWord_5131951).sum := by decide
  have hdescent : baseEnd_5131951 < baseStart_5131951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131967 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_5131967 : Nat := 118140960795 + 5131967 * 2 ^ 59
def prefixEnd_5131967 : Nat := 4983230072969 + 3 ^ 40 * 5131967 * 2
def baseEnd_5131967 : Nat := 2635165774012427889211019

theorem tailTrace_5131967 : CollatzResearch.WordTrace tailWord_5131967 prefixEnd_5131967 2635165774012427889211019 := by
  unfold tailWord_5131967
  simp only [CollatzResearch.WordTrace]
  refine ⟨187178213798767504029354155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124785475865845002686236103 187178213798767504029354155)
  ·
    refine ⟨280767320698151256044031233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187178213798767504029354155 280767320698151256044031233)
    ·
      refine ⟨210575490523613442033023425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280767320698151256044031233 210575490523613442033023425)
      ·
        refine ⟨157931617892710081524767569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210575490523613442033023425 157931617892710081524767569)
        ·
          refine ⟨118448713419532561143575677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157931617892710081524767569 118448713419532561143575677)
          ·
            refine ⟨44418267532324710428840879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118448713419532561143575677 44418267532324710428840879)
            ·
              refine ⟨66627401298487065643261319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44418267532324710428840879 66627401298487065643261319)
              ·
                refine ⟨99941101947730598464891979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66627401298487065643261319 99941101947730598464891979)
                ·
                  refine ⟨149911652921595897697337969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99941101947730598464891979 149911652921595897697337969)
                  ·
                    refine ⟨112433739691196923273003477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149911652921595897697337969 112433739691196923273003477)
                    ·
                      refine ⟨2635165774012427889211019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112433739691196923273003477 2635165774012427889211019)
                      ·
                        rfl

theorem cell23_5131967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_5131967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131967 prefixEnd_5131967 := by exact prefixLift 5131967
  have htrace : WordTrace (prefixWord ++ tailWord_5131967) baseStart_5131967 baseEnd_5131967 := by
    simpa [prefixWord, tailWord_5131967, baseEnd_5131967] using wordTrace_append hprefix tailTrace_5131967
  have hstable : (prefixWord ++ tailWord_5131967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131967).length < 2 ^ (prefixWord ++ tailWord_5131967).sum := by decide
  have hdescent : baseEnd_5131967 < baseStart_5131967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131968 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 2, 2, 2]
def baseStart_5131968 : Nat := 118140960795 + 5131968 * 2 ^ 59
def prefixEnd_5131968 : Nat := 4983230072969 + 3 ^ 40 * 5131968 * 2
def baseEnd_5131968 : Nat := 2635166287493082385298515

theorem tailTrace_5131968 : CollatzResearch.WordTrace tailWord_5131968 prefixEnd_5131968 2635166287493082385298515 := by
  unfold tailWord_5131968
  simp only [CollatzResearch.WordTrace]
  refine ⟨93589125135881940600070279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124785500181175920800093705 93589125135881940600070279)
  ·
    refine ⟨140383687703822910900105419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93589125135881940600070279 140383687703822910900105419)
    ·
      refine ⟨210575531555734366350158129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140383687703822910900105419 210575531555734366350158129)
      ·
        refine ⟨157931648666800774762618597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210575531555734366350158129 157931648666800774762618597)
        ·
          refine ⟨29612184125025145267990987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157931648666800774762618597 29612184125025145267990987)
          ·
            refine ⟨44418276187537717901986481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29612184125025145267990987 44418276187537717901986481)
            ·
              refine ⟨33313707140653288426489861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44418276187537717901986481 33313707140653288426489861)
              ·
                refine ⟨6246320088872491579966849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33313707140653288426489861 6246320088872491579966849)
                ·
                  refine ⟨4684740066654368684975137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6246320088872491579966849 4684740066654368684975137)
                  ·
                    refine ⟨3513555049990776513731353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4684740066654368684975137 3513555049990776513731353)
                    ·
                      refine ⟨2635166287493082385298515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513555049990776513731353 2635166287493082385298515)
                      ·
                        rfl

theorem cell23_5131968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_5131968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131968 prefixEnd_5131968 := by exact prefixLift 5131968
  have htrace : WordTrace (prefixWord ++ tailWord_5131968) baseStart_5131968 baseEnd_5131968 := by
    simpa [prefixWord, tailWord_5131968, baseEnd_5131968] using wordTrace_append hprefix tailTrace_5131968
  have hstable : (prefixWord ++ tailWord_5131968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131968).length < 2 ^ (prefixWord ++ tailWord_5131968).sum := by decide
  have hdescent : baseEnd_5131968 < baseStart_5131968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131985 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 2, 2, 2]
def baseStart_5131985 : Nat := 118140960795 + 5131985 * 2 ^ 59
def prefixEnd_5131985 : Nat := 4983230072969 + 3 ^ 40 * 5131985 * 2
def baseEnd_5131985 : Nat := 2635175016664208818785937

theorem tailTrace_5131985 : CollatzResearch.WordTrace tailWord_5131985 prefixEnd_5131985 2635175016664208818785937 := by
  unfold tailWord_5131985
  simp only [CollatzResearch.WordTrace]
  refine ⟨187178870312702293103509409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124785913541801528735672939 187178870312702293103509409)
  ·
    refine ⟨140384152734526719827632057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187178870312702293103509409 140384152734526719827632057)
    ·
      refine ⟨105288114550895039870724043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140384152734526719827632057 105288114550895039870724043)
      ·
        refine ⟨157932171826342559806086065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105288114550895039870724043 157932171826342559806086065)
        ·
          refine ⟨118449128869756919854564549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157932171826342559806086065 118449128869756919854564549)
          ·
            refine ⟨22209211663079422472730853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118449128869756919854564549 22209211663079422472730853)
            ·
              refine ⟨4164227186827391713637035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22209211663079422472730853 4164227186827391713637035)
              ·
                refine ⟨6246340780241087570455553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164227186827391713637035 6246340780241087570455553)
                ·
                  refine ⟨4684755585180815677841665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6246340780241087570455553 4684755585180815677841665)
                  ·
                    refine ⟨3513566688885611758381249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4684755585180815677841665 3513566688885611758381249)
                    ·
                      refine ⟨2635175016664208818785937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513566688885611758381249 2635175016664208818785937)
                      ·
                        rfl

theorem cell23_5131985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_5131985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5131985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5131985 prefixEnd_5131985 := by exact prefixLift 5131985
  have htrace : WordTrace (prefixWord ++ tailWord_5131985) baseStart_5131985 baseEnd_5131985 := by
    simpa [prefixWord, tailWord_5131985, baseEnd_5131985] using wordTrace_append hprefix tailTrace_5131985
  have hstable : (prefixWord ++ tailWord_5131985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131985).length < 2 ^ (prefixWord ++ tailWord_5131985).sum := by decide
  have hdescent : baseEnd_5131985 < baseStart_5131985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132014 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_5132014 : Nat := 118140960795 + 5132014 * 2 ^ 59
def prefixEnd_5132014 : Nat := 4983230072969 + 3 ^ 40 * 5132014 * 2
def baseEnd_5132014 : Nat := 2635189907603189205323303

theorem tailTrace_5132014 : CollatzResearch.WordTrace tailWord_5132014 prefixEnd_5132014 2635189907603189205323303 := by
  unfold tailWord_5132014
  simp only [CollatzResearch.WordTrace]
  refine ⟨23397491003699653882039387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124786618686398154037543397 23397491003699653882039387)
  ·
    refine ⟨35096236505549480823059081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23397491003699653882039387 35096236505549480823059081)
    ·
      refine ⟨26322177379162110617294311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35096236505549480823059081 26322177379162110617294311)
      ·
        refine ⟨39483266068743165925941467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26322177379162110617294311 39483266068743165925941467)
        ·
          refine ⟨59224899103114748888912201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39483266068743165925941467 59224899103114748888912201)
          ·
            refine ⟨44418674327336061666684151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59224899103114748888912201 44418674327336061666684151)
            ·
              refine ⟨66628011491004092500026227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44418674327336061666684151 66628011491004092500026227)
              ·
                refine ⟨99942017236506138750039341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66628011491004092500026227 99942017236506138750039341)
                ·
                  refine ⟨37478256463689802031264753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99942017236506138750039341 37478256463689802031264753)
                  ·
                    refine ⟨28108692347767351523448565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37478256463689802031264753 28108692347767351523448565)
                    ·
                      refine ⟨2635189907603189205323303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28108692347767351523448565 2635189907603189205323303)
                      ·
                        rfl

theorem cell23_5132014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_5132014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132014 prefixEnd_5132014 := by exact prefixLift 5132014
  have htrace : WordTrace (prefixWord ++ tailWord_5132014) baseStart_5132014 baseEnd_5132014 := by
    simpa [prefixWord, tailWord_5132014, baseEnd_5132014] using wordTrace_append hprefix tailTrace_5132014
  have hstable : (prefixWord ++ tailWord_5132014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132014).length < 2 ^ (prefixWord ++ tailWord_5132014).sum := by decide
  have hdescent : baseEnd_5132014 < baseStart_5132014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132024 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_5132024 : Nat := 118140960795 + 5132024 * 2 ^ 59
def prefixEnd_5132024 : Nat := 4983230072969 + 3 ^ 40 * 5132024 * 2
def baseEnd_5132024 : Nat := 2635195042409734166198257

theorem tailTrace_5132024 : CollatzResearch.WordTrace tailWord_5132024 prefixEnd_5132024 2635195042409734166198257 := by
  unfold tailWord_5132024
  simp only [CollatzResearch.WordTrace]
  refine ⟨93590146379780501382089563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124786861839707335176119417 93590146379780501382089563)
  ·
    refine ⟨140385219569670752073134345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93590146379780501382089563 140385219569670752073134345)
    ·
      refine ⟨105288914677253064054850759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140385219569670752073134345 105288914677253064054850759)
      ·
        refine ⟨157933372015879596082276139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105288914677253064054850759 157933372015879596082276139)
        ·
          refine ⟨236900058023819394123414209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157933372015879596082276139 236900058023819394123414209)
          ·
            refine ⟨177675043517864545592560657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236900058023819394123414209 177675043517864545592560657)
            ·
              refine ⟨133256282638398409194420493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177675043517864545592560657 133256282638398409194420493)
              ·
                refine ⟨49971105989399403447907685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133256282638398409194420493 49971105989399403447907685)
                ·
                  refine ⟨9369582373012388146482691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49971105989399403447907685 9369582373012388146482691)
                  ·
                    refine ⟨14054373559518582219724037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9369582373012388146482691 14054373559518582219724037)
                    ·
                      refine ⟨2635195042409734166198257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14054373559518582219724037 2635195042409734166198257)
                      ·
                        rfl

theorem cell23_5132024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_5132024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132024 prefixEnd_5132024 := by exact prefixLift 5132024
  have htrace : WordTrace (prefixWord ++ tailWord_5132024) baseStart_5132024 baseEnd_5132024 := by
    simpa [prefixWord, tailWord_5132024, baseEnd_5132024] using wordTrace_append hprefix tailTrace_5132024
  have hstable : (prefixWord ++ tailWord_5132024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132024).length < 2 ^ (prefixWord ++ tailWord_5132024).sum := by decide
  have hdescent : baseEnd_5132024 < baseStart_5132024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132058 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4]
def baseStart_5132058 : Nat := 118140960795 + 5132058 * 2 ^ 59
def prefixEnd_5132058 : Nat := 4983230072969 + 3 ^ 40 * 5132058 * 2
def baseEnd_5132058 : Nat := 2635212500751987033173101

theorem tailTrace_5132058 : CollatzResearch.WordTrace tailWord_5132058 prefixEnd_5132058 2635212500751987033173101 := by
  unfold tailWord_5132058
  simp only [CollatzResearch.WordTrace]
  refine ⟨46795383210359456642729207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124787688560958551047277885 46795383210359456642729207)
  ·
    refine ⟨70193074815539184964093811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46795383210359456642729207 70193074815539184964093811)
    ·
      refine ⟨105289612223308777446140717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70193074815539184964093811 105289612223308777446140717)
      ·
        refine ⟨39483604583740791542302769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105289612223308777446140717 39483604583740791542302769)
        ·
          refine ⟨29612703437805593656727077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39483604583740791542302769 29612703437805593656727077)
          ·
            refine ⟨5552381894588548810636327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29612703437805593656727077 5552381894588548810636327)
            ·
              refine ⟨8328572841882823215954491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552381894588548810636327 8328572841882823215954491)
              ·
                refine ⟨12492859262824234823931737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8328572841882823215954491 12492859262824234823931737)
                ·
                  refine ⟨9369644447118176117948803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12492859262824234823931737 9369644447118176117948803)
                  ·
                    refine ⟨14054466670677264176923205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9369644447118176117948803 14054466670677264176923205)
                    ·
                      refine ⟨2635212500751987033173101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14054466670677264176923205 2635212500751987033173101)
                      ·
                        rfl

theorem cell23_5132058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_5132058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132058 prefixEnd_5132058 := by exact prefixLift 5132058
  have htrace : WordTrace (prefixWord ++ tailWord_5132058) baseStart_5132058 baseEnd_5132058 := by
    simpa [prefixWord, tailWord_5132058, baseEnd_5132058] using wordTrace_append hprefix tailTrace_5132058
  have hstable : (prefixWord ++ tailWord_5132058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132058).length < 2 ^ (prefixWord ++ tailWord_5132058).sum := by decide
  have hdescent : baseEnd_5132058 < baseStart_5132058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132064 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 8]
def baseStart_5132064 : Nat := 118140960795 + 5132064 * 2 ^ 59
def prefixEnd_5132064 : Nat := 4983230072969 + 3 ^ 40 * 5132064 * 2
def baseEnd_5132064 : Nat := 292801731292879334410897

theorem tailTrace_5132064 : CollatzResearch.WordTrace tailWord_5132064 prefixEnd_5132064 292801731292879334410897 := by
  unfold tailWord_5132064
  simp only [CollatzResearch.WordTrace]
  refine ⟨93590875839708044797817623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124787834452944059730423497 93590875839708044797817623)
  ·
    refine ⟨140386313759562067196726435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93590875839708044797817623 140386313759562067196726435)
    ·
      refine ⟨210579470639343100795089653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140386313759562067196726435 210579470639343100795089653)
      ·
        refine ⟨19741825372438415699539655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210579470639343100795089653 19741825372438415699539655)
        ·
          refine ⟨29612738058657623549309483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19741825372438415699539655 29612738058657623549309483)
          ·
            refine ⟨44419107087986435323964225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29612738058657623549309483 44419107087986435323964225)
            ·
              refine ⟨33314330315989826492973169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44419107087986435323964225 33314330315989826492973169)
              ·
                refine ⟨24985747736992369869729877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33314330315989826492973169 24985747736992369869729877)
                ·
                  refine ⟨292801731292879334410897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24985747736992369869729877 292801731292879334410897)
                  ·
                    rfl

theorem cell23_5132064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 8].length) (baseStart_5132064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132064 prefixEnd_5132064 := by exact prefixLift 5132064
  have htrace : WordTrace (prefixWord ++ tailWord_5132064) baseStart_5132064 baseEnd_5132064 := by
    simpa [prefixWord, tailWord_5132064, baseEnd_5132064] using wordTrace_append hprefix tailTrace_5132064
  have hstable : (prefixWord ++ tailWord_5132064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132064).length < 2 ^ (prefixWord ++ tailWord_5132064).sum := by decide
  have hdescent : baseEnd_5132064 < baseStart_5132064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132081 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 6]
def baseStart_5132081 : Nat := 118140960795 + 5132081 * 2 ^ 59
def prefixEnd_5132081 : Nat := 4983230072969 + 3 ^ 40 * 5132081 * 2
def baseEnd_5132081 : Nat := 292802701200782271465055

theorem tailTrace_5132081 : CollatzResearch.WordTrace tailWord_5132081 prefixEnd_5132081 292802701200782271465055 := by
  unfold tailWord_5132081
  simp only [CollatzResearch.WordTrace]
  refine ⟨187182371720354501499004097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124788247813569667666002731 187182371720354501499004097)
  ·
    refine ⟨140386778790265876124253073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187182371720354501499004097 140386778790265876124253073)
    ·
      refine ⟨105290084092699407093189805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140386778790265876124253073 105290084092699407093189805)
      ·
        refine ⟨39483781534762277659946177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105290084092699407093189805 39483781534762277659946177)
        ·
          refine ⟨29612836151071708244959633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39483781534762277659946177 29612836151071708244959633)
          ·
            refine ⟨22209627113303781183719725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29612836151071708244959633 22209627113303781183719725)
            ·
              refine ⟨8328610167488917943894897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22209627113303781183719725 8328610167488917943894897)
              ·
                refine ⟨6246457625616688457921173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8328610167488917943894897 6246457625616688457921173)
                ·
                  refine ⟨292802701200782271465055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6246457625616688457921173 292802701200782271465055)
                  ·
                    rfl

theorem cell23_5132081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 6].length) (baseStart_5132081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132081 prefixEnd_5132081 := by exact prefixLift 5132081
  have htrace : WordTrace (prefixWord ++ tailWord_5132081) baseStart_5132081 baseEnd_5132081 := by
    simpa [prefixWord, tailWord_5132081, baseEnd_5132081] using wordTrace_append hprefix tailTrace_5132081
  have hstable : (prefixWord ++ tailWord_5132081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132081).length < 2 ^ (prefixWord ++ tailWord_5132081).sum := by decide
  have hdescent : baseEnd_5132081 < baseStart_5132081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132101 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 3, 5, 2]
def baseStart_5132101 : Nat := 118140960795 + 5132101 * 2 ^ 59
def prefixEnd_5132101 : Nat := 4983230072969 + 3 ^ 40 * 5132101 * 2
def baseEnd_5132101 : Nat := 2635234580420130364935403

theorem tailTrace_5132101 : CollatzResearch.WordTrace tailWord_5132101 prefixEnd_5132101 2635234580420130364935403 := by
  unfold tailWord_5132101
  simp only [CollatzResearch.WordTrace]
  refine ⟨187183101180282044914732157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124788734120188029943154771 187183101180282044914732157)
  ·
    refine ⟨70193662942605766843024559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187183101180282044914732157 70193662942605766843024559)
    ·
      refine ⟨105290494413908650264536839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70193662942605766843024559 105290494413908650264536839)
      ·
        refine ⟨157935741620862975396805259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105290494413908650264536839 157935741620862975396805259)
        ·
          refine ⟨236903612431294463095207889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157935741620862975396805259 236903612431294463095207889)
          ·
            refine ⟨177677709323470847321405917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236903612431294463095207889 177677709323470847321405917)
            ·
              refine ⟨66629140996301567745527219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177677709323470847321405917 66629140996301567745527219)
              ·
                refine ⟨99943711494452351618290829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66629140996301567745527219 99943711494452351618290829)
                ·
                  refine ⟨37478891810419631856859061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99943711494452351618290829 37478891810419631856859061)
                  ·
                    refine ⟨3513646107226840486580537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37478891810419631856859061 3513646107226840486580537)
                    ·
                      refine ⟨2635234580420130364935403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513646107226840486580537 2635234580420130364935403)
                      ·
                        rfl

theorem cell23_5132101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_5132101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132101 prefixEnd_5132101 := by exact prefixLift 5132101
  have htrace : WordTrace (prefixWord ++ tailWord_5132101) baseStart_5132101 baseEnd_5132101 := by
    simpa [prefixWord, tailWord_5132101, baseEnd_5132101] using wordTrace_append hprefix tailTrace_5132101
  have hstable : (prefixWord ++ tailWord_5132101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132101).length < 2 ^ (prefixWord ++ tailWord_5132101).sum := by decide
  have hdescent : baseEnd_5132101 < baseStart_5132101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132142 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_5132142 : Nat := 118140960795 + 5132142 * 2 ^ 59
def prefixEnd_5132142 : Nat := 4983230072969 + 3 ^ 40 * 5132142 * 2
def baseEnd_5132142 : Nat := 2635255633126964704522715

theorem tailTrace_5132142 : CollatzResearch.WordTrace tailWord_5132142 prefixEnd_5132142 2635255633126964704522715 := by
  unfold tailWord_5132142
  simp only [CollatzResearch.WordTrace]
  refine ⟨23398074571641688614621835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124789731048755672611316453 23398074571641688614621835)
  ·
    refine ⟨35097111857462532921932753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23398074571641688614621835 35097111857462532921932753)
    ·
      refine ⟨26322833893096899691449565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35097111857462532921932753 26322833893096899691449565)
      ·
        refine ⟨9871062709911337384293587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26322833893096899691449565 9871062709911337384293587)
        ·
          refine ⟨14806594064867006076440381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9871062709911337384293587 14806594064867006076440381)
          ·
            refine ⟨5552472774325127278665143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14806594064867006076440381 5552472774325127278665143)
            ·
              refine ⟨8328709161487690917997715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552472774325127278665143 8328709161487690917997715)
              ·
                refine ⟨12493063742231536376996573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8328709161487690917997715 12493063742231536376996573)
                ·
                  refine ⟨4684898903336826141373715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12493063742231536376996573 4684898903336826141373715)
                  ·
                    refine ⟨7027348355005239212060573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4684898903336826141373715 7027348355005239212060573)
                    ·
                      refine ⟨2635255633126964704522715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7027348355005239212060573 2635255633126964704522715)
                      ·
                        rfl

theorem cell23_5132142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_5132142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132142 prefixEnd_5132142 := by exact prefixLift 5132142
  have htrace : WordTrace (prefixWord ++ tailWord_5132142) baseStart_5132142 baseEnd_5132142 := by
    simpa [prefixWord, tailWord_5132142, baseEnd_5132142] using wordTrace_append hprefix tailTrace_5132142
  have hstable : (prefixWord ++ tailWord_5132142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132142).length < 2 ^ (prefixWord ++ tailWord_5132142).sum := by decide
  have hdescent : baseEnd_5132142 < baseStart_5132142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132154 : List Nat := [3, 1, 1, 1, 1, 1, 5, 10]
def baseStart_5132154 : Nat := 118140960795 + 5132154 * 2 ^ 59
def prefixEnd_5132154 : Nat := 4983230072969 + 3 ^ 40 * 5132154 * 2
def baseEnd_5132154 : Nat := 97602288699808098428617

theorem tailTrace_5132154 : CollatzResearch.WordTrace tailWord_5132154 prefixEnd_5132154 97602288699808098428617 := by
  unfold tailWord_5132154
  simp only [CollatzResearch.WordTrace]
  refine ⟨46796258562272508741602879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124790022832726689977607677 46796258562272508741602879)
  ·
    refine ⟨70194387843408763112404319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46796258562272508741602879 70194387843408763112404319)
    ·
      refine ⟨105291581765113144668606479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70194387843408763112404319 105291581765113144668606479)
      ·
        refine ⟨157937372647669717002909719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105291581765113144668606479 157937372647669717002909719)
        ·
          refine ⟨236906058971504575504364579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157937372647669717002909719 236906058971504575504364579)
          ·
            refine ⟨355359088457256863256546869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236906058971504575504364579 355359088457256863256546869)
            ·
              refine ⟨33314914542867830930301269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 355359088457256863256546869 33314914542867830930301269)
              ·
                refine ⟨97602288699808098428617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33314914542867830930301269 97602288699808098428617)
                ·
                  rfl

theorem cell23_5132154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 10].length) (baseStart_5132154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132154 prefixEnd_5132154 := by exact prefixLift 5132154
  have htrace : WordTrace (prefixWord ++ tailWord_5132154) baseStart_5132154 baseEnd_5132154 := by
    simpa [prefixWord, tailWord_5132154, baseEnd_5132154] using wordTrace_append hprefix tailTrace_5132154
  have hstable : (prefixWord ++ tailWord_5132154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132154).length < 2 ^ (prefixWord ++ tailWord_5132154).sum := by decide
  have hdescent : baseEnd_5132154 < baseStart_5132154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132178 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5132178 : Nat := 118140960795 + 5132178 * 2 ^ 59
def prefixEnd_5132178 : Nat := 4983230072969 + 3 ^ 40 * 5132178 * 2
def baseEnd_5132178 : Nat := 2635274118430526563672549

theorem tailTrace_5132178 : CollatzResearch.WordTrace tailWord_5132178 prefixEnd_5132178 2635274118430526563672549 := by
  unfold tailWord_5132178
  simp only [CollatzResearch.WordTrace]
  refine ⟨46796477400250771766321297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124790606400668724710190125 46796477400250771766321297)
  ·
    refine ⟨35097358050188078824740973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46796477400250771766321297 35097358050188078824740973)
    ·
      refine ⟨13161509268820529559277865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35097358050188078824740973 13161509268820529559277865)
      ·
        refine ⟨9871131951615397169458399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13161509268820529559277865 9871131951615397169458399)
        ·
          refine ⟨14806697927423095754187599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9871131951615397169458399 14806697927423095754187599)
          ·
            refine ⟨22210046891134643631281399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14806697927423095754187599 22210046891134643631281399)
            ·
              refine ⟨33315070336701965446922099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22210046891134643631281399 33315070336701965446922099)
              ·
                refine ⟨49972605505052948170383149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33315070336701965446922099 49972605505052948170383149)
                ·
                  refine ⟨18739727064394855563893681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49972605505052948170383149 18739727064394855563893681)
                  ·
                    refine ⟨14054795298296141672920261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18739727064394855563893681 14054795298296141672920261)
                    ·
                      refine ⟨2635274118430526563672549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14054795298296141672920261 2635274118430526563672549)
                      ·
                        rfl

theorem cell23_5132178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5132178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132178 prefixEnd_5132178 := by exact prefixLift 5132178
  have htrace : WordTrace (prefixWord ++ tailWord_5132178) baseStart_5132178 baseEnd_5132178 := by
    simpa [prefixWord, tailWord_5132178, baseEnd_5132178] using wordTrace_append hprefix tailTrace_5132178
  have hstable : (prefixWord ++ tailWord_5132178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132178).length < 2 ^ (prefixWord ++ tailWord_5132178).sum := by decide
  have hdescent : baseEnd_5132178 < baseStart_5132178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132199 : List Nat := [1, 1, 6, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_5132199 : Nat := 118140960795 + 5132199 * 2 ^ 59
def prefixEnd_5132199 : Nat := 4983230072969 + 3 ^ 40 * 5132199 * 2
def baseEnd_5132199 : Nat := 2635284901524270981509953

theorem tailTrace_5132199 : CollatzResearch.WordTrace tailWord_5132199 prefixEnd_5132199 2635284901524270981509953 := by
  unfold tailWord_5132199
  simp only [CollatzResearch.WordTrace]
  refine ⟨187186675533927007651799651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124791117022618005101199767 187186675533927007651799651)
  ·
    refine ⟨280780013300890511477699477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187186675533927007651799651 280780013300890511477699477)
    ·
      refine ⟨13161563123479242725517163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 280780013300890511477699477 13161563123479242725517163)
      ·
        refine ⟨19742344685218864088275745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13161563123479242725517163 19742344685218864088275745)
        ·
          refine ⟨14806758513914148066206809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19742344685218864088275745 14806758513914148066206809)
          ·
            refine ⟨11105068885435611049655107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14806758513914148066206809 11105068885435611049655107)
            ·
              refine ⟨16657603328153416574482661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11105068885435611049655107 16657603328153416574482661)
              ·
                refine ⟨3123300624028765607715499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16657603328153416574482661 3123300624028765607715499)
                ·
                  refine ⟨4684950936043148411573249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123300624028765607715499 4684950936043148411573249)
                  ·
                    refine ⟨3513713202032361308679937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4684950936043148411573249 3513713202032361308679937)
                    ·
                      refine ⟨2635284901524270981509953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513713202032361308679937 2635284901524270981509953)
                      ·
                        rfl

theorem cell23_5132199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_5132199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132199 prefixEnd_5132199 := by exact prefixLift 5132199
  have htrace : WordTrace (prefixWord ++ tailWord_5132199) baseStart_5132199 baseEnd_5132199 := by
    simpa [prefixWord, tailWord_5132199, baseEnd_5132199] using wordTrace_append hprefix tailTrace_5132199
  have hstable : (prefixWord ++ tailWord_5132199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132199).length < 2 ^ (prefixWord ++ tailWord_5132199).sum := by decide
  have hdescent : baseEnd_5132199 < baseStart_5132199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132212 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_5132212 : Nat := 118140960795 + 5132212 * 2 ^ 59
def prefixEnd_5132212 : Nat := 4983230072969 + 3 ^ 40 * 5132212 * 2
def baseEnd_5132212 : Nat := 2635291576772779430647393

theorem tailTrace_5132212 : CollatzResearch.WordTrace tailWord_5132212 prefixEnd_5132212 2635291576772779430647393 := by
  unfold tailWord_5132212
  simp only [CollatzResearch.WordTrace]
  refine ⟨93593574841439955436011445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124791433121919940581348593 93593574841439955436011445)
  ·
    refine ⟨8774397641384995822126073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93593574841439955436011445 8774397641384995822126073)
    ·
      refine ⟨6580798231038746866594555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8774397641384995822126073 6580798231038746866594555)
      ·
        refine ⟨9871197346558120299891833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6580798231038746866594555 9871197346558120299891833)
        ·
          refine ⟨7403398009918590224918875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9871197346558120299891833 7403398009918590224918875)
          ·
            refine ⟨11105097014877885337378313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7403398009918590224918875 11105097014877885337378313)
            ·
              refine ⟨8328822761158414003033735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11105097014877885337378313 8328822761158414003033735)
              ·
                refine ⟨12493234141737621004550603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8328822761158414003033735 12493234141737621004550603)
                ·
                  refine ⟨18739851212606431506825905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12493234141737621004550603 18739851212606431506825905)
                  ·
                    refine ⟨14054888409454823630119429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18739851212606431506825905 14054888409454823630119429)
                    ·
                      refine ⟨2635291576772779430647393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14054888409454823630119429 2635291576772779430647393)
                      ·
                        rfl

theorem cell23_5132212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_5132212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132212 prefixEnd_5132212 := by exact prefixLift 5132212
  have htrace : WordTrace (prefixWord ++ tailWord_5132212) baseStart_5132212 baseEnd_5132212 := by
    simpa [prefixWord, tailWord_5132212, baseEnd_5132212] using wordTrace_append hprefix tailTrace_5132212
  have hstable : (prefixWord ++ tailWord_5132212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132212).length < 2 ^ (prefixWord ++ tailWord_5132212).sum := by decide
  have hdescent : baseEnd_5132212 < baseStart_5132212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132241 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_5132241 : Nat := 118140960795 + 5132241 * 2 ^ 59
def prefixEnd_5132241 : Nat := 4983230072969 + 3 ^ 40 * 5132241 * 2
def baseEnd_5132241 : Nat := 2635306467711759817184759

theorem tailTrace_5132241 : CollatzResearch.WordTrace tailWord_5132241 prefixEnd_5132241 2635306467711759817184759 := by
  unfold tailWord_5132241
  simp only [CollatzResearch.WordTrace]
  refine ⟨187188207399774848824828577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124792138266516565883219051 187188207399774848824828577)
  ·
    refine ⟨140391155549831136618621433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187188207399774848824828577 140391155549831136618621433)
    ·
      refine ⟨105293366662373352463966075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140391155549831136618621433 105293366662373352463966075)
      ·
        refine ⟨157940049993560028695949113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105293366662373352463966075 157940049993560028695949113)
        ·
          refine ⟨118455037495170021521961835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157940049993560028695949113 118455037495170021521961835)
          ·
            refine ⟨177682556242755032282942753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118455037495170021521961835 177682556242755032282942753)
            ·
              refine ⟨133261917182066274212207065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177682556242755032282942753 133261917182066274212207065)
              ·
                refine ⟨99946437886549705659155299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133261917182066274212207065 99946437886549705659155299)
                ·
                  refine ⟨149919656829824558488732949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99946437886549705659155299 149919656829824558488732949)
                  ·
                    refine ⟨7027483913898026179159357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 149919656829824558488732949 7027483913898026179159357)
                    ·
                      refine ⟨2635306467711759817184759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7027483913898026179159357 2635306467711759817184759)
                      ·
                        rfl

theorem cell23_5132241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_5132241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132241 prefixEnd_5132241 := by exact prefixLift 5132241
  have htrace : WordTrace (prefixWord ++ tailWord_5132241) baseStart_5132241 baseEnd_5132241 := by
    simpa [prefixWord, tailWord_5132241, baseEnd_5132241] using wordTrace_append hprefix tailTrace_5132241
  have hstable : (prefixWord ++ tailWord_5132241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132241).length < 2 ^ (prefixWord ++ tailWord_5132241).sum := by decide
  have hdescent : baseEnd_5132241 < baseStart_5132241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132249 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 2, 1, 3]
def baseStart_5132249 : Nat := 118140960795 + 5132249 * 2 ^ 59
def prefixEnd_5132249 : Nat := 4983230072969 + 3 ^ 40 * 5132249 * 2
def baseEnd_5132249 : Nat := 2635310575556995785884723

theorem tailTrace_5132249 : CollatzResearch.WordTrace tailWord_5132249 prefixEnd_5132249 2635310575556995785884723 := by
  unfold tailWord_5132249
  simp only [CollatzResearch.WordTrace]
  refine ⟨187188499183745866191119801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124792332789163910794079867 187188499183745866191119801)
  ·
    refine ⟨140391374387809399643339851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187188499183745866191119801 140391374387809399643339851)
    ·
      refine ⟨210587061581714099465009777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140391374387809399643339851 210587061581714099465009777)
      ·
        refine ⟨157940296186285574598757333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210587061581714099465009777 157940296186285574598757333)
        ·
          refine ⟨3701725691866068154658375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 157940296186285574598757333 3701725691866068154658375)
          ·
            refine ⟨5552588537799102231987563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701725691866068154658375 5552588537799102231987563)
            ·
              refine ⟨8328882806698653347981345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552588537799102231987563 8328882806698653347981345)
              ·
                refine ⟨6246662105023990010986009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8328882806698653347981345 6246662105023990010986009)
                ·
                  refine ⟨4684996578767992508239507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6246662105023990010986009 4684996578767992508239507)
                  ·
                    refine ⟨7027494868151988762359261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4684996578767992508239507 7027494868151988762359261)
                    ·
                      refine ⟨2635310575556995785884723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7027494868151988762359261 2635310575556995785884723)
                      ·
                        rfl

theorem cell23_5132249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_5132249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132249 prefixEnd_5132249 := by exact prefixLift 5132249
  have htrace : WordTrace (prefixWord ++ tailWord_5132249) baseStart_5132249 baseEnd_5132249 := by
    simpa [prefixWord, tailWord_5132249, baseEnd_5132249] using wordTrace_append hprefix tailTrace_5132249
  have hstable : (prefixWord ++ tailWord_5132249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132249).length < 2 ^ (prefixWord ++ tailWord_5132249).sum := by decide
  have hdescent : baseEnd_5132249 < baseStart_5132249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132291 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 6, 5]
def baseStart_5132291 : Nat := 118140960795 + 5132291 * 2 ^ 59
def prefixEnd_5132291 : Nat := 4983230072969 + 3 ^ 40 * 5132291 * 2
def baseEnd_5132291 : Nat := 878444047248161540519843

theorem tailTrace_5132291 : CollatzResearch.WordTrace tailWord_5132291 prefixEnd_5132291 878444047248161540519843 := by
  unfold tailWord_5132291
  simp only [CollatzResearch.WordTrace]
  refine ⟨187190031049593707364148727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124793354033062471576099151 187190031049593707364148727)
  ·
    refine ⟨280785046574390561046223091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187190031049593707364148727 280785046574390561046223091)
    ·
      refine ⟨421177569861585841569334637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280785046574390561046223091 421177569861585841569334637)
      ·
        refine ⟨157941588698094690588500489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421177569861585841569334637 157941588698094690588500489)
        ·
          refine ⟨118456191523571017941375367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157941588698094690588500489 118456191523571017941375367)
          ·
            refine ⟨177684287285356526912063051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118456191523571017941375367 177684287285356526912063051)
            ·
              refine ⟨266526430928034790368094577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177684287285356526912063051 266526430928034790368094577)
              ·
                refine ⟨199894823196026092776070933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266526430928034790368094577 199894823196026092776070933)
                ·
                  refine ⟨9370069837313723098878325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 199894823196026092776070933 9370069837313723098878325)
                  ·
                    refine ⟨878444047248161540519843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9370069837313723098878325 878444047248161540519843)
                    ·
                      rfl

theorem cell23_5132291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 5].length) (baseStart_5132291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132291 prefixEnd_5132291 := by exact prefixLift 5132291
  have htrace : WordTrace (prefixWord ++ tailWord_5132291) baseStart_5132291 baseEnd_5132291 := by
    simpa [prefixWord, tailWord_5132291, baseEnd_5132291] using wordTrace_append hprefix tailTrace_5132291
  have hstable : (prefixWord ++ tailWord_5132291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132291).length < 2 ^ (prefixWord ++ tailWord_5132291).sum := by decide
  have hdescent : baseEnd_5132291 < baseStart_5132291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132295 : List Nat := [1, 1, 4, 3, 1, 2, 3, 3, 5]
def baseStart_5132295 : Nat := 118140960795 + 5132295 * 2 ^ 59
def prefixEnd_5132295 : Nat := 4983230072969 + 3 ^ 40 * 5132295 * 2
def baseEnd_5132295 : Nat := 292814910629678067323279

theorem tailTrace_5132295 : CollatzResearch.WordTrace tailWord_5132295 prefixEnd_5132295 292814910629678067323279 := by
  unfold tailWord_5132295
  simp only [CollatzResearch.WordTrace]
  refine ⟨187190176941579216047294339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124793451294386144031529559 187190176941579216047294339)
  ·
    refine ⟨280785265412368824070941509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187190176941579216047294339 280785265412368824070941509)
    ·
      refine ⟨52647237264819154513301533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280785265412368824070941509 52647237264819154513301533)
      ·
        refine ⟨19742713974307182942488075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52647237264819154513301533 19742713974307182942488075)
        ·
          refine ⟨29614070961460774413732113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19742713974307182942488075 29614070961460774413732113)
          ·
            refine ⟨22210553221095580810299085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29614070961460774413732113 22210553221095580810299085)
            ·
              refine ⟨8328957457910842803862157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22210553221095580810299085 8328957457910842803862157)
              ·
                refine ⟨3123359046716566051448309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8328957457910842803862157 3123359046716566051448309)
                ·
                  refine ⟨292814910629678067323279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3123359046716566051448309 292814910629678067323279)
                  ·
                    rfl

theorem cell23_5132295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 5].length) (baseStart_5132295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132295 prefixEnd_5132295 := by exact prefixLift 5132295
  have htrace : WordTrace (prefixWord ++ tailWord_5132295) baseStart_5132295 baseEnd_5132295 := by
    simpa [prefixWord, tailWord_5132295, baseEnd_5132295] using wordTrace_append hprefix tailTrace_5132295
  have hstable : (prefixWord ++ tailWord_5132295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132295).length < 2 ^ (prefixWord ++ tailWord_5132295).sum := by decide
  have hdescent : baseEnd_5132295 < baseStart_5132295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132351 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 10]
def baseStart_5132351 : Nat := 118140960795 + 5132351 * 2 ^ 59
def prefixEnd_5132351 : Nat := 4983230072969 + 3 ^ 40 * 5132351 * 2
def baseEnd_5132351 : Nat := 292818105620417154089917

theorem tailTrace_5132351 : CollatzResearch.WordTrace tailWord_5132351 prefixEnd_5132351 292818105620417154089917 := by
  unfold tailWord_5132351
  simp only [CollatzResearch.WordTrace]
  refine ⟨187192219429376337611332907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124794812952917558407555271 187192219429376337611332907)
  ·
    refine ⟨280788329144064506416999361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187192219429376337611332907 280788329144064506416999361)
    ·
      refine ⟨210591246858048379812749521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280788329144064506416999361 210591246858048379812749521)
      ·
        refine ⟨157943435143536284859562141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210591246858048379812749521 157943435143536284859562141)
        ·
          refine ⟨59228788178826106822335803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157943435143536284859562141 59228788178826106822335803)
          ·
            refine ⟨88843182268239160233503705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59228788178826106822335803 88843182268239160233503705)
            ·
              refine ⟨66632386701179370175127779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88843182268239160233503705 66632386701179370175127779)
              ·
                refine ⟨99948580051769055262691669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66632386701179370175127779 99948580051769055262691669)
                ·
                  refine ⟨292818105620417154089917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 99948580051769055262691669 292818105620417154089917)
                  ·
                    rfl

theorem cell23_5132351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 10].length) (baseStart_5132351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132351 prefixEnd_5132351 := by exact prefixLift 5132351
  have htrace : WordTrace (prefixWord ++ tailWord_5132351) baseStart_5132351 baseEnd_5132351 := by
    simpa [prefixWord, tailWord_5132351, baseEnd_5132351] using wordTrace_append hprefix tailTrace_5132351
  have hstable : (prefixWord ++ tailWord_5132351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132351).length < 2 ^ (prefixWord ++ tailWord_5132351).sum := by decide
  have hdescent : baseEnd_5132351 < baseStart_5132351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132445 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_5132445 : Nat := 118140960795 + 5132445 * 2 ^ 59
def prefixEnd_5132445 : Nat := 4983230072969 + 3 ^ 40 * 5132445 * 2
def baseEnd_5132445 : Nat := 878470405921759006344607

theorem tailTrace_5132445 : CollatzResearch.WordTrace tailWord_5132445 prefixEnd_5132445 878470405921759006344607 := by
  unfold tailWord_5132445
  simp only [CollatzResearch.WordTrace]
  refine ⟨187195647891035791665254789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124797098594023861110169859 187195647891035791665254789)
  ·
    refine ⟨35099183979569210937235273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187195647891035791665254789 35099183979569210937235273)
    ·
      refine ⟨26324387984676908202926455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35099183979569210937235273 26324387984676908202926455)
      ·
        refine ⟨39486581977015362304389683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26324387984676908202926455 39486581977015362304389683)
        ·
          refine ⟨59229872965523043456584525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39486581977015362304389683 59229872965523043456584525)
          ·
            refine ⟨22211202362071141296219197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59229872965523043456584525 22211202362071141296219197)
            ·
              refine ⟨8329200885776677986082199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22211202362071141296219197 8329200885776677986082199)
              ·
                refine ⟨12493801328665016979123299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8329200885776677986082199 12493801328665016979123299)
                ·
                  refine ⟨18740701992997525468684949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12493801328665016979123299 18740701992997525468684949)
                  ·
                    refine ⟨878470405921759006344607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18740701992997525468684949 878470405921759006344607)
                    ·
                      rfl

theorem cell23_5132445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_5132445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132445 prefixEnd_5132445 := by exact prefixLift 5132445
  have htrace : WordTrace (prefixWord ++ tailWord_5132445) baseStart_5132445 baseEnd_5132445 := by
    simpa [prefixWord, tailWord_5132445, baseEnd_5132445] using wordTrace_append hprefix tailTrace_5132445
  have hstable : (prefixWord ++ tailWord_5132445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132445).length < 2 ^ (prefixWord ++ tailWord_5132445).sum := by decide
  have hdescent : baseEnd_5132445 < baseStart_5132445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132488 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 2, 7]
def baseStart_5132488 : Nat := 118140960795 + 5132488 * 2 ^ 59
def prefixEnd_5132488 : Nat := 4983230072969 + 3 ^ 40 * 5132488 * 2
def baseEnd_5132488 : Nat := 878477765811140116932041

theorem tailTrace_5132488 : CollatzResearch.WordTrace tailWord_5132488 prefixEnd_5132488 878477765811140116932041 := by
  unfold tailWord_5132488
  simp only [CollatzResearch.WordTrace]
  refine ⟨93598608114940005004535059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124798144153253340006046745 93598608114940005004535059)
  ·
    refine ⟨140397912172410007506802589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93598608114940005004535059 140397912172410007506802589)
    ·
      refine ⟨52649217064653752815050971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140397912172410007506802589 52649217064653752815050971)
      ·
        refine ⟨78973825596980629222576457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52649217064653752815050971 78973825596980629222576457)
        ·
          refine ⟨59230369197735471916932343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78973825596980629222576457 59230369197735471916932343)
          ·
            refine ⟨88845553796603207875398515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59230369197735471916932343 88845553796603207875398515)
            ·
              refine ⟨133268330694904811813097773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88845553796603207875398515 133268330694904811813097773)
              ·
                refine ⟨49975624010589304429911665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133268330694904811813097773 49975624010589304429911665)
                ·
                  refine ⟨37481718007941978322433749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49975624010589304429911665 37481718007941978322433749)
                  ·
                    refine ⟨878477765811140116932041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37481718007941978322433749 878477765811140116932041)
                    ·
                      rfl

theorem cell23_5132488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_5132488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132488 prefixEnd_5132488 := by exact prefixLift 5132488
  have htrace : WordTrace (prefixWord ++ tailWord_5132488) baseStart_5132488 baseEnd_5132488 := by
    simpa [prefixWord, tailWord_5132488, baseEnd_5132488] using wordTrace_append hprefix tailTrace_5132488
  have hstable : (prefixWord ++ tailWord_5132488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132488).length < 2 ^ (prefixWord ++ tailWord_5132488).sum := by decide
  have hdescent : baseEnd_5132488 < baseStart_5132488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132492 : List Nat := [2, 2, 1, 6, 1, 1, 2, 8]
def baseStart_5132492 : Nat := 118140960795 + 5132492 * 2 ^ 59
def prefixEnd_5132492 : Nat := 4983230072969 + 3 ^ 40 * 5132492 * 2
def baseEnd_5132492 : Nat := 97608716716890308709115

theorem tailTrace_5132492 : CollatzResearch.WordTrace tailWord_5132492 prefixEnd_5132492 97608716716890308709115 := by
  unfold tailWord_5132492
  simp only [CollatzResearch.WordTrace]
  refine ⟨93598681060932759346107865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124798241414577012461477153 93598681060932759346107865)
  ·
    refine ⟨70199010795699569509580899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93598681060932759346107865 70199010795699569509580899)
    ·
      refine ⟨105298516193549354264371349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70199010795699569509580899 105298516193549354264371349)
      ·
        refine ⟨4935867946572625981142407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105298516193549354264371349 4935867946572625981142407)
        ·
          refine ⟨7403801919858938971713611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4935867946572625981142407 7403801919858938971713611)
          ·
            refine ⟨11105702879788408457570417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7403801919858938971713611 11105702879788408457570417)
            ·
              refine ⟨8329277159841306343177813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11105702879788408457570417 8329277159841306343177813)
              ·
                refine ⟨97608716716890308709115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8329277159841306343177813 97608716716890308709115)
                ·
                  rfl

theorem cell23_5132492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 8].length) (baseStart_5132492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132492 prefixEnd_5132492 := by exact prefixLift 5132492
  have htrace : WordTrace (prefixWord ++ tailWord_5132492) baseStart_5132492 baseEnd_5132492 := by
    simpa [prefixWord, tailWord_5132492, baseEnd_5132492] using wordTrace_append hprefix tailTrace_5132492
  have hstable : (prefixWord ++ tailWord_5132492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132492).length < 2 ^ (prefixWord ++ tailWord_5132492).sum := by decide
  have hdescent : baseEnd_5132492 < baseStart_5132492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132512 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 3, 3, 2]
def baseStart_5132512 : Nat := 118140960795 + 5132512 * 2 ^ 59
def prefixEnd_5132512 : Nat := 4983230072969 + 3 ^ 40 * 5132512 * 2
def baseEnd_5132512 : Nat := 2635445620969128256896013

theorem tailTrace_5132512 : CollatzResearch.WordTrace tailWord_5132512 prefixEnd_5132512 2635445620969128256896013 := by
  unfold tailWord_5132512
  simp only [CollatzResearch.WordTrace]
  refine ⟨93599045790896531053971895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124798727721195374738629193 93599045790896531053971895)
  ·
    refine ⟨140398568686344796580957843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93599045790896531053971895 140398568686344796580957843)
    ·
      refine ⟨210597853029517194871436765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140398568686344796580957843 210597853029517194871436765)
      ·
        refine ⟨78974194886068948076788787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210597853029517194871436765 78974194886068948076788787)
        ·
          refine ⟨118461292329103422115183181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78974194886068948076788787 118461292329103422115183181)
          ·
            refine ⟨44422984623413783293193693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118461292329103422115183181 44422984623413783293193693)
            ·
              refine ⟨16658619233780168734947635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44422984623413783293193693 16658619233780168734947635)
              ·
                refine ⟨24987928850670253102421453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16658619233780168734947635 24987928850670253102421453)
                ·
                  refine ⟨9370473319001344913408045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24987928850670253102421453 9370473319001344913408045)
                  ·
                    refine ⟨3513927494625504342528017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9370473319001344913408045 3513927494625504342528017)
                    ·
                      refine ⟨2635445620969128256896013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513927494625504342528017 2635445620969128256896013)
                      ·
                        rfl

theorem cell23_5132512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_5132512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132512 prefixEnd_5132512 := by exact prefixLift 5132512
  have htrace : WordTrace (prefixWord ++ tailWord_5132512) baseStart_5132512 baseEnd_5132512 := by
    simpa [prefixWord, tailWord_5132512, baseEnd_5132512] using wordTrace_append hprefix tailTrace_5132512
  have hstable : (prefixWord ++ tailWord_5132512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132512).length < 2 ^ (prefixWord ++ tailWord_5132512).sum := by decide
  have hdescent : baseEnd_5132512 < baseStart_5132512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132545 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_5132545 : Nat := 118140960795 + 5132545 * 2 ^ 59
def prefixEnd_5132545 : Nat := 4983230072969 + 3 ^ 40 * 5132545 * 2
def baseEnd_5132545 : Nat := 2635462565830726627783361

theorem tailTrace_5132545 : CollatzResearch.WordTrace tailWord_5132545 prefixEnd_5132545 2635462565830726627783361 := by
  unfold tailWord_5132545
  simp only [CollatzResearch.WordTrace]
  refine ⟨187199295190673508743895089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124799530127115672495930059 187199295190673508743895089)
  ·
    refine ⟨140399471393005131557921317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187199295190673508743895089 140399471393005131557921317)
    ·
      refine ⟨26324900886188462167110247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140399471393005131557921317 26324900886188462167110247)
      ·
        refine ⟨39487351329282693250665371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26324900886188462167110247 39487351329282693250665371)
        ·
          refine ⟨59231026993924039875998057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39487351329282693250665371 59231026993924039875998057)
          ·
            refine ⟨44423270245443029906998543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59231026993924039875998057 44423270245443029906998543)
            ·
              refine ⟨66634905368164544860497815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44423270245443029906998543 66634905368164544860497815)
              ·
                refine ⟨99952358052246817290746723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66634905368164544860497815 99952358052246817290746723)
                ·
                  refine ⟨149928537078370225936120085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99952358052246817290746723 149928537078370225936120085)
                  ·
                    refine ⟨7027900175548604340755629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 149928537078370225936120085 7027900175548604340755629)
                    ·
                      refine ⟨2635462565830726627783361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7027900175548604340755629 2635462565830726627783361)
                      ·
                        rfl

theorem cell23_5132545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_5132545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132545 prefixEnd_5132545 := by exact prefixLift 5132545
  have htrace : WordTrace (prefixWord ++ tailWord_5132545) baseStart_5132545 baseEnd_5132545 := by
    simpa [prefixWord, tailWord_5132545, baseEnd_5132545] using wordTrace_append hprefix tailTrace_5132545
  have hstable : (prefixWord ++ tailWord_5132545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132545).length < 2 ^ (prefixWord ++ tailWord_5132545).sum := by decide
  have hdescent : baseEnd_5132545 < baseStart_5132545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132555 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 4]
def baseStart_5132555 : Nat := 118140960795 + 5132555 * 2 ^ 59
def prefixEnd_5132555 : Nat := 4983230072969 + 3 ^ 40 * 5132555 * 2
def baseEnd_5132555 : Nat := 2635467700637271588658315

theorem tailTrace_5132555 : CollatzResearch.WordTrace tailWord_5132555 prefixEnd_5132555 2635467700637271588658315 := by
  unfold tailWord_5132555
  simp only [CollatzResearch.WordTrace]
  refine ⟨187199659920637280451759119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124799773280424853634506079 187199659920637280451759119)
  ·
    refine ⟨280799489880955920677638679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187199659920637280451759119 280799489880955920677638679)
    ·
      refine ⟨421199234821433881016458019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280799489880955920677638679 421199234821433881016458019)
      ·
        refine ⟨631798852232150821524687029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421199234821433881016458019 631798852232150821524687029)
        ·
          refine ⟨59231142396764139517939409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 631798852232150821524687029 59231142396764139517939409)
          ·
            refine ⟨44423356797573104638454557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59231142396764139517939409 44423356797573104638454557)
            ·
              refine ⟨16658758799089914239420459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44423356797573104638454557 16658758799089914239420459)
              ·
                refine ⟨24988138198634871359130689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16658758799089914239420459 24988138198634871359130689)
                ·
                  refine ⟨18741103648976153519348017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24988138198634871359130689 18741103648976153519348017)
                  ·
                    refine ⟨14055827736732115139511013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18741103648976153519348017 14055827736732115139511013)
                    ·
                      refine ⟨2635467700637271588658315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14055827736732115139511013 2635467700637271588658315)
                      ·
                        rfl

theorem cell23_5132555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 4].length) (baseStart_5132555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132555 prefixEnd_5132555 := by exact prefixLift 5132555
  have htrace : WordTrace (prefixWord ++ tailWord_5132555) baseStart_5132555 baseEnd_5132555 := by
    simpa [prefixWord, tailWord_5132555, baseEnd_5132555] using wordTrace_append hprefix tailTrace_5132555
  have hstable : (prefixWord ++ tailWord_5132555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132555).length < 2 ^ (prefixWord ++ tailWord_5132555).sum := by decide
  have hdescent : baseEnd_5132555 < baseStart_5132555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132593 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 2, 2, 2]
def baseStart_5132593 : Nat := 118140960795 + 5132593 * 2 ^ 59
def prefixEnd_5132593 : Nat := 4983230072969 + 3 ^ 40 * 5132593 * 2
def baseEnd_5132593 : Nat := 2635487212902142439983141

theorem tailTrace_5132593 : CollatzResearch.WordTrace tailWord_5132593 prefixEnd_5132593 2635487212902142439983141 := by
  unfold tailWord_5132593
  simp only [CollatzResearch.WordTrace]
  refine ⟨187201045894499612941642433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124800697262999741961094955 187201045894499612941642433)
  ·
    refine ⟨140400784420874709706231825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187201045894499612941642433 140400784420874709706231825)
    ·
      refine ⟨105300588315656032279673869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140400784420874709706231825 105300588315656032279673869)
      ·
        refine ⟨39487720618371012104877701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105300588315656032279673869 39487720618371012104877701)
        ·
          refine ⟨7403947615944564769664569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39487720618371012104877701 7403947615944564769664569)
          ·
            refine ⟨5552960711958423577248427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7403947615944564769664569 5552960711958423577248427)
            ·
              refine ⟨8329441067937635365872641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552960711958423577248427 8329441067937635365872641)
              ·
                refine ⟨6247080800953226524404481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8329441067937635365872641 6247080800953226524404481)
                ·
                  refine ⟨4685310600714919893303361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6247080800953226524404481 4685310600714919893303361)
                  ·
                    refine ⟨3513982950536189919977521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4685310600714919893303361 3513982950536189919977521)
                    ·
                      refine ⟨2635487212902142439983141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3513982950536189919977521 2635487212902142439983141)
                      ·
                        rfl

theorem cell23_5132593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_5132593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132593 prefixEnd_5132593 := by exact prefixLift 5132593
  have htrace : WordTrace (prefixWord ++ tailWord_5132593) baseStart_5132593 baseEnd_5132593 := by
    simpa [prefixWord, tailWord_5132593, baseEnd_5132593] using wordTrace_append hprefix tailTrace_5132593
  have hstable : (prefixWord ++ tailWord_5132593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132593).length < 2 ^ (prefixWord ++ tailWord_5132593).sum := by decide
  have hdescent : baseEnd_5132593 < baseStart_5132593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132595 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 4, 5]
def baseStart_5132595 : Nat := 118140960795 + 5132595 * 2 ^ 59
def prefixEnd_5132595 : Nat := 4983230072969 + 3 ^ 40 * 5132595 * 2
def baseEnd_5132595 : Nat := 878496079954483810719377

theorem tailTrace_5132595 : CollatzResearch.WordTrace tailWord_5132595 prefixEnd_5132595 878496079954483810719377 := by
  unfold tailWord_5132595
  simp only [CollatzResearch.WordTrace]
  refine ⟨187201118840492367283215239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124800745893661578188810159 187201118840492367283215239)
  ·
    refine ⟨280801678260738550924822859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187201118840492367283215239 280801678260738550924822859)
    ·
      refine ⟨421202517391107826387234289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280801678260738550924822859 421202517391107826387234289)
      ·
        refine ⟨315901888043330869790425717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421202517391107826387234289 315901888043330869790425717)
        ·
          refine ⟨29615802004062269042852411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 315901888043330869790425717 29615802004062269042852411)
          ·
            refine ⟨44423703006093403564278617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29615802004062269042852411 44423703006093403564278617)
            ·
              refine ⟨33317777254570052673208963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44423703006093403564278617 33317777254570052673208963)
              ·
                refine ⟨49976665881855079009813445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33317777254570052673208963 49976665881855079009813445)
                ·
                  refine ⟨9370624852847827314340021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49976665881855079009813445 9370624852847827314340021)
                  ·
                    refine ⟨878496079954483810719377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9370624852847827314340021 878496079954483810719377)
                    ·
                      rfl

theorem cell23_5132595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 5].length) (baseStart_5132595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132595 prefixEnd_5132595 := by exact prefixLift 5132595
  have htrace : WordTrace (prefixWord ++ tailWord_5132595) baseStart_5132595 baseEnd_5132595 := by
    simpa [prefixWord, tailWord_5132595, baseEnd_5132595] using wordTrace_append hprefix tailTrace_5132595
  have hstable : (prefixWord ++ tailWord_5132595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132595).length < 2 ^ (prefixWord ++ tailWord_5132595).sum := by decide
  have hdescent : baseEnd_5132595 < baseStart_5132595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132615 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_5132615 : Nat := 118140960795 + 5132615 * 2 ^ 59
def prefixEnd_5132615 : Nat := 4983230072969 + 3 ^ 40 * 5132615 * 2
def baseEnd_5132615 : Nat := 2635498509476541353908039

theorem tailTrace_5132615 : CollatzResearch.WordTrace tailWord_5132615 prefixEnd_5132615 2635498509476541353908039 := by
  unfold tailWord_5132615
  simp only [CollatzResearch.WordTrace]
  refine ⟨187201848300419910698943299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124801232200279940465962199 187201848300419910698943299)
  ·
    refine ⟨280802772450629866048414949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187201848300419910698943299 280802772450629866048414949)
    ·
      refine ⟨52650519834493099884077803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280802772450629866048414949 52650519834493099884077803)
      ·
        refine ⟨78975779751739649826116705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52650519834493099884077803 78975779751739649826116705)
        ·
          refine ⟨59231834813804737369587529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78975779751739649826116705 59231834813804737369587529)
          ·
            refine ⟨44423876110353553027190647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59231834813804737369587529 44423876110353553027190647)
            ·
              refine ⟨66635814165530329540785971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44423876110353553027190647 66635814165530329540785971)
              ·
                refine ⟨99953721248295494311178957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66635814165530329540785971 99953721248295494311178957)
                ·
                  refine ⟨37482645468110810366692109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99953721248295494311178957 37482645468110810366692109)
                  ·
                    refine ⟨14055992050541553887509541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37482645468110810366692109 14055992050541553887509541)
                    ·
                      refine ⟨2635498509476541353908039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14055992050541553887509541 2635498509476541353908039)
                      ·
                        rfl

theorem cell23_5132615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_5132615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132615 prefixEnd_5132615 := by exact prefixLift 5132615
  have htrace : WordTrace (prefixWord ++ tailWord_5132615) baseStart_5132615 baseEnd_5132615 := by
    simpa [prefixWord, tailWord_5132615, baseEnd_5132615] using wordTrace_append hprefix tailTrace_5132615
  have hstable : (prefixWord ++ tailWord_5132615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132615).length < 2 ^ (prefixWord ++ tailWord_5132615).sum := by decide
  have hdescent : baseEnd_5132615 < baseStart_5132615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132632 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 4, 4, 2]
def baseStart_5132632 : Nat := 118140960795 + 5132632 * 2 ^ 59
def prefixEnd_5132632 : Nat := 4983230072969 + 3 ^ 40 * 5132632 * 2
def baseEnd_5132632 : Nat := 2635507238647667787395461

theorem tailTrace_5132632 : CollatzResearch.WordTrace tailWord_5132632 prefixEnd_5132632 2635507238647667787395461 := by
  unfold tailWord_5132632
  simp only [CollatzResearch.WordTrace]
  refine ⟨93601234170679161301156075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124801645560905548401541433 93601234170679161301156075)
  ·
    refine ⟨140401851256018741951734113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93601234170679161301156075 140401851256018741951734113)
    ·
      refine ⟨105301388442014056463800585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140401851256018741951734113 105301388442014056463800585)
      ·
        refine ⟨78976041331510542347850439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105301388442014056463800585 78976041331510542347850439)
        ·
          refine ⟨118464061997265813521775659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78976041331510542347850439 118464061997265813521775659)
          ·
            refine ⟨177696092995898720282663489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118464061997265813521775659 177696092995898720282663489)
            ·
              refine ⟨133272069746924040211997617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177696092995898720282663489 133272069746924040211997617)
              ·
                refine ⟨99954052310193030158998213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133272069746924040211997617 99954052310193030158998213)
                ·
                  refine ⟨18741384808161193154812165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99954052310193030158998213 18741384808161193154812165)
                  ·
                    refine ⟨3514009651530223716527281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18741384808161193154812165 3514009651530223716527281)
                    ·
                      refine ⟨2635507238647667787395461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514009651530223716527281 2635507238647667787395461)
                      ·
                        rfl

theorem cell23_5132632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_5132632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132632 prefixEnd_5132632 := by exact prefixLift 5132632
  have htrace : WordTrace (prefixWord ++ tailWord_5132632) baseStart_5132632 baseEnd_5132632 := by
    simpa [prefixWord, tailWord_5132632, baseEnd_5132632] using wordTrace_append hprefix tailTrace_5132632
  have hstable : (prefixWord ++ tailWord_5132632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132632).length < 2 ^ (prefixWord ++ tailWord_5132632).sum := by decide
  have hdescent : baseEnd_5132632 < baseStart_5132632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132686 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5132686 : Nat := 118140960795 + 5132686 * 2 ^ 59
def prefixEnd_5132686 : Nat := 4983230072969 + 3 ^ 40 * 5132686 * 2
def baseEnd_5132686 : Nat := 2635534966603010576120213

theorem tailTrace_5132686 : CollatzResearch.WordTrace tailWord_5132686 prefixEnd_5132686 2635534966603010576120213 := by
  unfold tailWord_5132686
  simp only [CollatzResearch.WordTrace]
  refine ⟨23400554735395336228097239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124802958588775126549851941 23400554735395336228097239)
  ·
    refine ⟨35100832103093004342145859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23400554735395336228097239 35100832103093004342145859)
    ·
      refine ⟨52651248154639506513218789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35100832103093004342145859 52651248154639506513218789)
      ·
        refine ⟨9872109028994907471228523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52651248154639506513218789 9872109028994907471228523)
        ·
          refine ⟨14808163543492361206842785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9872109028994907471228523 14808163543492361206842785)
          ·
            refine ⟨11106122657619270905132089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14808163543492361206842785 11106122657619270905132089)
            ·
              refine ⟨8329591993214453178849067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11106122657619270905132089 8329591993214453178849067)
              ·
                refine ⟨12494387989821679768273601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8329591993214453178849067 12494387989821679768273601)
                ·
                  refine ⟨9370790992366259826205201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12494387989821679768273601 9370790992366259826205201)
                  ·
                    refine ⟨7028093244274694869653901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9370790992366259826205201 7028093244274694869653901)
                    ·
                      refine ⟨2635534966603010576120213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028093244274694869653901 2635534966603010576120213)
                      ·
                        rfl

theorem cell23_5132686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5132686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132686 prefixEnd_5132686 := by exact prefixLift 5132686
  have htrace : WordTrace (prefixWord ++ tailWord_5132686) baseStart_5132686 baseEnd_5132686 := by
    simpa [prefixWord, tailWord_5132686, baseEnd_5132686] using wordTrace_append hprefix tailTrace_5132686
  have hstable : (prefixWord ++ tailWord_5132686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132686).length < 2 ^ (prefixWord ++ tailWord_5132686).sum := by decide
  have hdescent : baseEnd_5132686 < baseStart_5132686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132709 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 2, 3, 2]
def baseStart_5132709 : Nat := 118140960795 + 5132709 * 2 ^ 59
def prefixEnd_5132709 : Nat := 4983230072969 + 3 ^ 40 * 5132709 * 2
def baseEnd_5132709 : Nat := 2635546776658063986132607

theorem tailTrace_5132709 : CollatzResearch.WordTrace tailWord_5132709 prefixEnd_5132709 2635546776658063986132607 := by
  unfold tailWord_5132709
  simp only [CollatzResearch.WordTrace]
  refine ⟨187205276762079364752865181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124803517841386243168576787 187205276762079364752865181)
  ·
    refine ⟨70201978785779761782324443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187205276762079364752865181 70201978785779761782324443)
    ·
      refine ⟨105302968178669642673486665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70201978785779761782324443 105302968178669642673486665)
      ·
        refine ⟨78977226134002232005114999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105302968178669642673486665 78977226134002232005114999)
        ·
          refine ⟨118465839201003348007672499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78977226134002232005114999 118465839201003348007672499)
          ·
            refine ⟨177698758801505022011508749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118465839201003348007672499 177698758801505022011508749)
            ·
              refine ⟨66637034550564383254315781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177698758801505022011508749 66637034550564383254315781)
              ·
                refine ⟨12494443978230821860184209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66637034550564383254315781 12494443978230821860184209)
                ·
                  refine ⟨9370832983673116395138157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12494443978230821860184209 9370832983673116395138157)
                  ·
                    refine ⟨3514062368877418648176809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9370832983673116395138157 3514062368877418648176809)
                    ·
                      refine ⟨2635546776658063986132607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514062368877418648176809 2635546776658063986132607)
                      ·
                        rfl

theorem cell23_5132709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_5132709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132709 prefixEnd_5132709 := by exact prefixLift 5132709
  have htrace : WordTrace (prefixWord ++ tailWord_5132709) baseStart_5132709 baseEnd_5132709 := by
    simpa [prefixWord, tailWord_5132709, baseEnd_5132709] using wordTrace_append hprefix tailTrace_5132709
  have hstable : (prefixWord ++ tailWord_5132709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132709).length < 2 ^ (prefixWord ++ tailWord_5132709).sum := by decide
  have hdescent : baseEnd_5132709 < baseStart_5132709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132722 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_5132722 : Nat := 118140960795 + 5132722 * 2 ^ 59
def prefixEnd_5132722 : Nat := 4983230072969 + 3 ^ 40 * 5132722 * 2
def baseEnd_5132722 : Nat := 2635553451906572435270047

theorem tailTrace_5132722 : CollatzResearch.WordTrace tailWord_5132722 prefixEnd_5132722 2635553451906572435270047 := by
  unfold tailWord_5132722
  simp only [CollatzResearch.WordTrace]
  refine ⟨46801437727758066993272105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124803833940688178648725613 46801437727758066993272105)
  ·
    refine ⟨35101078295818550244954079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46801437727758066993272105 35101078295818550244954079)
    ·
      refine ⟨52651617443727825367431119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35101078295818550244954079 52651617443727825367431119)
      ·
        refine ⟨78977426165591738051146679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52651617443727825367431119 78977426165591738051146679)
        ·
          refine ⟨118466139248387607076720019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78977426165591738051146679 118466139248387607076720019)
          ·
            refine ⟨177699208872581410615080029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118466139248387607076720019 177699208872581410615080029)
            ·
              refine ⟨66637203327218028980655011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177699208872581410615080029 66637203327218028980655011)
              ·
                refine ⟨99955804990827043470982517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66637203327218028980655011 99955804990827043470982517)
                ·
                  refine ⟨9370856717890035325404611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99955804990827043470982517 9370856717890035325404611)
                  ·
                    refine ⟨14056285076835052988106917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9370856717890035325404611 14056285076835052988106917)
                    ·
                      refine ⟨2635553451906572435270047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14056285076835052988106917 2635553451906572435270047)
                      ·
                        rfl

theorem cell23_5132722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_5132722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132722 prefixEnd_5132722 := by exact prefixLift 5132722
  have htrace : WordTrace (prefixWord ++ tailWord_5132722) baseStart_5132722 baseEnd_5132722 := by
    simpa [prefixWord, tailWord_5132722, baseEnd_5132722] using wordTrace_append hprefix tailTrace_5132722
  have hstable : (prefixWord ++ tailWord_5132722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132722).length < 2 ^ (prefixWord ++ tailWord_5132722).sum := by decide
  have hdescent : baseEnd_5132722 < baseStart_5132722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132737 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5132737 : Nat := 118140960795 + 5132737 * 2 ^ 59
def prefixEnd_5132737 : Nat := 4983230072969 + 3 ^ 40 * 5132737 * 2
def baseEnd_5132737 : Nat := 2635561154116389876582479

theorem tailTrace_5132737 : CollatzResearch.WordTrace tailWord_5132737 prefixEnd_5132737 2635561154116389876582479 := by
  unfold tailWord_5132737
  simp only [CollatzResearch.WordTrace]
  refine ⟨187206298005977925534884465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124804198670651950356589643 187206298005977925534884465)
  ·
    refine ⟨140404723504483444151163349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187206298005977925534884465 140404723504483444151163349)
    ·
      refine ⟨3290735707136330722292891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 140404723504483444151163349 3290735707136330722292891)
      ·
        refine ⟨4936103560704496083439337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3290735707136330722292891 4936103560704496083439337)
        ·
          refine ⟨3702077670528372062579503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4936103560704496083439337 3702077670528372062579503)
          ·
            refine ⟨5553116505792558093869255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702077670528372062579503 5553116505792558093869255)
            ·
              refine ⟨8329674758688837140803883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553116505792558093869255 8329674758688837140803883)
              ·
                refine ⟨12494512138033255711205825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8329674758688837140803883 12494512138033255711205825)
                ·
                  refine ⟨9370884103524941783404369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12494512138033255711205825 9370884103524941783404369)
                  ·
                    refine ⟨7028163077643706337553277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9370884103524941783404369 7028163077643706337553277)
                    ·
                      refine ⟨2635561154116389876582479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028163077643706337553277 2635561154116389876582479)
                      ·
                        rfl

theorem cell23_5132737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5132737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132737 prefixEnd_5132737 := by exact prefixLift 5132737
  have htrace : WordTrace (prefixWord ++ tailWord_5132737) baseStart_5132737 baseEnd_5132737 := by
    simpa [prefixWord, tailWord_5132737, baseEnd_5132737] using wordTrace_append hprefix tailTrace_5132737
  have hstable : (prefixWord ++ tailWord_5132737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132737).length < 2 ^ (prefixWord ++ tailWord_5132737).sum := by decide
  have hdescent : baseEnd_5132737 < baseStart_5132737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132745 : List Nat := [1, 2, 1, 1, 2, 1, 4, 11]
def baseStart_5132745 : Nat := 118140960795 + 5132745 * 2 ^ 59
def prefixEnd_5132745 : Nat := 4983230072969 + 3 ^ 40 * 5132745 * 2
def baseEnd_5132745 : Nat := 97613528220800957232683

theorem tailTrace_5132745 : CollatzResearch.WordTrace tailWord_5132745 prefixEnd_5132745 97613528220800957232683 := by
  unfold tailWord_5132745
  simp only [CollatzResearch.WordTrace]
  refine ⟨187206589789948942901175689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124804393193299295267450459 187206589789948942901175689)
  ·
    refine ⟨140404942342461707175881767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187206589789948942901175689 140404942342461707175881767)
    ·
      refine ⟨210607413513692560763822651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140404942342461707175881767 210607413513692560763822651)
      ·
        refine ⟨315911120270538841145733977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210607413513692560763822651 315911120270538841145733977)
        ·
          refine ⟨236933340202904130859300483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315911120270538841145733977 236933340202904130859300483)
          ·
            refine ⟨355400010304356196288950725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236933340202904130859300483 355400010304356196288950725)
            ·
              refine ⟨66637501932066786804178261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 355400010304356196288950725 66637501932066786804178261)
              ·
                refine ⟨97613528220800957232683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 66637501932066786804178261 97613528220800957232683)
                ·
                  rfl

theorem cell23_5132745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 11].length) (baseStart_5132745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132745 prefixEnd_5132745 := by exact prefixLift 5132745
  have htrace : WordTrace (prefixWord ++ tailWord_5132745) baseStart_5132745 baseEnd_5132745 := by
    simpa [prefixWord, tailWord_5132745, baseEnd_5132745] using wordTrace_append hprefix tailTrace_5132745
  have hstable : (prefixWord ++ tailWord_5132745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132745).length < 2 ^ (prefixWord ++ tailWord_5132745).sum := by decide
  have hdescent : baseEnd_5132745 < baseStart_5132745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132755 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 7]
def baseStart_5132755 : Nat := 118140960795 + 5132755 * 2 ^ 59
def prefixEnd_5132755 : Nat := 4983230072969 + 3 ^ 40 * 5132755 * 2
def baseEnd_5132755 : Nat := 2635570396768170806157395

theorem tailTrace_5132755 : CollatzResearch.WordTrace tailWord_5132755 prefixEnd_5132755 2635570396768170806157395 := by
  unfold tailWord_5132755
  simp only [CollatzResearch.WordTrace]
  refine ⟨187206954519912714609039719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124804636346608476406026479 187206954519912714609039719)
  ·
    refine ⟨280810431779869071913559579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187206954519912714609039719 280810431779869071913559579)
    ·
      refine ⟨421215647669803607870339369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280810431779869071913559579 421215647669803607870339369)
      ·
        refine ⟨315911735752352705902754527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421215647669803607870339369 315911735752352705902754527)
        ·
          refine ⟨473867603628529058854131791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315911735752352705902754527 473867603628529058854131791)
          ·
            refine ⟨710801405442793588281197687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473867603628529058854131791 710801405442793588281197687)
            ·
              refine ⟨1066202108164190382421796531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710801405442793588281197687 1066202108164190382421796531)
              ·
                refine ⟨1599303162246285573632694797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066202108164190382421796531 1599303162246285573632694797)
                ·
                  refine ⟨599738685842357090112260549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1599303162246285573632694797 599738685842357090112260549)
                  ·
                    refine ⟨112451003595441954396048853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 599738685842357090112260549 112451003595441954396048853)
                    ·
                      refine ⟨2635570396768170806157395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112451003595441954396048853 2635570396768170806157395)
                      ·
                        rfl

theorem cell23_5132755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_5132755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132755 prefixEnd_5132755 := by exact prefixLift 5132755
  have htrace : WordTrace (prefixWord ++ tailWord_5132755) baseStart_5132755 baseEnd_5132755 := by
    simpa [prefixWord, tailWord_5132755, baseEnd_5132755] using wordTrace_append hprefix tailTrace_5132755
  have hstable : (prefixWord ++ tailWord_5132755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132755).length < 2 ^ (prefixWord ++ tailWord_5132755).sum := by decide
  have hdescent : baseEnd_5132755 < baseStart_5132755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132756 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_5132756 : Nat := 118140960795 + 5132756 * 2 ^ 59
def prefixEnd_5132756 : Nat := 4983230072969 + 3 ^ 40 * 5132756 * 2
def baseEnd_5132756 : Nat := 2635570910248825302244891

theorem tailTrace_5132756 : CollatzResearch.WordTrace tailWord_5132756 prefixEnd_5132756 2635570910248825302244891 := by
  unfold tailWord_5132756
  simp only [CollatzResearch.WordTrace]
  refine ⟨93603495496454545889913061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124804660661939394519884081 93603495496454545889913061)
  ·
    refine ⟨17550655405585227354358699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93603495496454545889913061 17550655405585227354358699)
    ·
      refine ⟨26325983108377841031538049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17550655405585227354358699 26325983108377841031538049)
      ·
        refine ⟨19744487331283380773653537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26325983108377841031538049 19744487331283380773653537)
        ·
          refine ⟨14808365498462535580240153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19744487331283380773653537 14808365498462535580240153)
          ·
            refine ⟨11106274123846901685180115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14808365498462535580240153 11106274123846901685180115)
            ·
              refine ⟨16659411185770352527770173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11106274123846901685180115 16659411185770352527770173)
              ·
                refine ⟨6247279194663882197913815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16659411185770352527770173 6247279194663882197913815)
                ·
                  refine ⟨9370918791995823296870723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6247279194663882197913815 9370918791995823296870723)
                  ·
                    refine ⟨14056378187993734945306085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9370918791995823296870723 14056378187993734945306085)
                    ·
                      refine ⟨2635570910248825302244891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14056378187993734945306085 2635570910248825302244891)
                      ·
                        rfl

theorem cell23_5132756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_5132756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132756 prefixEnd_5132756 := by exact prefixLift 5132756
  have htrace : WordTrace (prefixWord ++ tailWord_5132756) baseStart_5132756 baseEnd_5132756 := by
    simpa [prefixWord, tailWord_5132756, baseEnd_5132756] using wordTrace_append hprefix tailTrace_5132756
  have hstable : (prefixWord ++ tailWord_5132756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132756).length < 2 ^ (prefixWord ++ tailWord_5132756).sum := by decide
  have hdescent : baseEnd_5132756 < baseStart_5132756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132772 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_5132772 : Nat := 118140960795 + 5132772 * 2 ^ 59
def prefixEnd_5132772 : Nat := 4983230072969 + 3 ^ 40 * 5132772 * 2
def baseEnd_5132772 : Nat := 2635579125939297239644817

theorem tailTrace_5132772 : CollatzResearch.WordTrace tailWord_5132772 prefixEnd_5132772 2635579125939297239644817 := by
  unfold tailWord_5132772
  simp only [CollatzResearch.WordTrace]
  refine ⟨93603787280425563256204285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124805049707234084341605713 93603787280425563256204285)
  ·
    refine ⟨35101420230159586221076607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93603787280425563256204285 35101420230159586221076607)
    ·
      refine ⟨52652130345239379331614911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35101420230159586221076607 52652130345239379331614911)
      ·
        refine ⟨78978195517859068997422367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52652130345239379331614911 78978195517859068997422367)
        ·
          refine ⟨118467293276788603496133551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78978195517859068997422367 118467293276788603496133551)
          ·
            refine ⟨177700939915182905244200327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118467293276788603496133551 177700939915182905244200327)
            ·
              refine ⟨266551409872774357866300491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177700939915182905244200327 266551409872774357866300491)
              ·
                refine ⟨399827114809161536799450737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266551409872774357866300491 399827114809161536799450737)
                ·
                  refine ⟨299870336106871152599588053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399827114809161536799450737 299870336106871152599588053)
                  ·
                    refine ⟨7028211002504792639052845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 299870336106871152599588053 7028211002504792639052845)
                    ·
                      refine ⟨2635579125939297239644817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028211002504792639052845 2635579125939297239644817)
                      ·
                        rfl

theorem cell23_5132772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_5132772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132772 prefixEnd_5132772 := by exact prefixLift 5132772
  have htrace : WordTrace (prefixWord ++ tailWord_5132772) baseStart_5132772 baseEnd_5132772 := by
    simpa [prefixWord, tailWord_5132772, baseEnd_5132772] using wordTrace_append hprefix tailTrace_5132772
  have hstable : (prefixWord ++ tailWord_5132772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132772).length < 2 ^ (prefixWord ++ tailWord_5132772).sum := by decide
  have hdescent : baseEnd_5132772 < baseStart_5132772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132807 : List Nat := [1, 1, 4, 3, 3, 2, 1, 3, 1, 2, 2]
def baseStart_5132807 : Nat := 118140960795 + 5132807 * 2 ^ 59
def prefixEnd_5132807 : Nat := 4983230072969 + 3 ^ 40 * 5132807 * 2
def baseEnd_5132807 : Nat := 2635597097762204602707157

theorem tailTrace_5132807 : CollatzResearch.WordTrace tailWord_5132807 prefixEnd_5132807 2635597097762204602707157 := by
  unfold tailWord_5132807
  simp only [CollatzResearch.WordTrace]
  refine ⟨187208851115724327489932675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124805900743816218326621783 187208851115724327489932675)
  ·
    refine ⟨280813276673586491234899013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187208851115724327489932675 280813276673586491234899013)
    ·
      refine ⟨52652489376297467106543565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280813276673586491234899013 52652489376297467106543565)
      ·
        refine ⟨19744683516111550164953837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52652489376297467106543565 19744683516111550164953837)
        ·
          refine ⟨7404256318541831311857689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19744683516111550164953837 7404256318541831311857689)
          ·
            refine ⟨5553192238906373483893267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7404256318541831311857689 5553192238906373483893267)
            ·
              refine ⟨8329788358359560225839901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553192238906373483893267 8329788358359560225839901)
              ·
                refine ⟨3123670634384835084689963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8329788358359560225839901 3123670634384835084689963)
                ·
                  refine ⟨4685505951577252627034945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123670634384835084689963 4685505951577252627034945)
                  ·
                    refine ⟨3514129463682939470276209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4685505951577252627034945 3514129463682939470276209)
                    ·
                      refine ⟨2635597097762204602707157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514129463682939470276209 2635597097762204602707157)
                      ·
                        rfl

theorem cell23_5132807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_5132807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132807 prefixEnd_5132807 := by exact prefixLift 5132807
  have htrace : WordTrace (prefixWord ++ tailWord_5132807) baseStart_5132807 baseEnd_5132807 := by
    simpa [prefixWord, tailWord_5132807, baseEnd_5132807] using wordTrace_append hprefix tailTrace_5132807
  have hstable : (prefixWord ++ tailWord_5132807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132807).length < 2 ^ (prefixWord ++ tailWord_5132807).sum := by decide
  have hdescent : baseEnd_5132807 < baseStart_5132807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132840 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_5132840 : Nat := 118140960795 + 5132840 * 2 ^ 59
def prefixEnd_5132840 : Nat := 4983230072969 + 3 ^ 40 * 5132840 * 2
def baseEnd_5132840 : Nat := 2635614042623802973594505

theorem tailTrace_5132840 : CollatzResearch.WordTrace tailWord_5132840 prefixEnd_5132840 2635614042623802973594505 := by
  unfold tailWord_5132840
  simp only [CollatzResearch.WordTrace]
  refine ⟨93605027362302387062941987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124806703149736516083922649 93605027362302387062941987)
  ·
    refine ⟨140407541043453580594412981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93605027362302387062941987 140407541043453580594412981)
    ·
      refine ⟨13163206972823773180726217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140407541043453580594412981 13163206972823773180726217)
      ·
        refine ⟨9872405229617829885544663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13163206972823773180726217 9872405229617829885544663)
        ·
          refine ⟨14808607844426744828316995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9872405229617829885544663 14808607844426744828316995)
          ·
            refine ⟨22212911766640117242475493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14808607844426744828316995 22212911766640117242475493)
            ·
              refine ⟨4164920956245021982964155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22212911766640117242475493 4164920956245021982964155)
              ·
                refine ⟨6247381434367532974446233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164920956245021982964155 6247381434367532974446233)
                ·
                  refine ⟨4685536075775649730834675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6247381434367532974446233 4685536075775649730834675)
                  ·
                    refine ⟨7028304113663474596252013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4685536075775649730834675 7028304113663474596252013)
                    ·
                      refine ⟨2635614042623802973594505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028304113663474596252013 2635614042623802973594505)
                      ·
                        rfl

theorem cell23_5132840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_5132840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132840 prefixEnd_5132840 := by exact prefixLift 5132840
  have htrace : WordTrace (prefixWord ++ tailWord_5132840) baseStart_5132840 baseEnd_5132840 := by
    simpa [prefixWord, tailWord_5132840, baseEnd_5132840] using wordTrace_append hprefix tailTrace_5132840
  have hstable : (prefixWord ++ tailWord_5132840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132840).length < 2 ^ (prefixWord ++ tailWord_5132840).sum := by decide
  have hdescent : baseEnd_5132840 < baseStart_5132840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132906 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_5132906 : Nat := 118140960795 + 5132906 * 2 ^ 59
def prefixEnd_5132906 : Nat := 4983230072969 + 3 ^ 40 * 5132906 * 2
def baseEnd_5132906 : Nat := 2635647932346999715369201

theorem tailTrace_5132906 : CollatzResearch.WordTrace tailWord_5132906 prefixEnd_5132906 2635647932346999715369201 := by
  unfold tailWord_5132906
  simp only [CollatzResearch.WordTrace]
  refine ⟨46803115485591416849446643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124808307961577111598524381 46803115485591416849446643)
  ·
    refine ⟨70204673228387125274169965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46803115485591416849446643 70204673228387125274169965)
    ·
      refine ⟨26326752460645171977813737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70204673228387125274169965 26326752460645171977813737)
      ·
        refine ⟨19745064345483878983360303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26326752460645171977813737 19745064345483878983360303)
        ·
          refine ⟨29617596518225818475040455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19745064345483878983360303 29617596518225818475040455)
          ·
            refine ⟨44426394777338727712560683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29617596518225818475040455 44426394777338727712560683)
            ·
              refine ⟨66639592166008091568841025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44426394777338727712560683 66639592166008091568841025)
              ·
                refine ⟨49979694124506068676630769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66639592166008091568841025 49979694124506068676630769)
                ·
                  refine ⟨37484770593379551507473077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49979694124506068676630769 37484770593379551507473077)
                  ·
                    refine ⟨3514197243129332953825601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37484770593379551507473077 3514197243129332953825601)
                    ·
                      refine ⟨2635647932346999715369201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514197243129332953825601 2635647932346999715369201)
                      ·
                        rfl

theorem cell23_5132906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_5132906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132906 prefixEnd_5132906 := by exact prefixLift 5132906
  have htrace : WordTrace (prefixWord ++ tailWord_5132906) baseStart_5132906 baseEnd_5132906 := by
    simpa [prefixWord, tailWord_5132906, baseEnd_5132906] using wordTrace_append hprefix tailTrace_5132906
  have hstable : (prefixWord ++ tailWord_5132906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132906).length < 2 ^ (prefixWord ++ tailWord_5132906).sum := by decide
  have hdescent : baseEnd_5132906 < baseStart_5132906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132956 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_5132956 : Nat := 118140960795 + 5132956 * 2 ^ 59
def prefixEnd_5132956 : Nat := 4983230072969 + 3 ^ 40 * 5132956 * 2
def baseEnd_5132956 : Nat := 2635673606379724519743971

theorem tailTrace_5132956 : CollatzResearch.WordTrace tailWord_5132956 prefixEnd_5132956 2635673606379724519743971 := by
  unfold tailWord_5132956
  simp only [CollatzResearch.WordTrace]
  refine ⟨93607142796092262968553361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124809523728123017291404481 93607142796092262968553361)
  ·
    refine ⟨70205357097069197226415021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93607142796092262968553361 70205357097069197226415021)
    ·
      refine ⟨26327008911400948959905633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70205357097069197226415021 26327008911400948959905633)
      ·
        refine ⟨19745256683550711719929225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26327008911400948959905633 19745256683550711719929225)
        ·
          refine ⟨14808942512663033789946919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19745256683550711719929225 14808942512663033789946919)
          ·
            refine ⟨22213413768994550684920379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14808942512663033789946919 22213413768994550684920379)
            ·
              refine ⟨33320120653491826027380569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22213413768994550684920379 33320120653491826027380569)
              ·
                refine ⟨24990090490118869520535427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33320120653491826027380569 24990090490118869520535427)
                ·
                  refine ⟨37485135735178304280803141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24990090490118869520535427 37485135735178304280803141)
                  ·
                    refine ⟨7028462950345932052650589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37485135735178304280803141 7028462950345932052650589)
                    ·
                      refine ⟨2635673606379724519743971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028462950345932052650589 2635673606379724519743971)
                      ·
                        rfl

theorem cell23_5132956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_5132956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5132956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5132956 prefixEnd_5132956 := by exact prefixLift 5132956
  have htrace : WordTrace (prefixWord ++ tailWord_5132956) baseStart_5132956 baseEnd_5132956 := by
    simpa [prefixWord, tailWord_5132956, baseEnd_5132956] using wordTrace_append hprefix tailTrace_5132956
  have hstable : (prefixWord ++ tailWord_5132956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132956).length < 2 ^ (prefixWord ++ tailWord_5132956).sum := by decide
  have hdescent : baseEnd_5132956 < baseStart_5132956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133010 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 6]
def baseStart_5133010 : Nat := 118140960795 + 5133010 * 2 ^ 59
def prefixEnd_5133010 : Nat := 4983230072969 + 3 ^ 40 * 5133010 * 2
def baseEnd_5133010 : Nat := 292855703815007478718747

theorem tailTrace_5133010 : CollatzResearch.WordTrace tailWord_5133010 prefixEnd_5133010 292855703815007478718747 := by
  unfold tailWord_5133010
  simp only [CollatzResearch.WordTrace]
  refine ⟨46804063783497223289893121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124810836755992595439714989 46804063783497223289893121)
  ·
    refine ⟨35103047837622917467419841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46804063783497223289893121 35103047837622917467419841)
    ·
      refine ⟨26327285878217188100564881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35103047837622917467419841 26327285878217188100564881)
      ·
        refine ⟨19745464408662891075423661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26327285878217188100564881 19745464408662891075423661)
        ·
          refine ⟨7404549153248584153283873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19745464408662891075423661 7404549153248584153283873)
          ·
            refine ⟨5553411864936438114962905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7404549153248584153283873 5553411864936438114962905)
            ·
              refine ⟨4165058898702328586222179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5553411864936438114962905 4165058898702328586222179)
              ·
                refine ⟨6247588348053492879333269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165058898702328586222179 6247588348053492879333269)
                ·
                  refine ⟨292855703815007478718747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6247588348053492879333269 292855703815007478718747)
                  ·
                    rfl

theorem cell23_5133010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_5133010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133010 prefixEnd_5133010 := by exact prefixLift 5133010
  have htrace : WordTrace (prefixWord ++ tailWord_5133010) baseStart_5133010 baseEnd_5133010 := by
    simpa [prefixWord, tailWord_5133010, baseEnd_5133010] using wordTrace_append hprefix tailTrace_5133010
  have hstable : (prefixWord ++ tailWord_5133010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133010).length < 2 ^ (prefixWord ++ tailWord_5133010).sum := by decide
  have hdescent : baseEnd_5133010 < baseStart_5133010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133023 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 1, 5]
def baseStart_5133023 : Nat := 118140960795 + 5133023 * 2 ^ 59
def prefixEnd_5133023 : Nat := 4983230072969 + 3 ^ 40 * 5133023 * 2
def baseEnd_5133023 : Nat := 878569336527858585868721

theorem tailTrace_5133023 : CollatzResearch.WordTrace tailWord_5133023 prefixEnd_5133023 878569336527858585868721 := by
  unfold tailWord_5133023
  simp only [CollatzResearch.WordTrace]
  refine ⟨187216729282941796379795723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124811152855294530919863815 187216729282941796379795723)
  ·
    refine ⟨280825093924412694569693585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187216729282941796379795723 280825093924412694569693585)
    ·
      refine ⟨210618820443309520927270189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280825093924412694569693585 210618820443309520927270189)
      ·
        refine ⟨78982057666241070347726321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210618820443309520927270189 78982057666241070347726321)
        ·
          refine ⟨59236543249680802760794741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78982057666241070347726321 59236543249680802760794741)
          ·
            refine ⟨5553425929657575258824507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59236543249680802760794741 5553425929657575258824507)
            ·
              refine ⟨8330138894486362888236761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553425929657575258824507 8330138894486362888236761)
              ·
                refine ⟨6247604170864772166177571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8330138894486362888236761 6247604170864772166177571)
                ·
                  refine ⟨9371406256297158249266357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6247604170864772166177571 9371406256297158249266357)
                  ·
                    refine ⟨878569336527858585868721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9371406256297158249266357 878569336527858585868721)
                    ·
                      rfl

theorem cell23_5133023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 5].length) (baseStart_5133023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133023 prefixEnd_5133023 := by exact prefixLift 5133023
  have htrace : WordTrace (prefixWord ++ tailWord_5133023) baseStart_5133023 baseEnd_5133023 := by
    simpa [prefixWord, tailWord_5133023, baseEnd_5133023] using wordTrace_append hprefix tailTrace_5133023
  have hstable : (prefixWord ++ tailWord_5133023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133023).length < 2 ^ (prefixWord ++ tailWord_5133023).sum := by decide
  have hdescent : baseEnd_5133023 < baseStart_5133023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133053 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_5133053 : Nat := 118140960795 + 5133053 * 2 ^ 59
def prefixEnd_5133053 : Nat := 4983230072969 + 3 ^ 40 * 5133053 * 2
def baseEnd_5133053 : Nat := 878574471334403546743675

theorem tailTrace_5133053 : CollatzResearch.WordTrace tailWord_5133053 prefixEnd_5133053 878574471334403546743675 := by
  unfold tailWord_5133053
  simp only [CollatzResearch.WordTrace]
  refine ⟨187217823472833111503387813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124811882315222074335591875 187217823472833111503387813)
  ·
    refine ⟨35103341901156208406885215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187217823472833111503387813 35103341901156208406885215)
    ·
      refine ⟨52655012851734312610327823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35103341901156208406885215 52655012851734312610327823)
      ·
        refine ⟨78982519277601468915491735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52655012851734312610327823 78982519277601468915491735)
        ·
          refine ⟨118473778916402203373237603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78982519277601468915491735 118473778916402203373237603)
          ·
            refine ⟨177710668374603305059856405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118473778916402203373237603 177710668374603305059856405)
            ·
              refine ⟨8330187580059529924680769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177710668374603305059856405 8330187580059529924680769)
              ·
                refine ⟨6247640685044647443510577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8330187580059529924680769 6247640685044647443510577)
                ·
                  refine ⟨4685730513783485582632933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6247640685044647443510577 4685730513783485582632933)
                  ·
                    refine ⟨878574471334403546743675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4685730513783485582632933 878574471334403546743675)
                    ·
                      rfl

theorem cell23_5133053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_5133053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133053 prefixEnd_5133053 := by exact prefixLift 5133053
  have htrace : WordTrace (prefixWord ++ tailWord_5133053) baseStart_5133053 baseEnd_5133053 := by
    simpa [prefixWord, tailWord_5133053, baseEnd_5133053] using wordTrace_append hprefix tailTrace_5133053
  have hstable : (prefixWord ++ tailWord_5133053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133053).length < 2 ^ (prefixWord ++ tailWord_5133053).sum := by decide
  have hdescent : baseEnd_5133053 < baseStart_5133053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133054 : List Nat := [4, 2, 2, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_5133054 : Nat := 118140960795 + 5133054 * 2 ^ 59
def prefixEnd_5133054 : Nat := 4983230072969 + 3 ^ 40 * 5133054 * 2
def baseEnd_5133054 : Nat := 2635723927483865136318521

theorem tailTrace_5133054 : CollatzResearch.WordTrace tailWord_5133054 prefixEnd_5133054 2635723927483865136318521 := by
  unfold tailWord_5133054
  simp only [CollatzResearch.WordTrace]
  refine ⟨23402232493228686084271777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124811906630552992449449477 23402232493228686084271777)
  ·
    refine ⟨17551674369921514563203833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23402232493228686084271777 17551674369921514563203833)
    ·
      refine ⟨13163755777441135922402875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17551674369921514563203833 13163755777441135922402875)
      ·
        refine ⟨19745633666161703883604313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13163755777441135922402875 19745633666161703883604313)
        ·
          refine ⟨14809225249621277912703235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19745633666161703883604313 14809225249621277912703235)
          ·
            refine ⟨22213837874431916869054853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14809225249621277912703235 22213837874431916869054853)
            ·
              refine ⟨4165094601455984412947785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22213837874431916869054853 4165094601455984412947785)
              ·
                refine ⟨3123820951091988309710839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4165094601455984412947785 3123820951091988309710839)
                ·
                  refine ⟨4685731426637982464566259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123820951091988309710839 4685731426637982464566259)
                  ·
                    refine ⟨7028597139956973696849389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4685731426637982464566259 7028597139956973696849389)
                    ·
                      refine ⟨2635723927483865136318521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028597139956973696849389 2635723927483865136318521)
                      ·
                        rfl

theorem cell23_5133054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_5133054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133054 prefixEnd_5133054 := by exact prefixLift 5133054
  have htrace : WordTrace (prefixWord ++ tailWord_5133054) baseStart_5133054 baseEnd_5133054 := by
    simpa [prefixWord, tailWord_5133054, baseEnd_5133054] using wordTrace_append hprefix tailTrace_5133054
  have hstable : (prefixWord ++ tailWord_5133054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133054).length < 2 ^ (prefixWord ++ tailWord_5133054).sum := by decide
  have hdescent : baseEnd_5133054 < baseStart_5133054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133060 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_5133060 : Nat := 118140960795 + 5133060 * 2 ^ 59
def prefixEnd_5133060 : Nat := 4983230072969 + 3 ^ 40 * 5133060 * 2
def baseEnd_5133060 : Nat := 2635727008367792112843493

theorem tailTrace_5133060 : CollatzResearch.WordTrace tailWord_5133060 prefixEnd_5133060 2635727008367792112843493 := by
  unfold tailWord_5133060
  simp only [CollatzResearch.WordTrace]
  refine ⟨93609039391903875849446317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124812052522538501132595089 93609039391903875849446317)
  ·
    refine ⟨35103389771963953443542369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93609039391903875849446317 35103389771963953443542369)
    ·
      refine ⟨26327542328972965082656777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35103389771963953443542369 26327542328972965082656777)
      ·
        refine ⟨19745656746729723811992583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26327542328972965082656777 19745656746729723811992583)
        ·
          refine ⟨29618485120094585717988875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19745656746729723811992583 29618485120094585717988875)
          ·
            refine ⟨44427727680141878576983313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29618485120094585717988875 44427727680141878576983313)
            ·
              refine ⟨33320795760106408932737485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44427727680141878576983313 33320795760106408932737485)
              ·
                refine ⟨12495298410039903349776557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33320795760106408932737485 12495298410039903349776557)
                ·
                  refine ⟨4685736903764963756166209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12495298410039903349776557 4685736903764963756166209)
                  ·
                    refine ⟨3514302677823722817124657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4685736903764963756166209 3514302677823722817124657)
                    ·
                      refine ⟨2635727008367792112843493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514302677823722817124657 2635727008367792112843493)
                      ·
                        rfl

theorem cell23_5133060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_5133060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133060 prefixEnd_5133060 := by exact prefixLift 5133060
  have htrace : WordTrace (prefixWord ++ tailWord_5133060) baseStart_5133060 baseEnd_5133060 := by
    simpa [prefixWord, tailWord_5133060, baseEnd_5133060] using wordTrace_append hprefix tailTrace_5133060
  have hstable : (prefixWord ++ tailWord_5133060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133060).length < 2 ^ (prefixWord ++ tailWord_5133060).sum := by decide
  have hdescent : baseEnd_5133060 < baseStart_5133060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133063 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_5133063 : Nat := 118140960795 + 5133063 * 2 ^ 59
def prefixEnd_5133063 : Nat := 4983230072969 + 3 ^ 40 * 5133063 * 2
def baseEnd_5133063 : Nat := 2635728548809755601105979

theorem tailTrace_5133063 : CollatzResearch.WordTrace tailWord_5133063 prefixEnd_5133063 2635728548809755601105979 := by
  unfold tailWord_5133063
  simp only [CollatzResearch.WordTrace]
  refine ⟨187218188202796883211251843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124812125468531255474167895 187218188202796883211251843)
  ·
    refine ⟨280827282304195324816877765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187218188202796883211251843 280827282304195324816877765)
    ·
      refine ⟨52655115432036623403164581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280827282304195324816877765 52655115432036623403164581)
      ·
        refine ⟨9872834143506866888093359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52655115432036623403164581 9872834143506866888093359)
        ·
          refine ⟨14809251215260300332140039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9872834143506866888093359 14809251215260300332140039)
          ·
            refine ⟨22213876822890450498210059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14809251215260300332140039 22213876822890450498210059)
            ·
              refine ⟨33320815234335675747315089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22213876822890450498210059 33320815234335675747315089)
              ·
                refine ⟨24990611425751756810486317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33320815234335675747315089 24990611425751756810486317)
                ·
                  refine ⟨9371479284656908803932369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24990611425751756810486317 9371479284656908803932369)
                  ·
                    refine ⟨7028609463492681602949277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9371479284656908803932369 7028609463492681602949277)
                    ·
                      refine ⟨2635728548809755601105979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028609463492681602949277 2635728548809755601105979)
                      ·
                        rfl

theorem cell23_5133063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_5133063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133063 prefixEnd_5133063 := by exact prefixLift 5133063
  have htrace : WordTrace (prefixWord ++ tailWord_5133063) baseStart_5133063 baseEnd_5133063 := by
    simpa [prefixWord, tailWord_5133063, baseEnd_5133063] using wordTrace_append hprefix tailTrace_5133063
  have hstable : (prefixWord ++ tailWord_5133063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133063).length < 2 ^ (prefixWord ++ tailWord_5133063).sum := by decide
  have hdescent : baseEnd_5133063 < baseStart_5133063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133093 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 3]
def baseStart_5133093 : Nat := 118140960795 + 5133093 * 2 ^ 59
def prefixEnd_5133093 : Nat := 4983230072969 + 3 ^ 40 * 5133093 * 2
def baseEnd_5133093 : Nat := 2635743953229390483730841

theorem tailTrace_5133093 : CollatzResearch.WordTrace tailWord_5133093 prefixEnd_5133093 2635743953229390483730841 := by
  unfold tailWord_5133093
  simp only [CollatzResearch.WordTrace]
  refine ⟨187219282392688198334843933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124812854928458798889895955 187219282392688198334843933)
  ·
    refine ⟨70207230897258074375566475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187219282392688198334843933 70207230897258074375566475)
    ·
      refine ⟨105310846345887111563349713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70207230897258074375566475 105310846345887111563349713)
      ·
        refine ⟨78983134759415333672512285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105310846345887111563349713 78983134759415333672512285)
        ·
          refine ⟨29618675534780750127192107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78983134759415333672512285 29618675534780750127192107)
          ·
            refine ⟨44428013302171125190788161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29618675534780750127192107 44428013302171125190788161)
            ·
              refine ⟨33321009976628343893091121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44428013302171125190788161 33321009976628343893091121)
              ·
                refine ⟨24990757482471257919818341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33321009976628343893091121 24990757482471257919818341)
                ·
                  refine ⟨4685767027963360859965939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24990757482471257919818341 4685767027963360859965939)
                  ·
                    refine ⟨7028650541945041289948909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4685767027963360859965939 7028650541945041289948909)
                    ·
                      refine ⟨2635743953229390483730841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028650541945041289948909 2635743953229390483730841)
                      ·
                        rfl

theorem cell23_5133093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_5133093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133093 prefixEnd_5133093 := by exact prefixLift 5133093
  have htrace : WordTrace (prefixWord ++ tailWord_5133093) baseStart_5133093 baseEnd_5133093 := by
    simpa [prefixWord, tailWord_5133093, baseEnd_5133093] using wordTrace_append hprefix tailTrace_5133093
  have hstable : (prefixWord ++ tailWord_5133093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133093).length < 2 ^ (prefixWord ++ tailWord_5133093).sum := by decide
  have hdescent : baseEnd_5133093 < baseStart_5133093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133124 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5133124 : Nat := 118140960795 + 5133124 * 2 ^ 59
def prefixEnd_5133124 : Nat := 4983230072969 + 3 ^ 40 * 5133124 * 2
def baseEnd_5133124 : Nat := 2635759871129679862443199

theorem tailTrace_5133124 : CollatzResearch.WordTrace tailWord_5133124 prefixEnd_5133124 2635759871129679862443199 := by
  unfold tailWord_5133124
  simp only [CollatzResearch.WordTrace]
  refine ⟨93610206527787945314611213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124813608703717260419481617 93610206527787945314611213)
  ·
    refine ⟨35103827447920479492979205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93610206527787945314611213 35103827447920479492979205)
    ·
      refine ⟨6581967646485089904933601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35103827447920479492979205 6581967646485089904933601)
      ·
        refine ⟨4936475734863817428700201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6581967646485089904933601 4936475734863817428700201)
        ·
          refine ⟨3702356801147863071525151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4936475734863817428700201 3702356801147863071525151)
          ·
            refine ⟨5553535201721794607287727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702356801147863071525151 5553535201721794607287727)
            ·
              refine ⟨8330302802582691910931591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553535201721794607287727 8330302802582691910931591)
              ·
                refine ⟨12495454203874037866397387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8330302802582691910931591 12495454203874037866397387)
                ·
                  refine ⟨18743181305811056799596081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12495454203874037866397387 18743181305811056799596081)
                  ·
                    refine ⟨14057385979358292599697061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18743181305811056799596081 14057385979358292599697061)
                    ·
                      refine ⟨2635759871129679862443199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14057385979358292599697061 2635759871129679862443199)
                      ·
                        rfl

theorem cell23_5133124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5133124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133124 prefixEnd_5133124 := by exact prefixLift 5133124
  have htrace : WordTrace (prefixWord ++ tailWord_5133124) baseStart_5133124 baseEnd_5133124 := by
    simpa [prefixWord, tailWord_5133124, baseEnd_5133124] using wordTrace_append hprefix tailTrace_5133124
  have hstable : (prefixWord ++ tailWord_5133124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133124).length < 2 ^ (prefixWord ++ tailWord_5133124).sum := by decide
  have hdescent : baseEnd_5133124 < baseStart_5133124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133136 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 3]
def baseStart_5133136 : Nat := 118140960795 + 5133136 * 2 ^ 59
def prefixEnd_5133136 : Nat := 4983230072969 + 3 ^ 40 * 5133136 * 2
def baseEnd_5133136 : Nat := 2635766032897533815493143

theorem tailTrace_5133136 : CollatzResearch.WordTrace tailWord_5133136 prefixEnd_5133136 2635766032897533815493143 := by
  unfold tailWord_5133136
  simp only [CollatzResearch.WordTrace]
  refine ⟨93610425365766208339329631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124813900487688277785772841 93610425365766208339329631)
  ·
    refine ⟨140415638048649312508994447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93610425365766208339329631 140415638048649312508994447)
    ·
      refine ⟨210623457072973968763491671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140415638048649312508994447 210623457072973968763491671)
      ·
        refine ⟨315935185609460953145237507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210623457072973968763491671 315935185609460953145237507)
        ·
          refine ⟨473902778414191429717856261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315935185609460953145237507 473902778414191429717856261)
          ·
            refine ⟨88856770952660893072098049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 473902778414191429717856261 88856770952660893072098049)
            ·
              refine ⟨66642578214495669804073537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88856770952660893072098049 66642578214495669804073537)
              ·
                refine ⟨49981933660871752353055153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66642578214495669804073537 49981933660871752353055153)
                ·
                  refine ⟨37486450245653814264791365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49981933660871752353055153 37486450245653814264791365)
                  ·
                    refine ⟨7028709421060090174648381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37486450245653814264791365 7028709421060090174648381)
                    ·
                      refine ⟨2635766032897533815493143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028709421060090174648381 2635766032897533815493143)
                      ·
                        rfl

theorem cell23_5133136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_5133136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133136 prefixEnd_5133136 := by exact prefixLift 5133136
  have htrace : WordTrace (prefixWord ++ tailWord_5133136) baseStart_5133136 baseEnd_5133136 := by
    simpa [prefixWord, tailWord_5133136, baseEnd_5133136] using wordTrace_append hprefix tailTrace_5133136
  have hstable : (prefixWord ++ tailWord_5133136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133136).length < 2 ^ (prefixWord ++ tailWord_5133136).sum := by decide
  have hdescent : baseEnd_5133136 < baseStart_5133136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133137 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 1, 3, 2]
def baseStart_5133137 : Nat := 118140960795 + 5133137 * 2 ^ 59
def prefixEnd_5133137 : Nat := 4983230072969 + 3 ^ 40 * 5133137 * 2
def baseEnd_5133137 : Nat := 2635766546378188311580639

theorem tailTrace_5133137 : CollatzResearch.WordTrace tailWord_5133137 prefixEnd_5133137 2635766546378188311580639 := by
  unfold tailWord_5133137
  simp only [CollatzResearch.WordTrace]
  refine ⟨187220887204528793849445665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124813924803019195899630443 187220887204528793849445665)
  ·
    refine ⟨140415665403396595387084249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187220887204528793849445665 140415665403396595387084249)
    ·
      refine ⟨105311749052547446540313187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140415665403396595387084249 105311749052547446540313187)
      ·
        refine ⟨157967623578821169810469781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105311749052547446540313187 157967623578821169810469781)
        ·
          refine ⟨7404732355257242334865771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 157967623578821169810469781 7404732355257242334865771)
          ·
            refine ⟨11107098532885863502298657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7404732355257242334865771 11107098532885863502298657)
            ·
              refine ⟨8330323899664397626723993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11107098532885863502298657 8330323899664397626723993)
              ·
                refine ⟨6247742924748298220042995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8330323899664397626723993 6247742924748298220042995)
                ·
                  refine ⟨9371614387122447330064493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6247742924748298220042995 9371614387122447330064493)
                  ·
                    refine ⟨3514355395170917748774185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9371614387122447330064493 3514355395170917748774185)
                    ·
                      refine ⟨2635766546378188311580639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514355395170917748774185 2635766546378188311580639)
                      ·
                        rfl

theorem cell23_5133137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_5133137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133137 prefixEnd_5133137 := by exact prefixLift 5133137
  have htrace : WordTrace (prefixWord ++ tailWord_5133137) baseStart_5133137 baseEnd_5133137 := by
    simpa [prefixWord, tailWord_5133137, baseEnd_5133137] using wordTrace_append hprefix tailTrace_5133137
  have hstable : (prefixWord ++ tailWord_5133137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133137).length < 2 ^ (prefixWord ++ tailWord_5133137).sum := by decide
  have hdescent : baseEnd_5133137 < baseStart_5133137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133173 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 7]
def baseStart_5133173 : Nat := 118140960795 + 5133173 * 2 ^ 59
def prefixEnd_5133173 : Nat := 4983230072969 + 3 ^ 40 * 5133173 * 2
def baseEnd_5133173 : Nat := 292865003520194463414497

theorem tailTrace_5133173 : CollatzResearch.WordTrace tailWord_5133173 prefixEnd_5133173 292865003520194463414497 := by
  unfold tailWord_5133173
  simp only [CollatzResearch.WordTrace]
  refine ⟨187222200232398371997756173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124814800154932247998504115 187222200232398371997756173)
  ·
    refine ⟨70208325087149389499158565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187222200232398371997756173 70208325087149389499158565)
    ·
      refine ⟨13164060953840510531092231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70208325087149389499158565 13164060953840510531092231)
      ·
        refine ⟨19746091430760765796638347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13164060953840510531092231 19746091430760765796638347)
        ·
          refine ⟨29619137146141148694957521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19746091430760765796638347 29619137146141148694957521)
          ·
            refine ⟨22214352859605861521218141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29619137146141148694957521 22214352859605861521218141)
            ·
              refine ⟨8330382322352198070456803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22214352859605861521218141 8330382322352198070456803)
              ·
                refine ⟨12495573483528297105685205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8330382322352198070456803 12495573483528297105685205)
                ·
                  refine ⟨292865003520194463414497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12495573483528297105685205 292865003520194463414497)
                  ·
                    rfl

theorem cell23_5133173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_5133173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133173 prefixEnd_5133173 := by exact prefixLift 5133173
  have htrace : WordTrace (prefixWord ++ tailWord_5133173) baseStart_5133173 baseEnd_5133173 := by
    simpa [prefixWord, tailWord_5133173, baseEnd_5133173] using wordTrace_append hprefix tailTrace_5133173
  have hstable : (prefixWord ++ tailWord_5133173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133173).length < 2 ^ (prefixWord ++ tailWord_5133173).sum := by decide
  have hdescent : baseEnd_5133173 < baseStart_5133173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133240 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 2, 4, 2]
def baseStart_5133240 : Nat := 118140960795 + 5133240 * 2 ^ 59
def prefixEnd_5133240 : Nat := 4983230072969 + 3 ^ 40 * 5133240 * 2
def baseEnd_5133240 : Nat := 2635819434885601408592665

theorem tailTrace_5133240 : CollatzResearch.WordTrace tailWord_5133240 prefixEnd_5133240 2635819434885601408592665 := by
  unfold tailWord_5133240
  simp only [CollatzResearch.WordTrace]
  refine ⟨93612321961577821220222587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124816429282103761626963449 93612321961577821220222587)
  ·
    refine ⟨140418482942366731830333881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93612321961577821220222587 140418482942366731830333881)
    ·
      refine ⟨105313862206775048872750411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140418482942366731830333881 105313862206775048872750411)
      ·
        refine ⟨157970793310162573309125617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105313862206775048872750411 157970793310162573309125617)
        ·
          refine ⟨118478094982621929981844213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157970793310162573309125617 118478094982621929981844213)
          ·
            refine ⟨11107321404620805935797895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118478094982621929981844213 11107321404620805935797895)
            ·
              refine ⟨16660982106931208903696843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11107321404620805935797895 16660982106931208903696843)
              ·
                refine ⟨24991473160396813355545265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16660982106931208903696843 24991473160396813355545265)
                ·
                  refine ⟨18743604870297610016658949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24991473160396813355545265 18743604870297610016658949)
                  ·
                    refine ⟨3514425913180801878123553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18743604870297610016658949 3514425913180801878123553)
                    ·
                      refine ⟨2635819434885601408592665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514425913180801878123553 2635819434885601408592665)
                      ·
                        rfl

theorem cell23_5133240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_5133240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133240 prefixEnd_5133240 := by exact prefixLift 5133240
  have htrace : WordTrace (prefixWord ++ tailWord_5133240) baseStart_5133240 baseEnd_5133240 := by
    simpa [prefixWord, tailWord_5133240, baseEnd_5133240] using wordTrace_append hprefix tailTrace_5133240
  have hstable : (prefixWord ++ tailWord_5133240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133240).length < 2 ^ (prefixWord ++ tailWord_5133240).sum := by decide
  have hdescent : baseEnd_5133240 < baseStart_5133240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133270 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5133270 : Nat := 118140960795 + 5133270 * 2 ^ 59
def prefixEnd_5133270 : Nat := 4983230072969 + 3 ^ 40 * 5133270 * 2
def baseEnd_5133270 : Nat := 2635834839305236291217527

theorem tailTrace_5133270 : CollatzResearch.WordTrace tailWord_5133270 prefixEnd_5133270 2635834839305236291217527 := by
  unfold tailWord_5133270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11701608632065434847752329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124817158742031305042691509 11701608632065434847752329)
  ·
    refine ⟨8776206474049076135814247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11701608632065434847752329 8776206474049076135814247)
    ·
      refine ⟨13164309711073614203721371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8776206474049076135814247 13164309711073614203721371)
      ·
        refine ⟨19746464566610421305582057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13164309711073614203721371 19746464566610421305582057)
        ·
          refine ⟨14809848424957815979186543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19746464566610421305582057 14809848424957815979186543)
          ·
            refine ⟨22214772637436723968779815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14809848424957815979186543 22214772637436723968779815)
            ·
              refine ⟨33322158956155085953169723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22214772637436723968779815 33322158956155085953169723)
              ·
                refine ⟨49983238434232628929754585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33322158956155085953169723 49983238434232628929754585)
                ·
                  refine ⟨37487428825674471697315939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49983238434232628929754585 37487428825674471697315939)
                  ·
                    refine ⟨56231143238511707545973909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37487428825674471697315939 56231143238511707545973909)
                    ·
                      refine ⟨2635834839305236291217527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56231143238511707545973909 2635834839305236291217527)
                      ·
                        rfl

theorem cell23_5133270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5133270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133270 prefixEnd_5133270 := by exact prefixLift 5133270
  have htrace : WordTrace (prefixWord ++ tailWord_5133270) baseStart_5133270 baseEnd_5133270 := by
    simpa [prefixWord, tailWord_5133270, baseEnd_5133270] using wordTrace_append hprefix tailTrace_5133270
  have hstable : (prefixWord ++ tailWord_5133270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133270).length < 2 ^ (prefixWord ++ tailWord_5133270).sum := by decide
  have hdescent : baseEnd_5133270 < baseStart_5133270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133324 : List Nat := [2, 2, 1, 2, 3, 2, 3, 3, 1, 1, 3]
def baseStart_5133324 : Nat := 118140960795 + 5133324 * 2 ^ 59
def prefixEnd_5133324 : Nat := 4983230072969 + 3 ^ 40 * 5133324 * 2
def baseEnd_5133324 : Nat := 2635862567260579079942279

theorem tailTrace_5133324 : CollatzResearch.WordTrace tailWord_5133324 prefixEnd_5133324 2635862567260579079942279 := by
  unfold tailWord_5133324
  simp only [CollatzResearch.WordTrace]
  refine ⟨93613853827425662393251513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124818471769900883191002017 93613853827425662393251513)
  ·
    refine ⟨70210390370569246794938635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93613853827425662393251513 70210390370569246794938635)
    ·
      refine ⟨105315585555853870192407953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70210390370569246794938635 105315585555853870192407953)
      ·
        refine ⟨78986689166890402644305965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105315585555853870192407953 78986689166890402644305965)
        ·
          refine ⟨29620008437583900991614737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78986689166890402644305965 29620008437583900991614737)
          ·
            refine ⟨22215006328187925743711053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29620008437583900991614737 22215006328187925743711053)
            ·
              refine ⟨8330627373070472153891645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22215006328187925743711053 8330627373070472153891645)
              ·
                refine ⟨3123985264901427057709367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8330627373070472153891645 3123985264901427057709367)
                ·
                  refine ⟨4685977897352140586564051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123985264901427057709367 4685977897352140586564051)
                  ·
                    refine ⟨7028966846028210879846077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4685977897352140586564051 7028966846028210879846077)
                    ·
                      refine ⟨2635862567260579079942279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028966846028210879846077 2635862567260579079942279)
                      ·
                        rfl

theorem cell23_5133324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_5133324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133324 prefixEnd_5133324 := by exact prefixLift 5133324
  have htrace : WordTrace (prefixWord ++ tailWord_5133324) baseStart_5133324 baseEnd_5133324 := by
    simpa [prefixWord, tailWord_5133324, baseEnd_5133324] using wordTrace_append hprefix tailTrace_5133324
  have hstable : (prefixWord ++ tailWord_5133324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133324).length < 2 ^ (prefixWord ++ tailWord_5133324).sum := by decide
  have hdescent : baseEnd_5133324 < baseStart_5133324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133341 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_5133341 : Nat := 118140960795 + 5133341 * 2 ^ 59
def prefixEnd_5133341 : Nat := 4983230072969 + 3 ^ 40 * 5133341 * 2
def baseEnd_5133341 : Nat := 2635871296431705513429701

theorem tailTrace_5133341 : CollatzResearch.WordTrace tailWord_5133341 prefixEnd_5133341 2635871296431705513429701 := by
  unfold tailWord_5133341
  simp only [CollatzResearch.WordTrace]
  refine ⟨187228327695789736689871877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124818885130526491126581251 187228327695789736689871877)
  ·
    refine ⟨35105311442960575629350977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187228327695789736689871877 35105311442960575629350977)
    ·
      refine ⟨26328983582220431722013233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35105311442960575629350977 26328983582220431722013233)
      ·
        refine ⟨19746737686665323791509925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26328983582220431722013233 19746737686665323791509925)
        ·
          refine ⟨3702513316249748210908111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19746737686665323791509925 3702513316249748210908111)
          ·
            refine ⟨5553769974374622316362167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702513316249748210908111 5553769974374622316362167)
            ·
              refine ⟨8330654961561933474543251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553769974374622316362167 8330654961561933474543251)
              ·
                refine ⟨12495982442342900211814877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8330654961561933474543251 12495982442342900211814877)
                ·
                  refine ⟨4685993415878587579430579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12495982442342900211814877 4685993415878587579430579)
                  ·
                    refine ⟨7028990123817881369145869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4685993415878587579430579 7028990123817881369145869)
                    ·
                      refine ⟨2635871296431705513429701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7028990123817881369145869 2635871296431705513429701)
                      ·
                        rfl

theorem cell23_5133341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_5133341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133341 prefixEnd_5133341 := by exact prefixLift 5133341
  have htrace : WordTrace (prefixWord ++ tailWord_5133341) baseStart_5133341 baseEnd_5133341 := by
    simpa [prefixWord, tailWord_5133341, baseEnd_5133341] using wordTrace_append hprefix tailTrace_5133341
  have hstable : (prefixWord ++ tailWord_5133341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133341).length < 2 ^ (prefixWord ++ tailWord_5133341).sum := by decide
  have hdescent : baseEnd_5133341 < baseStart_5133341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133343 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_5133343 : Nat := 118140960795 + 5133343 * 2 ^ 59
def prefixEnd_5133343 : Nat := 4983230072969 + 3 ^ 40 * 5133343 * 2
def baseEnd_5133343 : Nat := 2635872323393014505604691

theorem tailTrace_5133343 : CollatzResearch.WordTrace tailWord_5133343 prefixEnd_5133343 2635872323393014505604691 := by
  unfold tailWord_5133343
  simp only [CollatzResearch.WordTrace]
  refine ⟨187228400641782491031444683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124818933761188327354296455 187228400641782491031444683)
  ·
    refine ⟨280842600962673736547167025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187228400641782491031444683 280842600962673736547167025)
    ·
      refine ⟨210631950722005302410375269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280842600962673736547167025 210631950722005302410375269)
      ·
        refine ⟨39493490760375994201945363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210631950722005302410375269 39493490760375994201945363)
        ·
          refine ⟨59240236140563991302918045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39493490760375994201945363 59240236140563991302918045)
          ·
            refine ⟨22215088552711496738594267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59240236140563991302918045 22215088552711496738594267)
            ·
              refine ⟨33322632829067245107891401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22215088552711496738594267 33322632829067245107891401)
              ·
                refine ⟨24991974621800433830918551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33322632829067245107891401 24991974621800433830918551)
                ·
                  refine ⟨37487961932700650746377827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24991974621800433830918551 37487961932700650746377827)
                  ·
                    refine ⟨56231942899050976119566741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37487961932700650746377827 56231942899050976119566741)
                    ·
                      refine ⟨2635872323393014505604691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56231942899050976119566741 2635872323393014505604691)
                      ·
                        rfl

theorem cell23_5133343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_5133343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133343 prefixEnd_5133343 := by exact prefixLift 5133343
  have htrace : WordTrace (prefixWord ++ tailWord_5133343) baseStart_5133343 baseEnd_5133343 := by
    simpa [prefixWord, tailWord_5133343, baseEnd_5133343] using wordTrace_append hprefix tailTrace_5133343
  have hstable : (prefixWord ++ tailWord_5133343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133343).length < 2 ^ (prefixWord ++ tailWord_5133343).sum := by decide
  have hdescent : baseEnd_5133343 < baseStart_5133343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133364 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5133364 : Nat := 118140960795 + 5133364 * 2 ^ 59
def prefixEnd_5133364 : Nat := 4983230072969 + 3 ^ 40 * 5133364 * 2
def baseEnd_5133364 : Nat := 2635883106486758923442095

theorem tailTrace_5133364 : CollatzResearch.WordTrace tailWord_5133364 prefixEnd_5133364 2635883106486758923442095 := by
  unfold tailWord_5133364
  simp only [CollatzResearch.WordTrace]
  refine ⟨93614583287353205808979573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124819444383137607745306097 93614583287353205808979573)
  ·
    refine ⟨8776367183189363044591835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93614583287353205808979573 8776367183189363044591835)
    ·
      refine ⟨13164550774784044566887753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8776367183189363044591835 13164550774784044566887753)
      ·
        refine ⟨9873413081088033425165815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13164550774784044566887753 9873413081088033425165815)
        ·
          refine ⟨14810119621632050137748723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9873413081088033425165815 14810119621632050137748723)
          ·
            refine ⟨22215179432448075206623085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14810119621632050137748723 22215179432448075206623085)
            ·
              refine ⟨8330692287168028202483657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22215179432448075206623085 8330692287168028202483657)
              ·
                refine ⟨6248019215376021151862743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8330692287168028202483657 6248019215376021151862743)
                ·
                  refine ⟨9372028823064031727794115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6248019215376021151862743 9372028823064031727794115)
                  ·
                    refine ⟨14058043234596047591691173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9372028823064031727794115 14058043234596047591691173)
                    ·
                      refine ⟨2635883106486758923442095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14058043234596047591691173 2635883106486758923442095)
                      ·
                        rfl

theorem cell23_5133364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5133364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133364 prefixEnd_5133364 := by exact prefixLift 5133364
  have htrace : WordTrace (prefixWord ++ tailWord_5133364) baseStart_5133364 baseEnd_5133364 := by
    simpa [prefixWord, tailWord_5133364, baseEnd_5133364] using wordTrace_append hprefix tailTrace_5133364
  have hstable : (prefixWord ++ tailWord_5133364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133364).length < 2 ^ (prefixWord ++ tailWord_5133364).sum := by decide
  have hdescent : baseEnd_5133364 < baseStart_5133364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133377 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_5133377 : Nat := 118140960795 + 5133377 * 2 ^ 59
def prefixEnd_5133377 : Nat := 4983230072969 + 3 ^ 40 * 5133377 * 2
def baseEnd_5133377 : Nat := 2635889781735267372579535

theorem tailTrace_5133377 : CollatzResearch.WordTrace tailWord_5133377 prefixEnd_5133377 2635889781735267372579535 := by
  unfold tailWord_5133377
  simp only [CollatzResearch.WordTrace]
  refine ⟨187229640723659314838182385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124819760482439543225454923 187229640723659314838182385)
  ·
    refine ⟨140422230542744486128636789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187229640723659314838182385 140422230542744486128636789)
    ·
      refine ⟨13164584113382295574559699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140422230542744486128636789 13164584113382295574559699)
      ·
        refine ⟨19746876170073443361839549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13164584113382295574559699 19746876170073443361839549)
        ·
          refine ⟨7405078563777541260689831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19746876170073443361839549 7405078563777541260689831)
          ·
            refine ⟨11107617845666311891034747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7405078563777541260689831 11107617845666311891034747)
            ·
              refine ⟨16661426768499467836552121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11107617845666311891034747 16661426768499467836552121)
              ·
                refine ⟨12496070076374600877414091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16661426768499467836552121 12496070076374600877414091)
                ·
                  refine ⟨18744105114561901316121137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12496070076374600877414091 18744105114561901316121137)
                  ·
                    refine ⟨14058078835921425987090853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18744105114561901316121137 14058078835921425987090853)
                    ·
                      refine ⟨2635889781735267372579535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14058078835921425987090853 2635889781735267372579535)
                      ·
                        rfl

theorem cell23_5133377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_5133377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133377 prefixEnd_5133377 := by exact prefixLift 5133377
  have htrace : WordTrace (prefixWord ++ tailWord_5133377) baseStart_5133377 baseEnd_5133377 := by
    simpa [prefixWord, tailWord_5133377, baseEnd_5133377] using wordTrace_append hprefix tailTrace_5133377
  have hstable : (prefixWord ++ tailWord_5133377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133377).length < 2 ^ (prefixWord ++ tailWord_5133377).sum := by decide
  have hdescent : baseEnd_5133377 < baseStart_5133377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133393 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_5133393 : Nat := 118140960795 + 5133393 * 2 ^ 59
def prefixEnd_5133393 : Nat := 4983230072969 + 3 ^ 40 * 5133393 * 2
def baseEnd_5133393 : Nat := 2635897997425739309979461

theorem tailTrace_5133393 : CollatzResearch.WordTrace tailWord_5133393 prefixEnd_5133393 2635897997425739309979461 := by
  unfold tailWord_5133393
  simp only [CollatzResearch.WordTrace]
  refine ⟨187230224291601349570764833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124820149527734233047176555 187230224291601349570764833)
  ·
    refine ⟨140422668218701012178073625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187230224291601349570764833 140422668218701012178073625)
    ·
      refine ⟨105317001164025759133555219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140422668218701012178073625 105317001164025759133555219)
      ·
        refine ⟨157975501746038638700332829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105317001164025759133555219 157975501746038638700332829)
        ·
          refine ⟨59240813154764489512624811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157975501746038638700332829 59240813154764489512624811)
          ·
            refine ⟨88861219732146734268937217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59240813154764489512624811 88861219732146734268937217)
            ·
              refine ⟨66645914799110050701702913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88861219732146734268937217 66645914799110050701702913)
              ·
                refine ⟨49984436099332538026277185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66645914799110050701702913 49984436099332538026277185)
                ·
                  refine ⟨37488327074499403519707889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49984436099332538026277185 37488327074499403519707889)
                  ·
                    refine ⟨28116245305874552639780917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37488327074499403519707889 28116245305874552639780917)
                    ·
                      refine ⟨2635897997425739309979461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28116245305874552639780917 2635897997425739309979461)
                      ·
                        rfl

theorem cell23_5133393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_5133393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133393 prefixEnd_5133393 := by exact prefixLift 5133393
  have htrace : WordTrace (prefixWord ++ tailWord_5133393) baseStart_5133393 baseEnd_5133393 := by
    simpa [prefixWord, tailWord_5133393, baseEnd_5133393] using wordTrace_append hprefix tailTrace_5133393
  have hstable : (prefixWord ++ tailWord_5133393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133393).length < 2 ^ (prefixWord ++ tailWord_5133393).sum := by decide
  have hdescent : baseEnd_5133393 < baseStart_5133393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133430 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_5133430 : Nat := 118140960795 + 5133430 * 2 ^ 59
def prefixEnd_5133430 : Nat := 4983230072969 + 3 ^ 40 * 5133430 * 2
def baseEnd_5133430 : Nat := 878638998736651888405597

theorem tailTrace_5133430 : CollatzResearch.WordTrace tailWord_5133430 prefixEnd_5133430 878638998736651888405597 := by
  unfold tailWord_5133430
  simp only [CollatzResearch.WordTrace]
  refine ⟨11701973362029206555616359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124821049194978203259907829 11701973362029206555616359)
  ·
    refine ⟨17552960043043809833424539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11701973362029206555616359 17552960043043809833424539)
    ·
      refine ⟨26329440064565714750136809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17552960043043809833424539 26329440064565714750136809)
      ·
        refine ⟨19747080048424286062602607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26329440064565714750136809 19747080048424286062602607)
        ·
          refine ⟨29620620072636429093903911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19747080048424286062602607 29620620072636429093903911)
          ·
            refine ⟨44430930108954643640855867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29620620072636429093903911 44430930108954643640855867)
            ·
              refine ⟨66646395163431965461283801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44430930108954643640855867 66646395163431965461283801)
              ·
                refine ⟨49984796372573974095962851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66646395163431965461283801 49984796372573974095962851)
                ·
                  refine ⟨74977194558860961143944277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49984796372573974095962851 74977194558860961143944277)
                  ·
                    refine ⟨878638998736651888405597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74977194558860961143944277 878638998736651888405597)
                    ·
                      rfl

theorem cell23_5133430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_5133430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133430 prefixEnd_5133430 := by exact prefixLift 5133430
  have htrace : WordTrace (prefixWord ++ tailWord_5133430) baseStart_5133430 baseEnd_5133430 := by
    simpa [prefixWord, tailWord_5133430, baseEnd_5133430] using wordTrace_append hprefix tailTrace_5133430
  have hstable : (prefixWord ++ tailWord_5133430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133430).length < 2 ^ (prefixWord ++ tailWord_5133430).sum := by decide
  have hdescent : baseEnd_5133430 < baseStart_5133430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133437 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_5133437 : Nat := 118140960795 + 5133437 * 2 ^ 59
def prefixEnd_5133437 : Nat := 4983230072969 + 3 ^ 40 * 5133437 * 2
def baseEnd_5133437 : Nat := 2635920590574537137829259

theorem tailTrace_5133437 : CollatzResearch.WordTrace tailWord_5133437 prefixEnd_5133437 2635920590574537137829259 := by
  unfold tailWord_5133437
  simp only [CollatzResearch.WordTrace]
  refine ⟨187231829103441945085366565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124821219402294630056911043 187231829103441945085366565)
  ·
    refine ⟨35105967956895364703506231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187231829103441945085366565 35105967956895364703506231)
    ·
      refine ⟨52658951935343047055259347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35105967956895364703506231 52658951935343047055259347)
      ·
        refine ⟨78988427903014570582889021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52658951935343047055259347 78988427903014570582889021)
        ·
          refine ⟨29620660463630463968583383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78988427903014570582889021 29620660463630463968583383)
          ·
            refine ⟨44430990695445695952875075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29620660463630463968583383 44430990695445695952875075)
            ·
              refine ⟨66646486043168543929312613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44430990695445695952875075 66646486043168543929312613)
              ·
                refine ⟨12496216133094101986746115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66646486043168543929312613 12496216133094101986746115)
                ·
                  refine ⟨18744324199641152980119173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12496216133094101986746115 18744324199641152980119173)
                  ·
                    refine ⟨3514560787432716183772345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18744324199641152980119173 3514560787432716183772345)
                    ·
                      refine ⟨2635920590574537137829259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514560787432716183772345 2635920590574537137829259)
                      ·
                        rfl

theorem cell23_5133437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_5133437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133437 prefixEnd_5133437 := by exact prefixLift 5133437
  have htrace : WordTrace (prefixWord ++ tailWord_5133437) baseStart_5133437 baseEnd_5133437 := by
    simpa [prefixWord, tailWord_5133437, baseEnd_5133437] using wordTrace_append hprefix tailTrace_5133437
  have hstable : (prefixWord ++ tailWord_5133437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133437).length < 2 ^ (prefixWord ++ tailWord_5133437).sum := by decide
  have hdescent : baseEnd_5133437 < baseStart_5133437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133441 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_5133441 : Nat := 118140960795 + 5133441 * 2 ^ 59
def prefixEnd_5133441 : Nat := 4983230072969 + 3 ^ 40 * 5133441 * 2
def baseEnd_5133441 : Nat := 2635922644497155122179241

theorem tailTrace_5133441 : CollatzResearch.WordTrace tailWord_5133441 prefixEnd_5133441 2635922644497155122179241 := by
  unfold tailWord_5133441
  simp only [CollatzResearch.WordTrace]
  refine ⟨187231974995427453768512177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124821316663618302512341451 187231974995427453768512177)
  ·
    refine ⟨140423981246570590326384133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187231974995427453768512177 140423981246570590326384133)
    ·
      refine ⟨26329496483731985686197025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140423981246570590326384133 26329496483731985686197025)
      ·
        refine ⟨19747122362798989264647769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26329496483731985686197025 19747122362798989264647769)
        ·
          refine ⟨14810341772099241948485827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19747122362798989264647769 14810341772099241948485827)
          ·
            refine ⟨22215512658148862922728741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14810341772099241948485827 22215512658148862922728741)
            ·
              refine ⟨4165408623402911798011639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22215512658148862922728741 4165408623402911798011639)
              ·
                refine ⟨6248112935104367697017459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165408623402911798011639 6248112935104367697017459)
                ·
                  refine ⟨9372169402656551545526189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6248112935104367697017459 9372169402656551545526189)
                  ·
                    refine ⟨3514563525996206829572321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9372169402656551545526189 3514563525996206829572321)
                    ·
                      refine ⟨2635922644497155122179241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514563525996206829572321 2635922644497155122179241)
                      ·
                        rfl

theorem cell23_5133441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_5133441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133441 prefixEnd_5133441 := by exact prefixLift 5133441
  have htrace : WordTrace (prefixWord ++ tailWord_5133441) baseStart_5133441 baseEnd_5133441 := by
    simpa [prefixWord, tailWord_5133441, baseEnd_5133441] using wordTrace_append hprefix tailTrace_5133441
  have hstable : (prefixWord ++ tailWord_5133441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133441).length < 2 ^ (prefixWord ++ tailWord_5133441).sum := by decide
  have hdescent : baseEnd_5133441 < baseStart_5133441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133443 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 9]
def baseStart_5133443 : Nat := 118140960795 + 5133443 * 2 ^ 59
def prefixEnd_5133443 : Nat := 4983230072969 + 3 ^ 40 * 5133443 * 2
def baseEnd_5133443 : Nat := 292880407939829346039359

theorem tailTrace_5133443 : CollatzResearch.WordTrace tailWord_5133443 prefixEnd_5133443 292880407939829346039359 := by
  unfold tailWord_5133443
  simp only [CollatzResearch.WordTrace]
  refine ⟨187232047941420208110084983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124821365294280138740056655 187232047941420208110084983)
  ·
    refine ⟨280848071912130312165127475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187232047941420208110084983 280848071912130312165127475)
    ·
      refine ⟨421272107868195468247691213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280848071912130312165127475 421272107868195468247691213)
      ·
        refine ⟨157977040450573300592884205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421272107868195468247691213 157977040450573300592884205)
        ·
          refine ⟨59241390168964987722331577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157977040450573300592884205 59241390168964987722331577)
          ·
            refine ⟨44431042626723740791748683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59241390168964987722331577 44431042626723740791748683)
            ·
              refine ⟨66646563940085611187623025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44431042626723740791748683 66646563940085611187623025)
              ·
                refine ⟨49984922955064208390717269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66646563940085611187623025 49984922955064208390717269)
                ·
                  refine ⟨292880407939829346039359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49984922955064208390717269 292880407939829346039359)
                  ·
                    rfl

theorem cell23_5133443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 9].length) (baseStart_5133443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133443 prefixEnd_5133443 := by exact prefixLift 5133443
  have htrace : WordTrace (prefixWord ++ tailWord_5133443) baseStart_5133443 baseEnd_5133443 := by
    simpa [prefixWord, tailWord_5133443, baseEnd_5133443] using wordTrace_append hprefix tailTrace_5133443
  have hstable : (prefixWord ++ tailWord_5133443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133443).length < 2 ^ (prefixWord ++ tailWord_5133443).sum := by decide
  have hdescent : baseEnd_5133443 < baseStart_5133443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133448 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_5133448 : Nat := 118140960795 + 5133448 * 2 ^ 59
def prefixEnd_5133448 : Nat := 4983230072969 + 3 ^ 40 * 5133448 * 2
def baseEnd_5133448 : Nat := 2635926238861736594791709

theorem tailTrace_5133448 : CollatzResearch.WordTrace tailWord_5133448 prefixEnd_5133448 2635926238861736594791709 := by
  unfold tailWord_5133448
  simp only [CollatzResearch.WordTrace]
  refine ⟨93616115153201046982008499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124821486870934729309344665 93616115153201046982008499)
  ·
    refine ⟨140424172729801570473012749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93616115153201046982008499 140424172729801570473012749)
    ·
      refine ⟨52659064773675588927379781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140424172729801570473012749 52659064773675588927379781)
      ·
        refine ⟨9873574645064172923883709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52659064773675588927379781 9873574645064172923883709)
        ·
          refine ⟨3702590491899064846456391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9873574645064172923883709 3702590491899064846456391)
          ·
            refine ⟨5553885737848597269684587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702590491899064846456391 5553885737848597269684587)
            ·
              refine ⟨8330828606772895904526881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553885737848597269684587 8330828606772895904526881)
              ·
                refine ⟨6248121455079671928395161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8330828606772895904526881 6248121455079671928395161)
                ·
                  refine ⟨4686091091309753946296371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6248121455079671928395161 4686091091309753946296371)
                  ·
                    refine ⟨7029136636964630919444557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4686091091309753946296371 7029136636964630919444557)
                    ·
                      refine ⟨2635926238861736594791709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7029136636964630919444557 2635926238861736594791709)
                      ·
                        rfl

theorem cell23_5133448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_5133448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133448 prefixEnd_5133448 := by exact prefixLift 5133448
  have htrace : WordTrace (prefixWord ++ tailWord_5133448) baseStart_5133448 baseEnd_5133448 := by
    simpa [prefixWord, tailWord_5133448, baseEnd_5133448] using wordTrace_append hprefix tailTrace_5133448
  have hstable : (prefixWord ++ tailWord_5133448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133448).length < 2 ^ (prefixWord ++ tailWord_5133448).sum := by decide
  have hdescent : baseEnd_5133448 < baseStart_5133448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133450 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5133450 : Nat := 118140960795 + 5133450 * 2 ^ 59
def prefixEnd_5133450 : Nat := 4983230072969 + 3 ^ 40 * 5133450 * 2
def baseEnd_5133450 : Nat := 2635927265823045586966699

theorem tailTrace_5133450 : CollatzResearch.WordTrace tailWord_5133450 prefixEnd_5133450 2635927265823045586966699 := by
  unfold tailWord_5133450
  simp only [CollatzResearch.WordTrace]
  refine ⟨46808075813098712076397451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124821535501596565537059869 46808075813098712076397451)
  ·
    refine ⟨70212113719648068114596177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46808075813098712076397451 70212113719648068114596177)
    ·
      refine ⟨52659085289736051085947133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70212113719648068114596177 52659085289736051085947133)
      ·
        refine ⟨19747156983651019157230175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52659085289736051085947133 19747156983651019157230175)
        ·
          refine ⟨29620735475476528735845263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19747156983651019157230175 29620735475476528735845263)
          ·
            refine ⟨44431103213214793103767895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29620735475476528735845263 44431103213214793103767895)
            ·
              refine ⟨66646654819822189655651843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44431103213214793103767895 66646654819822189655651843)
              ·
                refine ⟨99969982229733284483477765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66646654819822189655651843 99969982229733284483477765)
                ·
                  refine ⟨18744371668074990840652081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99969982229733284483477765 18744371668074990840652081)
                  ·
                    refine ⟨14058278751056243130489061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18744371668074990840652081 14058278751056243130489061)
                    ·
                      refine ⟨2635927265823045586966699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14058278751056243130489061 2635927265823045586966699)
                      ·
                        rfl

theorem cell23_5133450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5133450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133450 prefixEnd_5133450 := by exact prefixLift 5133450
  have htrace : WordTrace (prefixWord ++ tailWord_5133450) baseStart_5133450 baseEnd_5133450 := by
    simpa [prefixWord, tailWord_5133450, baseEnd_5133450] using wordTrace_append hprefix tailTrace_5133450
  have hstable : (prefixWord ++ tailWord_5133450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133450).length < 2 ^ (prefixWord ++ tailWord_5133450).sum := by decide
  have hdescent : baseEnd_5133450 < baseStart_5133450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133471 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5133471 : Nat := 118140960795 + 5133471 * 2 ^ 59
def prefixEnd_5133471 : Nat := 4983230072969 + 3 ^ 40 * 5133471 * 2
def baseEnd_5133471 : Nat := 2635938048916790004804103

theorem tailTrace_5133471 : CollatzResearch.WordTrace tailWord_5133471 prefixEnd_5133471 2635938048916790004804103 := by
  unfold tailWord_5133471
  simp only [CollatzResearch.WordTrace]
  refine ⟨187233069185318768892104267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124822046123545845928069511 187233069185318768892104267)
  ·
    refine ⟨280849603777978153338156401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187233069185318768892104267 280849603777978153338156401)
    ·
      refine ⟨210637202833483615003617301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280849603777978153338156401 210637202833483615003617301)
      ·
        refine ⟨9873618882819544453294561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 210637202833483615003617301 9873618882819544453294561)
        ·
          refine ⟨7405214162114658339970921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9873618882819544453294561 7405214162114658339970921)
          ·
            refine ⟨5553910621585993754978191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7405214162114658339970921 5553910621585993754978191)
            ·
              refine ⟨8330865932378990632467287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553910621585993754978191 8330865932378990632467287)
              ·
                refine ⟨12496298898568485948700931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8330865932378990632467287 12496298898568485948700931)
                ·
                  refine ⟨18744448347852728923051397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12496298898568485948700931 18744448347852728923051397)
                  ·
                    refine ⟨3514584065222386673072137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18744448347852728923051397 3514584065222386673072137)
                    ·
                      refine ⟨2635938048916790004804103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514584065222386673072137 2635938048916790004804103)
                      ·
                        rfl

theorem cell23_5133471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5133471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133471 prefixEnd_5133471 := by exact prefixLift 5133471
  have htrace : WordTrace (prefixWord ++ tailWord_5133471) baseStart_5133471 baseEnd_5133471 := by
    simpa [prefixWord, tailWord_5133471, baseEnd_5133471] using wordTrace_append hprefix tailTrace_5133471
  have hstable : (prefixWord ++ tailWord_5133471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133471).length < 2 ^ (prefixWord ++ tailWord_5133471).sum := by decide
  have hdescent : baseEnd_5133471 < baseStart_5133471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133490 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_5133490 : Nat := 118140960795 + 5133490 * 2 ^ 59
def prefixEnd_5133490 : Nat := 4983230072969 + 3 ^ 40 * 5133490 * 2
def baseEnd_5133490 : Nat := 878649268349741810155505

theorem tailTrace_5133490 : CollatzResearch.WordTrace tailWord_5133490 prefixEnd_5133490 878649268349741810155505 := by
  unfold tailWord_5133490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46808440543062483784261481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124822508114833290091363949 46808440543062483784261481)
  ·
    refine ⟨35106330407296862838196111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46808440543062483784261481 35106330407296862838196111)
    ·
      refine ⟨52659495610945294257294167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35106330407296862838196111 52659495610945294257294167)
      ·
        refine ⟨78989243416417941385941251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52659495610945294257294167 78989243416417941385941251)
        ·
          refine ⟨118483865124626912078911877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78989243416417941385941251 118483865124626912078911877)
          ·
            refine ⟨22215724710867546014795977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118483865124626912078911877 22215724710867546014795977)
            ·
              refine ⟨16661793533150659511096983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22215724710867546014795977 16661793533150659511096983)
              ·
                refine ⟨24992690299725989266645475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16661793533150659511096983 24992690299725989266645475)
                ·
                  refine ⟨37489035449588983899968213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24992690299725989266645475 37489035449588983899968213)
                  ·
                    refine ⟨878649268349741810155505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37489035449588983899968213 878649268349741810155505)
                    ·
                      rfl

theorem cell23_5133490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_5133490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133490 prefixEnd_5133490 := by exact prefixLift 5133490
  have htrace : WordTrace (prefixWord ++ tailWord_5133490) baseStart_5133490 baseEnd_5133490 := by
    simpa [prefixWord, tailWord_5133490, baseEnd_5133490] using wordTrace_append hprefix tailTrace_5133490
  have hstable : (prefixWord ++ tailWord_5133490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133490).length < 2 ^ (prefixWord ++ tailWord_5133490).sum := by decide
  have hdescent : baseEnd_5133490 < baseStart_5133490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133527 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 2, 4, 2]
def baseStart_5133527 : Nat := 118140960795 + 5133527 * 2 ^ 59
def prefixEnd_5133527 : Nat := 4983230072969 + 3 ^ 40 * 5133527 * 2
def baseEnd_5133527 : Nat := 2635966803833441785703845

theorem tailTrace_5133527 : CollatzResearch.WordTrace tailWord_5133527 prefixEnd_5133527 2635966803833441785703845 := by
  unfold tailWord_5133527
  simp only [CollatzResearch.WordTrace]
  refine ⟨187235111673115890456142835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124823407782077260304095223 187235111673115890456142835)
  ·
    refine ⟨280852667509673835684214253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187235111673115890456142835 280852667509673835684214253)
    ·
      refine ⟨105319750316127688381580345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280852667509673835684214253 105319750316127688381580345)
      ·
        refine ⟨78989812737095766286185259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105319750316127688381580345 78989812737095766286185259)
        ·
          refine ⟨118484719105643649429277889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78989812737095766286185259 118484719105643649429277889)
          ·
            refine ⟨88863539329232737071958417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118484719105643649429277889 88863539329232737071958417)
            ·
              refine ⟨66647654496924552803968813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88863539329232737071958417 66647654496924552803968813)
              ·
                refine ⟨24992870436346707301488305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66647654496924552803968813 24992870436346707301488305)
                ·
                  refine ⟨18744652827260030476116229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24992870436346707301488305 18744652827260030476116229)
                  ·
                    refine ⟨3514622405111255714271793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18744652827260030476116229 3514622405111255714271793)
                    ·
                      refine ⟨2635966803833441785703845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514622405111255714271793 2635966803833441785703845)
                      ·
                        rfl

theorem cell23_5133527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_5133527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133527 prefixEnd_5133527 := by exact prefixLift 5133527
  have htrace : WordTrace (prefixWord ++ tailWord_5133527) baseStart_5133527 baseEnd_5133527 := by
    simpa [prefixWord, tailWord_5133527, baseEnd_5133527] using wordTrace_append hprefix tailTrace_5133527
  have hstable : (prefixWord ++ tailWord_5133527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133527).length < 2 ^ (prefixWord ++ tailWord_5133527).sum := by decide
  have hdescent : baseEnd_5133527 < baseStart_5133527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133540 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_5133540 : Nat := 118140960795 + 5133540 * 2 ^ 59
def prefixEnd_5133540 : Nat := 4983230072969 + 3 ^ 40 * 5133540 * 2
def baseEnd_5133540 : Nat := 2635973479081950234841285

theorem tailTrace_5133540 : CollatzResearch.WordTrace tailWord_5133540 prefixEnd_5133540 2635973479081950234841285 := by
  unfold tailWord_5133540
  simp only [CollatzResearch.WordTrace]
  refine ⟨93617792911034396838183037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124823723881379195784244049 93617792911034396838183037)
  ·
    refine ⟨35106672341637898814318639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93617792911034396838183037 35106672341637898814318639)
    ·
      refine ⟨52660008512456848221477959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35106672341637898814318639 52660008512456848221477959)
      ·
        refine ⟨78990012768685272332216939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52660008512456848221477959 78990012768685272332216939)
        ·
          refine ⟨118485019153027908498325409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78990012768685272332216939 118485019153027908498325409)
          ·
            refine ⟨88863764364770931373744057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118485019153027908498325409 88863764364770931373744057)
            ·
              refine ⟨66647823273578198530308043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88863764364770931373744057 66647823273578198530308043)
              ·
                refine ⟨99971734910367297795462065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66647823273578198530308043 99971734910367297795462065)
                ·
                  refine ⟨74978801182775473346596549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99971734910367297795462065 74978801182775473346596549)
                  ·
                    refine ⟨14058525221770401252486853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74978801182775473346596549 14058525221770401252486853)
                    ·
                      refine ⟨2635973479081950234841285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14058525221770401252486853 2635973479081950234841285)
                      ·
                        rfl

theorem cell23_5133540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_5133540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133540 prefixEnd_5133540 := by exact prefixLift 5133540
  have htrace : WordTrace (prefixWord ++ tailWord_5133540) baseStart_5133540 baseEnd_5133540 := by
    simpa [prefixWord, tailWord_5133540, baseEnd_5133540] using wordTrace_append hprefix tailTrace_5133540
  have hstable : (prefixWord ++ tailWord_5133540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133540).length < 2 ^ (prefixWord ++ tailWord_5133540).sum := by decide
  have hdescent : baseEnd_5133540 < baseStart_5133540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133547 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 3]
def baseStart_5133547 : Nat := 118140960795 + 5133547 * 2 ^ 59
def prefixEnd_5133547 : Nat := 4983230072969 + 3 ^ 40 * 5133547 * 2
def baseEnd_5133547 : Nat := 2635977073446531707453753

theorem tailTrace_5133547 : CollatzResearch.WordTrace tailWord_5133547 prefixEnd_5133547 2635977073446531707453753 := by
  unfold tailWord_5133547
  simp only [CollatzResearch.WordTrace]
  refine ⟨187235841133043433871870895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124823894088695622581247263 187235841133043433871870895)
  ·
    refine ⟨280853761699565150807806343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187235841133043433871870895 280853761699565150807806343)
    ·
      refine ⟨421280642549347726211709515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280853761699565150807806343 421280642549347726211709515)
      ·
        refine ⟨631920963824021589317564273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421280642549347726211709515 631920963824021589317564273)
        ·
          refine ⟨473940722868016191988173205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631920963824021589317564273 473940722868016191988173205)
          ·
            refine ⟨22215971384438258999445619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 473940722868016191988173205 22215971384438258999445619)
            ·
              refine ⟨33323957076657388499168429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22215971384438258999445619 33323957076657388499168429)
              ·
                refine ⟨12496483903746520687188161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33323957076657388499168429 12496483903746520687188161)
                ·
                  refine ⟨9372362927809890515391121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12496483903746520687188161 9372362927809890515391121)
                  ·
                    refine ⟨7029272195857417886543341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9372362927809890515391121 7029272195857417886543341)
                    ·
                      refine ⟨2635977073446531707453753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7029272195857417886543341 2635977073446531707453753)
                      ·
                        rfl

theorem cell23_5133547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 3].length) (baseStart_5133547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133547 prefixEnd_5133547 := by exact prefixLift 5133547
  have htrace : WordTrace (prefixWord ++ tailWord_5133547) baseStart_5133547 baseEnd_5133547 := by
    simpa [prefixWord, tailWord_5133547, baseEnd_5133547] using wordTrace_append hprefix tailTrace_5133547
  have hstable : (prefixWord ++ tailWord_5133547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133547).length < 2 ^ (prefixWord ++ tailWord_5133547).sum := by decide
  have hdescent : baseEnd_5133547 < baseStart_5133547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133550 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_5133550 : Nat := 118140960795 + 5133550 * 2 ^ 59
def prefixEnd_5133550 : Nat := 4983230072969 + 3 ^ 40 * 5133550 * 2
def baseEnd_5133550 : Nat := 292886512654277243968471

theorem tailTrace_5133550 : CollatzResearch.WordTrace tailWord_5133550 prefixEnd_5133550 292886512654277243968471 := by
  unfold tailWord_5133550
  simp only [CollatzResearch.WordTrace]
  refine ⟨23404493819004070673028763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124823967034688376922820069 23404493819004070673028763)
  ·
    refine ⟨35106740728506106009543145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23404493819004070673028763 35106740728506106009543145)
    ·
      refine ⟨26330055546379579507157359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35106740728506106009543145 26330055546379579507157359)
      ·
        refine ⟨39495083319569369260736039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26330055546379579507157359 39495083319569369260736039)
        ·
          refine ⟨59242624979354053891104059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39495083319569369260736039 59242624979354053891104059)
          ·
            refine ⟨88863937469031080836656089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59242624979354053891104059 88863937469031080836656089)
            ·
              refine ⟨66647953101773310627492067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88863937469031080836656089 66647953101773310627492067)
              ·
                refine ⟨99971929652659965941238101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66647953101773310627492067 99971929652659965941238101)
                ·
                  refine ⟨292886512654277243968471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 99971929652659965941238101 292886512654277243968471)
                  ·
                    rfl

theorem cell23_5133550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_5133550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133550 prefixEnd_5133550 := by exact prefixLift 5133550
  have htrace : WordTrace (prefixWord ++ tailWord_5133550) baseStart_5133550 baseEnd_5133550 := by
    simpa [prefixWord, tailWord_5133550, baseEnd_5133550] using wordTrace_append hprefix tailTrace_5133550
  have hstable : (prefixWord ++ tailWord_5133550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133550).length < 2 ^ (prefixWord ++ tailWord_5133550).sum := by decide
  have hdescent : baseEnd_5133550 < baseStart_5133550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133567 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 6]
def baseStart_5133567 : Nat := 118140960795 + 5133567 * 2 ^ 59
def prefixEnd_5133567 : Nat := 4983230072969 + 3 ^ 40 * 5133567 * 2
def baseEnd_5133567 : Nat := 292887482562180181022629

theorem tailTrace_5133567 : CollatzResearch.WordTrace tailWord_5133567 prefixEnd_5133567 292887482562180181022629 := by
  unfold tailWord_5133567
  simp only [CollatzResearch.WordTrace]
  refine ⟨187236570592970977287598955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124824380395313984858399303 187236570592970977287598955)
  ·
    refine ⟨280854855889456465931398433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187236570592970977287598955 280854855889456465931398433)
    ·
      refine ⟨210641141917092349448548825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280854855889456465931398433 210641141917092349448548825)
      ·
        refine ⟨157980856437819262086411619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210641141917092349448548825 157980856437819262086411619)
        ·
          refine ⟨236971284656728893129617429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157980856437819262086411619 236971284656728893129617429)
          ·
            refine ⟨11108028968284166865450817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 236971284656728893129617429 11108028968284166865450817)
            ·
              refine ⟨8331021726213125149088113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11108028968284166865450817 8331021726213125149088113)
              ·
                refine ⟨6248266294659843861816085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8331021726213125149088113 6248266294659843861816085)
                ·
                  refine ⟨292887482562180181022629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6248266294659843861816085 292887482562180181022629)
                  ·
                    rfl

theorem cell23_5133567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 6].length) (baseStart_5133567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133567 prefixEnd_5133567 := by exact prefixLift 5133567
  have htrace : WordTrace (prefixWord ++ tailWord_5133567) baseStart_5133567 baseEnd_5133567 := by
    simpa [prefixWord, tailWord_5133567, baseEnd_5133567] using wordTrace_append hprefix tailTrace_5133567
  have hstable : (prefixWord ++ tailWord_5133567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133567).length < 2 ^ (prefixWord ++ tailWord_5133567).sum := by decide
  have hdescent : baseEnd_5133567 < baseStart_5133567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133571 : List Nat := [1, 1, 1, 3, 2, 4, 4, 2, 1, 4]
def baseStart_5133571 : Nat := 118140960795 + 5133571 * 2 ^ 59
def prefixEnd_5133571 : Nat := 4983230072969 + 3 ^ 40 * 5133571 * 2
def baseEnd_5133571 : Nat := 878663132327413204517881

theorem tailTrace_5133571 : CollatzResearch.WordTrace tailWord_5133571 prefixEnd_5133571 878663132327413204517881 := by
  unfold tailWord_5133571
  simp only [CollatzResearch.WordTrace]
  refine ⟨187236716484956485970744567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124824477656637657313829711 187236716484956485970744567)
  ·
    refine ⟨280855074727434728956116851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187236716484956485970744567 280855074727434728956116851)
    ·
      refine ⟨421282612091152093434175277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280855074727434728956116851 421282612091152093434175277)
      ·
        refine ⟨157980979534182035037815729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421282612091152093434175277 157980979534182035037815729)
        ·
          refine ⟨118485734650636526278361797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157980979534182035037815729 118485734650636526278361797)
          ·
            refine ⟨22216075246994348677192837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118485734650636526278361797 22216075246994348677192837)
            ·
              refine ⟨4165514108811440376973657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22216075246994348677192837 4165514108811440376973657)
              ·
                refine ⟨3124135581608580282730243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4165514108811440376973657 3124135581608580282730243)
                ·
                  refine ⟨4686203372412870424095365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124135581608580282730243 4686203372412870424095365)
                  ·
                    refine ⟨878663132327413204517881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4686203372412870424095365 878663132327413204517881)
                    ·
                      rfl

theorem cell23_5133571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 4].length) (baseStart_5133571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133571 prefixEnd_5133571 := by exact prefixLift 5133571
  have htrace : WordTrace (prefixWord ++ tailWord_5133571) baseStart_5133571 baseEnd_5133571 := by
    simpa [prefixWord, tailWord_5133571, baseEnd_5133571] using wordTrace_append hprefix tailTrace_5133571
  have hstable : (prefixWord ++ tailWord_5133571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133571).length < 2 ^ (prefixWord ++ tailWord_5133571).sum := by decide
  have hdescent : baseEnd_5133571 < baseStart_5133571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133594 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3]
def baseStart_5133594 : Nat := 118140960795 + 5133594 * 2 ^ 59
def prefixEnd_5133594 : Nat := 4983230072969 + 3 ^ 40 * 5133594 * 2
def baseEnd_5133594 : Nat := 2636001207037293023566037

theorem tailTrace_5133594 : CollatzResearch.WordTrace tailWord_5133594 prefixEnd_5133594 2636001207037293023566037 := by
  unfold tailWord_5133594
  simp only [CollatzResearch.WordTrace]
  refine ⟨46809388840968290224707959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124825036909248773932554557 46809388840968290224707959)
  ·
    refine ⟨70214083261452435337061939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46809388840968290224707959 70214083261452435337061939)
    ·
      refine ⟨105321124892178653005592909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70214083261452435337061939 105321124892178653005592909)
      ·
        refine ⟨39495421834566994877097341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105321124892178653005592909 39495421834566994877097341)
        ·
          refine ⟨14810783187962623078911503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39495421834566994877097341 14810783187962623078911503)
          ·
            refine ⟨22216174781943934618367255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14810783187962623078911503 22216174781943934618367255)
            ·
              refine ⟨33324262172915901927550883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22216174781943934618367255 33324262172915901927550883)
              ·
                refine ⟨49986393259373852891326325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33324262172915901927550883 49986393259373852891326325)
                ·
                  refine ⟨4686224368066298708561843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49986393259373852891326325 4686224368066298708561843)
                  ·
                    refine ⟨7029336552099448062842765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4686224368066298708561843 7029336552099448062842765)
                    ·
                      refine ⟨2636001207037293023566037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7029336552099448062842765 2636001207037293023566037)
                      ·
                        rfl

theorem cell23_5133594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_5133594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133594 prefixEnd_5133594 := by exact prefixLift 5133594
  have htrace : WordTrace (prefixWord ++ tailWord_5133594) baseStart_5133594 baseEnd_5133594 := by
    simpa [prefixWord, tailWord_5133594, baseEnd_5133594] using wordTrace_append hprefix tailTrace_5133594
  have hstable : (prefixWord ++ tailWord_5133594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133594).length < 2 ^ (prefixWord ++ tailWord_5133594).sum := by decide
  have hdescent : baseEnd_5133594 < baseStart_5133594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133604 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_5133604 : Nat := 118140960795 + 5133604 * 2 ^ 59
def prefixEnd_5133604 : Nat := 4983230072969 + 3 ^ 40 * 5133604 * 2
def baseEnd_5133604 : Nat := 2636006341843837984440991

theorem tailTrace_5133604 : CollatzResearch.WordTrace tailWord_5133604 prefixEnd_5133604 2636006341843837984440991 := by
  unfold tailWord_5133604
  simp only [CollatzResearch.WordTrace]
  refine ⟨93618960046918466303347933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124825280062557955071130577 93618960046918466303347933)
  ·
    refine ⟨35107110017594424863755475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93618960046918466303347933 35107110017594424863755475)
    ·
      refine ⟨52660665026391637295633213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35107110017594424863755475 52660665026391637295633213)
      ·
        refine ⟨19747749384896863985862455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52660665026391637295633213 19747749384896863985862455)
        ·
          refine ⟨29621624077345295978793683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19747749384896863985862455 29621624077345295978793683)
          ·
            refine ⟨44432436116017943968190525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29621624077345295978793683 44432436116017943968190525)
            ·
              refine ⟨16662163543506728988071447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44432436116017943968190525 16662163543506728988071447)
              ·
                refine ⟨24993245315260093482107171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16662163543506728988071447 24993245315260093482107171)
                ·
                  refine ⟨37489867972890140223160757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24993245315260093482107171 37489867972890140223160757)
                  ·
                    refine ⟨3514675122458450645921321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37489867972890140223160757 3514675122458450645921321)
                    ·
                      refine ⟨2636006341843837984440991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514675122458450645921321 2636006341843837984440991)
                      ·
                        rfl

theorem cell23_5133604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_5133604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133604 prefixEnd_5133604 := by exact prefixLift 5133604
  have htrace : WordTrace (prefixWord ++ tailWord_5133604) baseStart_5133604 baseEnd_5133604 := by
    simpa [prefixWord, tailWord_5133604, baseEnd_5133604] using wordTrace_append hprefix tailTrace_5133604
  have hstable : (prefixWord ++ tailWord_5133604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133604).length < 2 ^ (prefixWord ++ tailWord_5133604).sum := by decide
  have hdescent : baseEnd_5133604 < baseStart_5133604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133637 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_5133637 : Nat := 118140960795 + 5133637 * 2 ^ 59
def prefixEnd_5133637 : Nat := 4983230072969 + 3 ^ 40 * 5133637 * 2
def baseEnd_5133637 : Nat := 2636023286705436355328339

theorem tailTrace_5133637 : CollatzResearch.WordTrace tailWord_5133637 prefixEnd_5133637 2636023286705436355328339 := by
  unfold tailWord_5133637
  simp only [CollatzResearch.WordTrace]
  refine ⟨187239123702717379242647165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124826082468478252828431443 187239123702717379242647165)
  ·
    refine ⟨70214671388519017215992687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187239123702717379242647165 70214671388519017215992687)
    ·
      refine ⟨105322007082778525823989031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70214671388519017215992687 105322007082778525823989031)
      ·
        refine ⟨157983010624167788735983547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105322007082778525823989031 157983010624167788735983547)
        ·
          refine ⟨236974515936251683103975321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157983010624167788735983547 236974515936251683103975321)
          ·
            refine ⟨177730886952188762327981491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236974515936251683103975321 177730886952188762327981491)
            ·
              refine ⟨266596330428283143491972237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177730886952188762327981491 266596330428283143491972237)
              ·
                refine ⟨99973623910606178809489589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266596330428283143491972237 99973623910606178809489589)
                ·
                  refine ⟨9372527241619329263389649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99973623910606178809489589 9372527241619329263389649)
                  ·
                    refine ⟨7029395431214496947542237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9372527241619329263389649 7029395431214496947542237)
                    ·
                      refine ⟨2636023286705436355328339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7029395431214496947542237 2636023286705436355328339)
                      ·
                        rfl

theorem cell23_5133637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_5133637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133637 prefixEnd_5133637 := by exact prefixLift 5133637
  have htrace : WordTrace (prefixWord ++ tailWord_5133637) baseStart_5133637 baseEnd_5133637 := by
    simpa [prefixWord, tailWord_5133637, baseEnd_5133637] using wordTrace_append hprefix tailTrace_5133637
  have hstable : (prefixWord ++ tailWord_5133637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133637).length < 2 ^ (prefixWord ++ tailWord_5133637).sum := by decide
  have hdescent : baseEnd_5133637 < baseStart_5133637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133640 : List Nat := [2, 1, 3, 1, 1, 2, 1, 12]
def baseStart_5133640 : Nat := 118140960795 + 5133640 * 2 ^ 59
def prefixEnd_5133640 : Nat := 4983230072969 + 3 ^ 40 * 5133640 * 2
def baseEnd_5133640 : Nat := 97630549153607401614475

theorem tailTrace_5133640 : CollatzResearch.WordTrace tailWord_5133640 prefixEnd_5133640 97630549153607401614475 := by
  unfold tailWord_5133640
  simp only [CollatzResearch.WordTrace]
  refine ⟨93619616560853255377503187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124826155414471007170004249 93619616560853255377503187)
  ·
    refine ⟨140429424841279883066254781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93619616560853255377503187 140429424841279883066254781)
    ·
      refine ⟨52661034315479956149845543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140429424841279883066254781 52661034315479956149845543)
      ·
        refine ⟨78991551473219934224768315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52661034315479956149845543 78991551473219934224768315)
        ·
          refine ⟨118487327209829901337152473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78991551473219934224768315 118487327209829901337152473)
          ·
            refine ⟨88865495407372426002864355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118487327209829901337152473 88865495407372426002864355)
            ·
              refine ⟨133298243111058639004296533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88865495407372426002864355 133298243111058639004296533)
              ·
                refine ⟨97630549153607401614475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 133298243111058639004296533 97630549153607401614475)
                ·
                  rfl

theorem cell23_5133640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 12].length) (baseStart_5133640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133640 prefixEnd_5133640 := by exact prefixLift 5133640
  have htrace : WordTrace (prefixWord ++ tailWord_5133640) baseStart_5133640 baseEnd_5133640 := by
    simpa [prefixWord, tailWord_5133640, baseEnd_5133640] using wordTrace_append hprefix tailTrace_5133640
  have hstable : (prefixWord ++ tailWord_5133640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133640).length < 2 ^ (prefixWord ++ tailWord_5133640).sum := by decide
  have hdescent : baseEnd_5133640 < baseStart_5133640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133644 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_5133644 : Nat := 118140960795 + 5133644 * 2 ^ 59
def prefixEnd_5133644 : Nat := 4983230072969 + 3 ^ 40 * 5133644 * 2
def baseEnd_5133644 : Nat := 878675627023339275980269

theorem tailTrace_5133644 : CollatzResearch.WordTrace tailWord_5133644 prefixEnd_5133644 878675627023339275980269 := by
  unfold tailWord_5133644
  simp only [CollatzResearch.WordTrace]
  refine ⟨93619689506846009719075993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124826252675794679625434657 93619689506846009719075993)
  ·
    refine ⟨70214767130134507289306995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93619689506846009719075993 70214767130134507289306995)
    ·
      refine ⟨105322150695201760933960493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70214767130134507289306995 105322150695201760933960493)
      ·
        refine ⟨39495806510700660350235185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105322150695201760933960493 39495806510700660350235185)
        ·
          refine ⟨29621854883025495262676389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39495806510700660350235185 29621854883025495262676389)
          ·
            refine ⟨5554097790567280361751823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29621854883025495262676389 5554097790567280361751823)
            ·
              refine ⟨8331146685850920542627735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554097790567280361751823 8331146685850920542627735)
              ·
                refine ⟨12496720028776380813941603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8331146685850920542627735 12496720028776380813941603)
                ·
                  refine ⟨18745080043164571220912405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12496720028776380813941603 18745080043164571220912405)
                  ·
                    refine ⟨878675627023339275980269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18745080043164571220912405 878675627023339275980269)
                    ·
                      rfl

theorem cell23_5133644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_5133644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133644 prefixEnd_5133644 := by exact prefixLift 5133644
  have htrace : WordTrace (prefixWord ++ tailWord_5133644) baseStart_5133644 baseEnd_5133644 := by
    simpa [prefixWord, tailWord_5133644, baseEnd_5133644] using wordTrace_append hprefix tailTrace_5133644
  have hstable : (prefixWord ++ tailWord_5133644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133644).length < 2 ^ (prefixWord ++ tailWord_5133644).sum := by decide
  have hdescent : baseEnd_5133644 < baseStart_5133644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133657 : List Nat := [1, 2, 1, 2, 2, 2, 6, 7]
def baseStart_5133657 : Nat := 118140960795 + 5133657 * 2 ^ 59
def prefixEnd_5133657 : Nat := 4983230072969 + 3 ^ 40 * 5133657 * 2
def baseEnd_5133657 : Nat := 97630872456241713965861

theorem tailTrace_5133657 : CollatzResearch.WordTrace tailWord_5133657 prefixEnd_5133657 97630872456241713965861 := by
  unfold tailWord_5133657
  simp only [CollatzResearch.WordTrace]
  refine ⟨187239853162644922658375225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124826568775096615105583483 187239853162644922658375225)
  ·
    refine ⟨140429889871983691993781419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187239853162644922658375225 140429889871983691993781419)
    ·
      refine ⟨210644834807975537990672129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140429889871983691993781419 210644834807975537990672129)
      ·
        refine ⟨157983626105981653493004097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210644834807975537990672129 157983626105981653493004097)
        ·
          refine ⟨118487719579486240119753073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157983626105981653493004097 118487719579486240119753073)
          ·
            refine ⟨88865789684614680089814805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118487719579486240119753073 88865789684614680089814805)
            ·
              refine ⟨4165583891466313129210069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88865789684614680089814805 4165583891466313129210069)
              ·
                refine ⟨97630872456241713965861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4165583891466313129210069 97630872456241713965861)
                ·
                  rfl

theorem cell23_5133657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 7].length) (baseStart_5133657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133657 prefixEnd_5133657 := by exact prefixLift 5133657
  have htrace : WordTrace (prefixWord ++ tailWord_5133657) baseStart_5133657 baseEnd_5133657 := by
    simpa [prefixWord, tailWord_5133657, baseEnd_5133657] using wordTrace_append hprefix tailTrace_5133657
  have hstable : (prefixWord ++ tailWord_5133657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133657).length < 2 ^ (prefixWord ++ tailWord_5133657).sum := by decide
  have hdescent : baseEnd_5133657 < baseStart_5133657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133674 : List Nat := [3, 1, 3, 3, 2, 2, 9]
def baseStart_5133674 : Nat := 118140960795 + 5133674 * 2 ^ 59
def prefixEnd_5133674 : Nat := 4983230072969 + 3 ^ 40 * 5133674 * 2
def baseEnd_5133674 : Nat := 32543731919625342105749

theorem tailTrace_5133674 : CollatzResearch.WordTrace tailWord_5133674 prefixEnd_5133674 32543731919625342105749 := by
  unfold tailWord_5133674
  simp only [CollatzResearch.WordTrace]
  refine ⟨46810118300895833640436019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124826982135722223041162717 46810118300895833640436019)
  ·
    refine ⟨70215177451343750460654029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46810118300895833640436019 70215177451343750460654029)
    ·
      refine ⟨26330691544253906422745261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70215177451343750460654029 26330691544253906422745261)
      ·
        refine ⟨9874009329095214908529473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26330691544253906422745261 9874009329095214908529473)
        ·
          refine ⟨7405506996821411181397105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9874009329095214908529473 7405506996821411181397105)
          ·
            refine ⟨5554130247616058386047829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7405506996821411181397105 5554130247616058386047829)
            ·
              refine ⟨32543731919625342105749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5554130247616058386047829 32543731919625342105749)
              ·
                rfl

theorem cell23_5133674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 9].length) (baseStart_5133674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133674 prefixEnd_5133674 := by exact prefixLift 5133674
  have htrace : WordTrace (prefixWord ++ tailWord_5133674) baseStart_5133674 baseEnd_5133674 := by
    simpa [prefixWord, tailWord_5133674, baseEnd_5133674] using wordTrace_append hprefix tailTrace_5133674
  have hstable : (prefixWord ++ tailWord_5133674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133674).length < 2 ^ (prefixWord ++ tailWord_5133674).sum := by decide
  have hdescent : baseEnd_5133674 < baseStart_5133674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133685 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_5133685 : Nat := 118140960795 + 5133685 * 2 ^ 59
def prefixEnd_5133685 : Nat := 4983230072969 + 3 ^ 40 * 5133685 * 2
def baseEnd_5133685 : Nat := 2636047933776852167528119

theorem tailTrace_5133685 : CollatzResearch.WordTrace tailWord_5133685 prefixEnd_5133685 2636047933776852167528119 := by
  unfold tailWord_5133685
  simp only [CollatzResearch.WordTrace]
  refine ⟨187240874406543483440394509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124827249604362322293596339 187240874406543483440394509)
  ·
    refine ⟨70215327902453806290147941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187240874406543483440394509 70215327902453806290147941)
    ·
      refine ⟨13165373981710088679402739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70215327902453806290147941 13165373981710088679402739)
      ·
        refine ⟨19748060972565133019104109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13165373981710088679402739 19748060972565133019104109)
        ·
          refine ⟨7405522864711924882164041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19748060972565133019104109 7405522864711924882164041)
          ·
            refine ⟨5554142148533943661623031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7405522864711924882164041 5554142148533943661623031)
            ·
              refine ⟨8331213222800915492434547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554142148533943661623031 8331213222800915492434547)
              ·
                refine ⟨12496819834201373238651821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8331213222800915492434547 12496819834201373238651821)
                ·
                  refine ⟨4686307437825514964494433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12496819834201373238651821 4686307437825514964494433)
                  ·
                    refine ⟨3514730578369136223370825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4686307437825514964494433 3514730578369136223370825)
                    ·
                      refine ⟨2636047933776852167528119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514730578369136223370825 2636047933776852167528119)
                      ·
                        rfl

theorem cell23_5133685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_5133685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133685 prefixEnd_5133685 := by exact prefixLift 5133685
  have htrace : WordTrace (prefixWord ++ tailWord_5133685) baseStart_5133685 baseEnd_5133685 := by
    simpa [prefixWord, tailWord_5133685, baseEnd_5133685] using wordTrace_append hprefix tailTrace_5133685
  have hstable : (prefixWord ++ tailWord_5133685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133685).length < 2 ^ (prefixWord ++ tailWord_5133685).sum := by decide
  have hdescent : baseEnd_5133685 < baseStart_5133685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133728 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 1, 3, 2]
def baseStart_5133728 : Nat := 118140960795 + 5133728 * 2 ^ 59
def prefixEnd_5133728 : Nat := 4983230072969 + 3 ^ 40 * 5133728 * 2
def baseEnd_5133728 : Nat := 2636070013444995499290421

theorem tailTrace_5133728 : CollatzResearch.WordTrace tailWord_5133728 prefixEnd_5133728 2636070013444995499290421 := by
  unfold tailWord_5133728
  simp only [CollatzResearch.WordTrace]
  refine ⟨93621221372693850892104919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124828295163591801189473225 93621221372693850892104919)
  ·
    refine ⟨140431832059040776338157379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93621221372693850892104919 140431832059040776338157379)
    ·
      refine ⟨210647748088561164507236069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140431832059040776338157379 210647748088561164507236069)
      ·
        refine ⟨39496452766605218345106763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210647748088561164507236069 39496452766605218345106763)
        ·
          refine ⟨59244679149907827517660145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39496452766605218345106763 59244679149907827517660145)
          ·
            refine ⟨44433509362430870638245109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59244679149907827517660145 44433509362430870638245109)
            ·
              refine ⟨4165641502727894122335479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44433509362430870638245109 4165641502727894122335479)
              ·
                refine ⟨6248462254091841183503219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165641502727894122335479 6248462254091841183503219)
                ·
                  refine ⟨9372693381137761775254829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6248462254091841183503219 9372693381137761775254829)
                  ·
                    refine ⟨3514760017926660665720561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9372693381137761775254829 3514760017926660665720561)
                    ·
                      refine ⟨2636070013444995499290421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514760017926660665720561 2636070013444995499290421)
                      ·
                        rfl

theorem cell23_5133728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_5133728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133728 prefixEnd_5133728 := by exact prefixLift 5133728
  have htrace : WordTrace (prefixWord ++ tailWord_5133728) baseStart_5133728 baseEnd_5133728 := by
    simpa [prefixWord, tailWord_5133728, baseEnd_5133728] using wordTrace_append hprefix tailTrace_5133728
  have hstable : (prefixWord ++ tailWord_5133728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133728).length < 2 ^ (prefixWord ++ tailWord_5133728).sum := by decide
  have hdescent : baseEnd_5133728 < baseStart_5133728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133736 : List Nat := [2, 1, 6, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5133736 : Nat := 118140960795 + 5133736 * 2 ^ 59
def prefixEnd_5133736 : Nat := 4983230072969 + 3 ^ 40 * 5133736 * 2
def baseEnd_5133736 : Nat := 2636074121290231467990385

theorem tailTrace_5133736 : CollatzResearch.WordTrace tailWord_5133736 prefixEnd_5133736 2636074121290231467990385 := by
  unfold tailWord_5133736
  simp only [CollatzResearch.WordTrace]
  refine ⟨93621367264679359575250531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124828489686239146100334041 93621367264679359575250531)
  ·
    refine ⟨140432050897019039362875797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93621367264679359575250531 140432050897019039362875797)
    ·
      refine ⟨6582752385797767470134803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140432050897019039362875797 6582752385797767470134803)
      ·
        refine ⟨9874128578696651205202205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6582752385797767470134803 9874128578696651205202205)
        ·
          refine ⟨3702798217011244201950827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9874128578696651205202205 3702798217011244201950827)
          ·
            refine ⟨5554197325516866302926241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702798217011244201950827 5554197325516866302926241)
            ·
              refine ⟨4165647994137649727194681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5554197325516866302926241 4165647994137649727194681)
              ·
                refine ⟨3124235995603237295396011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4165647994137649727194681 3124235995603237295396011)
                ·
                  refine ⟨4686353993404855943094017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124235995603237295396011 4686353993404855943094017)
                  ·
                    refine ⟨3514765495053641957320513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4686353993404855943094017 3514765495053641957320513)
                    ·
                      refine ⟨2636074121290231467990385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514765495053641957320513 2636074121290231467990385)
                      ·
                        rfl

theorem cell23_5133736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5133736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133736 prefixEnd_5133736 := by exact prefixLift 5133736
  have htrace : WordTrace (prefixWord ++ tailWord_5133736) baseStart_5133736 baseEnd_5133736 := by
    simpa [prefixWord, tailWord_5133736, baseEnd_5133736] using wordTrace_append hprefix tailTrace_5133736
  have hstable : (prefixWord ++ tailWord_5133736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133736).length < 2 ^ (prefixWord ++ tailWord_5133736).sum := by decide
  have hdescent : baseEnd_5133736 < baseStart_5133736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133764 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 9]
def baseStart_5133764 : Nat := 118140960795 + 5133764 * 2 ^ 59
def prefixEnd_5133764 : Nat := 4983230072969 + 3 ^ 40 * 5133764 * 2
def baseEnd_5133764 : Nat := 292898722083173039826695

theorem tailTrace_5133764 : CollatzResearch.WordTrace tailWord_5133764 prefixEnd_5133764 292898722083173039826695 := by
  unfold tailWord_5133764
  simp only [CollatzResearch.WordTrace]
  refine ⟨93621877886628639966260173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124829170515504853288346897 93621877886628639966260173)
  ·
    refine ⟨35108204207485739987347565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93621877886628639966260173 35108204207485739987347565)
    ·
      refine ⟨13165576577807152495255337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35108204207485739987347565 13165576577807152495255337)
      ·
        refine ⟨9874182433355364371441503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13165576577807152495255337 9874182433355364371441503)
        ·
          refine ⟨14811273650033046557162255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9874182433355364371441503 14811273650033046557162255)
          ·
            refine ⟨22216910475049569835743383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14811273650033046557162255 22216910475049569835743383)
            ·
              refine ⟨33325365712574354753615075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22216910475049569835743383 33325365712574354753615075)
              ·
                refine ⟨49988048568861532130422613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33325365712574354753615075 49988048568861532130422613)
                ·
                  refine ⟨292898722083173039826695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49988048568861532130422613 292898722083173039826695)
                  ·
                    rfl

theorem cell23_5133764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_5133764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133764 prefixEnd_5133764 := by exact prefixLift 5133764
  have htrace : WordTrace (prefixWord ++ tailWord_5133764) baseStart_5133764 baseEnd_5133764 := by
    simpa [prefixWord, tailWord_5133764, baseEnd_5133764] using wordTrace_append hprefix tailTrace_5133764
  have hstable : (prefixWord ++ tailWord_5133764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133764).length < 2 ^ (prefixWord ++ tailWord_5133764).sum := by decide
  have hdescent : baseEnd_5133764 < baseStart_5133764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133781 : List Nat := [1, 3, 2, 3, 1, 1, 4, 3, 5]
def baseStart_5133781 : Nat := 118140960795 + 5133781 * 2 ^ 59
def prefixEnd_5133781 : Nat := 4983230072969 + 3 ^ 40 * 5133781 * 2
def baseEnd_5133781 : Nat := 292899691991075976880853

theorem tailTrace_5133781 : CollatzResearch.WordTrace tailWord_5133781 prefixEnd_5133781 292899691991075976880853 := by
  unfold tailWord_5133781
  simp only [CollatzResearch.WordTrace]
  refine ⟨187244375814195691835889197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124829583876130461223926131 187244375814195691835889197)
  ·
    refine ⟨70216640930323384438458449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187244375814195691835889197 70216640930323384438458449)
    ·
      refine ⟨52662480697742538328843837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70216640930323384438458449 52662480697742538328843837)
      ·
        refine ⟨19748430261653451873316439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52662480697742538328843837 19748430261653451873316439)
        ·
          refine ⟨29622645392480177809974659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19748430261653451873316439 29622645392480177809974659)
          ·
            refine ⟨44433968088720266714961989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29622645392480177809974659 44433968088720266714961989)
            ·
              refine ⟨8331369016635050009055373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44433968088720266714961989 8331369016635050009055373)
              ·
                refine ⟨3124263381238143753395765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8331369016635050009055373 3124263381238143753395765)
                ·
                  refine ⟨292899691991075976880853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3124263381238143753395765 292899691991075976880853)
                  ·
                    rfl

theorem cell23_5133781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_5133781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133781 prefixEnd_5133781 := by exact prefixLift 5133781
  have htrace : WordTrace (prefixWord ++ tailWord_5133781) baseStart_5133781 baseEnd_5133781 := by
    simpa [prefixWord, tailWord_5133781, baseEnd_5133781] using wordTrace_append hprefix tailTrace_5133781
  have hstable : (prefixWord ++ tailWord_5133781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133781).length < 2 ^ (prefixWord ++ tailWord_5133781).sum := by decide
  have hdescent : baseEnd_5133781 < baseStart_5133781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133827 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 6]
def baseStart_5133827 : Nat := 118140960795 + 5133827 * 2 ^ 59
def prefixEnd_5133827 : Nat := 4983230072969 + 3 ^ 40 * 5133827 * 2
def baseEnd_5133827 : Nat := 2636120848029790611952465

theorem tailTrace_5133827 : CollatzResearch.WordTrace tailWord_5133827 prefixEnd_5133827 2636120848029790611952465 := by
  unfold tailWord_5133827
  simp only [CollatzResearch.WordTrace]
  refine ⟨187246053572029041692063735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124830702381352694461375823 187246053572029041692063735)
  ·
    refine ⟨280869080358043562538095603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187246053572029041692063735 280869080358043562538095603)
    ·
      refine ⟨421303620537065343807143405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280869080358043562538095603 421303620537065343807143405)
      ·
        refine ⟨157988857701399503927678777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421303620537065343807143405 157988857701399503927678777)
        ·
          refine ⟨118491643276049627945759083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157988857701399503927678777 118491643276049627945759083)
          ·
            refine ⟨177737464914074441918638625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118491643276049627945759083 177737464914074441918638625)
            ·
              refine ⟨133303098685555831438978969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177737464914074441918638625 133303098685555831438978969)
              ·
                refine ⟨99977324014166873579234227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133303098685555831438978969 99977324014166873579234227)
                ·
                  refine ⟨149965986021250310368851341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99977324014166873579234227 149965986021250310368851341)
                  ·
                    refine ⟨56237244757968866388319253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149965986021250310368851341 56237244757968866388319253)
                    ·
                      refine ⟨2636120848029790611952465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56237244757968866388319253 2636120848029790611952465)
                      ·
                        rfl

theorem cell23_5133827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_5133827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133827 prefixEnd_5133827 := by exact prefixLift 5133827
  have htrace : WordTrace (prefixWord ++ tailWord_5133827) baseStart_5133827 baseEnd_5133827 := by
    simpa [prefixWord, tailWord_5133827, baseEnd_5133827] using wordTrace_append hprefix tailTrace_5133827
  have hstable : (prefixWord ++ tailWord_5133827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133827).length < 2 ^ (prefixWord ++ tailWord_5133827).sum := by decide
  have hdescent : baseEnd_5133827 < baseStart_5133827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133858 : List Nat := [3, 3, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_5133858 : Nat := 118140960795 + 5133858 * 2 ^ 59
def prefixEnd_5133858 : Nat := 4983230072969 + 3 ^ 40 * 5133858 * 2
def baseEnd_5133858 : Nat := 878712255310026663554941

theorem tailTrace_5133858 : CollatzResearch.WordTrace tailWord_5133858 prefixEnd_5133858 878712255310026663554941 := by
  unfold tailWord_5133858
  simp only [CollatzResearch.WordTrace]
  refine ⟨46811796058729183496610557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124831456156611155990961485 46811796058729183496610557)
  ·
    refine ⟨17554423522023443811228959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46811796058729183496610557 17554423522023443811228959)
    ·
      refine ⟨26331635283035165716843439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17554423522023443811228959 26331635283035165716843439)
      ·
        refine ⟨39497452924552748575265159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26331635283035165716843439 39497452924552748575265159)
        ·
          refine ⟨59246179386829122862897739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39497452924552748575265159 59246179386829122862897739)
          ·
            refine ⟨88869269080243684294346609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59246179386829122862897739 88869269080243684294346609)
            ·
              refine ⟨66651951810182763220759957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88869269080243684294346609 66651951810182763220759957)
              ·
                refine ⟨3124310241102317025973123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66651951810182763220759957 3124310241102317025973123)
                ·
                  refine ⟨4686465361653475538959685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124310241102317025973123 4686465361653475538959685)
                  ·
                    refine ⟨878712255310026663554941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4686465361653475538959685 878712255310026663554941)
                    ·
                      rfl

theorem cell23_5133858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_5133858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133858 prefixEnd_5133858 := by exact prefixLift 5133858
  have htrace : WordTrace (prefixWord ++ tailWord_5133858) baseStart_5133858 baseEnd_5133858 := by
    simpa [prefixWord, tailWord_5133858, baseEnd_5133858] using wordTrace_append hprefix tailTrace_5133858
  have hstable : (prefixWord ++ tailWord_5133858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133858).length < 2 ^ (prefixWord ++ tailWord_5133858).sum := by decide
  have hdescent : baseEnd_5133858 < baseStart_5133858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133867 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 11]
def baseStart_5133867 : Nat := 118140960795 + 5133867 * 2 ^ 59
def prefixEnd_5133867 : Nat := 4983230072969 + 3 ^ 40 * 5133867 * 2
def baseEnd_5133867 : Nat := 878713795751990151817427

theorem tailTrace_5133867 : CollatzResearch.WordTrace tailWord_5133867 prefixEnd_5133867 878713795751990151817427 := by
  unfold tailWord_5133867
  simp only [CollatzResearch.WordTrace]
  refine ⟨187247512491884128523519855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124831674994589419015679903 187247512491884128523519855)
  ·
    refine ⟨280871268737826192785279783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187247512491884128523519855 280871268737826192785279783)
    ·
      refine ⟨421306903106739289177919675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280871268737826192785279783 421306903106739289177919675)
      ·
        refine ⟨631960354660108933766879513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421306903106739289177919675 631960354660108933766879513)
        ·
          refine ⟨473970265995081700325159635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631960354660108933766879513 473970265995081700325159635)
          ·
            refine ⟨710955398992622550487739453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473970265995081700325159635 710955398992622550487739453)
            ·
              refine ⟨266608274622233456432902295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 710955398992622550487739453 266608274622233456432902295)
              ·
                refine ⟨399912411933350184649353443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266608274622233456432902295 399912411933350184649353443)
                ·
                  refine ⟨599868617900025276974030165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399912411933350184649353443 599868617900025276974030165)
                  ·
                    refine ⟨878713795751990151817427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 599868617900025276974030165 878713795751990151817427)
                    ·
                      rfl

theorem cell23_5133867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 11].length) (baseStart_5133867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133867 prefixEnd_5133867 := by exact prefixLift 5133867
  have htrace : WordTrace (prefixWord ++ tailWord_5133867) baseStart_5133867 baseEnd_5133867 := by
    simpa [prefixWord, tailWord_5133867, baseEnd_5133867] using wordTrace_append hprefix tailTrace_5133867
  have hstable : (prefixWord ++ tailWord_5133867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133867).length < 2 ^ (prefixWord ++ tailWord_5133867).sum := by decide
  have hdescent : baseEnd_5133867 < baseStart_5133867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133908 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_5133908 : Nat := 118140960795 + 5133908 * 2 ^ 59
def prefixEnd_5133908 : Nat := 4983230072969 + 3 ^ 40 * 5133908 * 2
def baseEnd_5133908 : Nat := 2636162439962804795039593

theorem tailTrace_5133908 : CollatzResearch.WordTrace tailWord_5133908 prefixEnd_5133908 2636162439962804795039593 := by
  unfold tailWord_5133908
  simp only [CollatzResearch.WordTrace]
  refine ⟨93624503942367796262881189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124832671923157061683841585 93624503942367796262881189)
  ·
    refine ⟨17554594489193961799290223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93624503942367796262881189 17554594489193961799290223)
    ·
      refine ⟨26331891733790942698935335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17554594489193961799290223 26331891733790942698935335)
      ·
        refine ⟨39497837600686414048403003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26331891733790942698935335 39497837600686414048403003)
        ·
          refine ⟨59246756401029621072604505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39497837600686414048403003 59246756401029621072604505)
          ·
            refine ⟨44435067300772215804453379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59246756401029621072604505 44435067300772215804453379)
            ·
              refine ⟨66652600951158323706680069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44435067300772215804453379 66652600951158323706680069)
              ·
                refine ⟨12497362678342185695002513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66652600951158323706680069 12497362678342185695002513)
                ·
                  refine ⟨9373022008756639271251885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12497362678342185695002513 9373022008756639271251885)
                  ·
                    refine ⟨3514883253283739726719457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9373022008756639271251885 3514883253283739726719457)
                    ·
                      refine ⟨2636162439962804795039593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514883253283739726719457 2636162439962804795039593)
                      ·
                        rfl

theorem cell23_5133908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_5133908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133908 prefixEnd_5133908 := by exact prefixLift 5133908
  have htrace : WordTrace (prefixWord ++ tailWord_5133908) baseStart_5133908 baseEnd_5133908 := by
    simpa [prefixWord, tailWord_5133908, baseEnd_5133908] using wordTrace_append hprefix tailTrace_5133908
  have hstable : (prefixWord ++ tailWord_5133908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133908).length < 2 ^ (prefixWord ++ tailWord_5133908).sum := by decide
  have hdescent : baseEnd_5133908 < baseStart_5133908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133942 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_5133942 : Nat := 118140960795 + 5133942 * 2 ^ 59
def prefixEnd_5133942 : Nat := 4983230072969 + 3 ^ 40 * 5133942 * 2
def baseEnd_5133942 : Nat := 2636179898305057662014437

theorem tailTrace_5133942 : CollatzResearch.WordTrace tailWord_5133942 prefixEnd_5133942 2636179898305057662014437 := by
  unfold tailWord_5133942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11703140497913276020781255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124833498644408277555000053 11703140497913276020781255)
  ·
    refine ⟨17554710746869914031171883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11703140497913276020781255 17554710746869914031171883)
    ·
      refine ⟨26332066120304871046757825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17554710746869914031171883 26332066120304871046757825)
      ·
        refine ⟨19749049590228653285068369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26332066120304871046757825 19749049590228653285068369)
        ·
          refine ⟨14811787192671489963801277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19749049590228653285068369 14811787192671489963801277)
          ·
            refine ⟨5554420197251808736425479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14811787192671489963801277 5554420197251808736425479)
            ·
              refine ⟨8331630295877713104638219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554420197251808736425479 8331630295877713104638219)
              ·
                refine ⟨12497445443816569656957329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8331630295877713104638219 12497445443816569656957329)
                ·
                  refine ⟨9373084082862427242717997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12497445443816569656957329 9373084082862427242717997)
                  ·
                    refine ⟨3514906531073410216019249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9373084082862427242717997 3514906531073410216019249)
                    ·
                      refine ⟨2636179898305057662014437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514906531073410216019249 2636179898305057662014437)
                      ·
                        rfl

theorem cell23_5133942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_5133942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133942 prefixEnd_5133942 := by exact prefixLift 5133942
  have htrace : WordTrace (prefixWord ++ tailWord_5133942) baseStart_5133942 baseEnd_5133942 := by
    simpa [prefixWord, tailWord_5133942, baseEnd_5133942] using wordTrace_append hprefix tailTrace_5133942
  have hstable : (prefixWord ++ tailWord_5133942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133942).length < 2 ^ (prefixWord ++ tailWord_5133942).sum := by decide
  have hdescent : baseEnd_5133942 < baseStart_5133942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133982 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5133982 : Nat := 118140960795 + 5133982 * 2 ^ 59
def prefixEnd_5133982 : Nat := 4983230072969 + 3 ^ 40 * 5133982 * 2
def baseEnd_5133982 : Nat := 878733479177079168504751

theorem tailTrace_5133982 : CollatzResearch.WordTrace tailWord_5133982 prefixEnd_5133982 878733479177079168504751 := by
  unfold tailWord_5133982
  simp only [CollatzResearch.WordTrace]
  refine ⟨23406463360808437895494525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124834471257645002109304133 23406463360808437895494525)
  ·
    refine ⟨8777423760303164210810447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23406463360808437895494525 8777423760303164210810447)
    ·
      refine ⟨13166135640454746316215671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8777423760303164210810447 13166135640454746316215671)
      ·
        refine ⟨19749203460682119474323507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13166135640454746316215671 19749203460682119474323507)
        ·
          refine ⟨29623805191023179211485261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19749203460682119474323507 29623805191023179211485261)
          ·
            refine ⟨11108926946633692204306973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29623805191023179211485261 11108926946633692204306973)
            ·
              refine ⟨4165847604987634576615115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11108926946633692204306973 4165847604987634576615115)
              ·
                refine ⟨6248771407481451864922673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165847604987634576615115 6248771407481451864922673)
                ·
                  refine ⟨4686578555611088898692005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6248771407481451864922673 4686578555611088898692005)
                  ·
                    refine ⟨878733479177079168504751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4686578555611088898692005 878733479177079168504751)
                    ·
                      rfl

theorem cell23_5133982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5133982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133982 prefixEnd_5133982 := by exact prefixLift 5133982
  have htrace : WordTrace (prefixWord ++ tailWord_5133982) baseStart_5133982 baseEnd_5133982 := by
    simpa [prefixWord, tailWord_5133982, baseEnd_5133982] using wordTrace_append hprefix tailTrace_5133982
  have hstable : (prefixWord ++ tailWord_5133982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133982).length < 2 ^ (prefixWord ++ tailWord_5133982).sum := by decide
  have hdescent : baseEnd_5133982 < baseStart_5133982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5133988 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_5133988 : Nat := 118140960795 + 5133988 * 2 ^ 59
def prefixEnd_5133988 : Nat := 4983230072969 + 3 ^ 40 * 5133988 * 2
def baseEnd_5133988 : Nat := 2636203518415164482039225

theorem tailTrace_5133988 : CollatzResearch.WordTrace tailWord_5133988 prefixEnd_5133988 2636203518415164482039225 := by
  unfold tailWord_5133988
  simp only [CollatzResearch.WordTrace]
  refine ⟨93625962862222883094337309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124834617149630510792449745 93625962862222883094337309)
  ·
    refine ⟨35109736073333581160376491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93625962862222883094337309 35109736073333581160376491)
    ·
      refine ⟨52664604110000371740564737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35109736073333581160376491 52664604110000371740564737)
      ·
        refine ⟨39498453082500278805423553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52664604110000371740564737 39498453082500278805423553)
        ·
          refine ⟨29623839811875209104067665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39498453082500278805423553 29623839811875209104067665)
          ·
            refine ⟨22217879858906406828050749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29623839811875209104067665 22217879858906406828050749)
            ·
              refine ⟨8331704947089902560519031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22217879858906406828050749 8331704947089902560519031)
              ·
                refine ⟨12497557420634853840778547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8331704947089902560519031 12497557420634853840778547)
                ·
                  refine ⟨18746336130952280761167821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12497557420634853840778547 18746336130952280761167821)
                  ·
                    refine ⟨7029876049107105285437933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18746336130952280761167821 7029876049107105285437933)
                    ·
                      refine ⟨2636203518415164482039225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7029876049107105285437933 2636203518415164482039225)
                      ·
                        rfl

theorem cell23_5133988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_5133988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5133988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5133988 prefixEnd_5133988 := by exact prefixLift 5133988
  have htrace : WordTrace (prefixWord ++ tailWord_5133988) baseStart_5133988 baseEnd_5133988 := by
    simpa [prefixWord, tailWord_5133988, baseEnd_5133988] using wordTrace_append hprefix tailTrace_5133988
  have hstable : (prefixWord ++ tailWord_5133988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5133988).length < 2 ^ (prefixWord ++ tailWord_5133988).sum := by decide
  have hdescent : baseEnd_5133988 < baseStart_5133988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5133988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134006 : List Nat := [5, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_5134006 : Nat := 118140960795 + 5134006 * 2 ^ 59
def prefixEnd_5134006 : Nat := 4983230072969 + 3 ^ 40 * 5134006 * 2
def baseEnd_5134006 : Nat := 2636212761066945411614143

theorem tailTrace_5134006 : CollatzResearch.WordTrace tailWord_5134006 prefixEnd_5134006 2636212761066945411614143 := by
  unfold tailWord_5134006
  simp only [CollatzResearch.WordTrace]
  refine ⟨11703286389898784703926867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124835054825587036841886581 11703286389898784703926867)
  ·
    refine ⟨17554929584848177055890301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11703286389898784703926867 17554929584848177055890301)
    ·
      refine ⟨6583098594318066395958863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17554929584848177055890301 6583098594318066395958863)
      ·
        refine ⟨9874647891477099593938295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6583098594318066395958863 9874647891477099593938295)
        ·
          refine ⟨14811971837215649390907443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9874647891477099593938295 14811971837215649390907443)
          ·
            refine ⟨22217957755823474086361165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14811971837215649390907443 22217957755823474086361165)
            ·
              refine ⟨8331734158433802782385437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22217957755823474086361165 8331734158433802782385437)
              ·
                refine ⟨3124400309412676043394539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8331734158433802782385437 3124400309412676043394539)
                ·
                  refine ⟨4686600464119014065091809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124400309412676043394539 4686600464119014065091809)
                  ·
                    refine ⟨3514950348089260548818857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4686600464119014065091809 3514950348089260548818857)
                    ·
                      refine ⟨2636212761066945411614143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514950348089260548818857 2636212761066945411614143)
                      ·
                        rfl

theorem cell23_5134006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_5134006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134006 prefixEnd_5134006 := by exact prefixLift 5134006
  have htrace : WordTrace (prefixWord ++ tailWord_5134006) baseStart_5134006 baseEnd_5134006 := by
    simpa [prefixWord, tailWord_5134006, baseEnd_5134006] using wordTrace_append hprefix tailTrace_5134006
  have hstable : (prefixWord ++ tailWord_5134006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134006).length < 2 ^ (prefixWord ++ tailWord_5134006).sum := by decide
  have hdescent : baseEnd_5134006 < baseStart_5134006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134049 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_5134049 : Nat := 118140960795 + 5134049 * 2 ^ 59
def prefixEnd_5134049 : Nat := 4983230072969 + 3 ^ 40 * 5134049 * 2
def baseEnd_5134049 : Nat := 2636234840735088743376445

theorem tailTrace_5134049 : CollatzResearch.WordTrace tailWord_5134049 prefixEnd_5134049 2636234840735088743376445 := by
  unfold tailWord_5134049
  simp only [CollatzResearch.WordTrace]
  refine ⟨187254150577224773606645201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124836100384816515737763467 187254150577224773606645201)
  ·
    refine ⟨140440612932918580204983901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187254150577224773606645201 140440612932918580204983901)
    ·
      refine ⟨52665229849844467576868963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140440612932918580204983901 52665229849844467576868963)
      ·
        refine ⟨78997844774766701365303445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52665229849844467576868963 78997844774766701365303445)
        ·
          refine ⟨3703023973817189126498599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78997844774766701365303445 3703023973817189126498599)
          ·
            refine ⟨5554535960725783689747899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703023973817189126498599 5554535960725783689747899)
            ·
              refine ⟨8331803941088675534621849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554535960725783689747899 8331803941088675534621849)
              ·
                refine ⟨6248852955816506650966387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8331803941088675534621849 6248852955816506650966387)
                ·
                  refine ⟨9373279433724759976449581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6248852955816506650966387 9373279433724759976449581)
                  ·
                    refine ⟨3514979787646784991168593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9373279433724759976449581 3514979787646784991168593)
                    ·
                      refine ⟨2636234840735088743376445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3514979787646784991168593 2636234840735088743376445)
                      ·
                        rfl

theorem cell23_5134049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_5134049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134049 prefixEnd_5134049 := by exact prefixLift 5134049
  have htrace : WordTrace (prefixWord ++ tailWord_5134049) baseStart_5134049 baseEnd_5134049 := by
    simpa [prefixWord, tailWord_5134049, baseEnd_5134049] using wordTrace_append hprefix tailTrace_5134049
  have hstable : (prefixWord ++ tailWord_5134049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134049).length < 2 ^ (prefixWord ++ tailWord_5134049).sum := by decide
  have hdescent : baseEnd_5134049 < baseStart_5134049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134088 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_5134088 : Nat := 118140960795 + 5134088 * 2 ^ 59
def prefixEnd_5134088 : Nat := 4983230072969 + 3 ^ 40 * 5134088 * 2
def baseEnd_5134088 : Nat := 2636254866480614090788765

theorem tailTrace_5134088 : CollatzResearch.WordTrace tailWord_5134088 prefixEnd_5134088 2636254866480614090788765 := by
  unfold tailWord_5134088
  simp only [CollatzResearch.WordTrace]
  refine ⟨93627786512041741633657459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124837048682722322178209945 93627786512041741633657459)
  ·
    refine ⟨140441679768062612450486189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93627786512041741633657459 140441679768062612450486189)
    ·
      refine ⟨52665629913023479668932321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140441679768062612450486189 52665629913023479668932321)
      ·
        refine ⟨39499222434767609751699241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52665629913023479668932321 39499222434767609751699241)
        ·
          refine ⟨29624416826075707313774431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39499222434767609751699241 29624416826075707313774431)
          ·
            refine ⟨44436625239113560970661647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29624416826075707313774431 44436625239113560970661647)
            ·
              refine ⟨66654937858670341455992471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44436625239113560970661647 66654937858670341455992471)
              ·
                refine ⟨99982406788005512183988707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66654937858670341455992471 99982406788005512183988707)
                ·
                  refine ⟨149973610182008268275983061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99982406788005512183988707 149973610182008268275983061)
                  ·
                    refine ⟨3515006488640818787718353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149973610182008268275983061 3515006488640818787718353)
                    ·
                      refine ⟨2636254866480614090788765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515006488640818787718353 2636254866480614090788765)
                      ·
                        rfl

theorem cell23_5134088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_5134088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134088 prefixEnd_5134088 := by exact prefixLift 5134088
  have htrace : WordTrace (prefixWord ++ tailWord_5134088) baseStart_5134088 baseEnd_5134088 := by
    simpa [prefixWord, tailWord_5134088, baseEnd_5134088] using wordTrace_append hprefix tailTrace_5134088
  have hstable : (prefixWord ++ tailWord_5134088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134088).length < 2 ^ (prefixWord ++ tailWord_5134088).sum := by decide
  have hdescent : baseEnd_5134088 < baseStart_5134088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134091 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 5]
def baseStart_5134091 : Nat := 118140960795 + 5134091 * 2 ^ 59
def prefixEnd_5134091 : Nat := 4983230072969 + 3 ^ 40 * 5134091 * 2
def baseEnd_5134091 : Nat := 2636256406922577579051251

theorem tailTrace_5134091 : CollatzResearch.WordTrace tailWord_5134091 prefixEnd_5134091 2636256406922577579051251 := by
  unfold tailWord_5134091
  simp only [CollatzResearch.WordTrace]
  refine ⟨187255682443072614779674127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124837121628715076519782751 187255682443072614779674127)
  ·
    refine ⟨280883523664608922169511191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187255682443072614779674127 280883523664608922169511191)
    ·
      refine ⟨421325285496913383254266787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280883523664608922169511191 421325285496913383254266787)
      ·
        refine ⟨631987928245370074881400181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421325285496913383254266787 631987928245370074881400181)
        ·
          refine ⟨59248868273003444520131267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 631987928245370074881400181 59248868273003444520131267)
          ·
            refine ⟨88873302409505166780196901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59248868273003444520131267 88873302409505166780196901)
            ·
              refine ⟨16663744201782218771286919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88873302409505166780196901 16663744201782218771286919)
              ·
                refine ⟨24995616302673328156930379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16663744201782218771286919 24995616302673328156930379)
                ·
                  refine ⟨37493424454009992235395569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24995616302673328156930379 37493424454009992235395569)
                  ·
                    refine ⟨28120068340507494176546677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37493424454009992235395569 28120068340507494176546677)
                    ·
                      refine ⟨2636256406922577579051251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28120068340507494176546677 2636256406922577579051251)
                      ·
                        rfl

theorem cell23_5134091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 5].length) (baseStart_5134091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134091 prefixEnd_5134091 := by exact prefixLift 5134091
  have htrace : WordTrace (prefixWord ++ tailWord_5134091) baseStart_5134091 baseEnd_5134091 := by
    simpa [prefixWord, tailWord_5134091, baseEnd_5134091] using wordTrace_append hprefix tailTrace_5134091
  have hstable : (prefixWord ++ tailWord_5134091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134091).length < 2 ^ (prefixWord ++ tailWord_5134091).sum := by decide
  have hdescent : baseEnd_5134091 < baseStart_5134091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134179 : List Nat := [1, 1, 1, 5, 4, 2, 1, 3, 1, 4]
def baseStart_5134179 : Nat := 118140960795 + 5134179 * 2 ^ 59
def prefixEnd_5134179 : Nat := 4983230072969 + 3 ^ 40 * 5134179 * 2
def baseEnd_5134179 : Nat := 878767197740057744916949

theorem tailTrace_5134179 : CollatzResearch.WordTrace tailWord_5134179 prefixEnd_5134179 878767197740057744916949 := by
  unfold tailWord_5134179
  simp only [CollatzResearch.WordTrace]
  refine ⟨187258892066753805808877591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124839261377835870539251727 187258892066753805808877591)
  ·
    refine ⟨280888338100130708713316387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187258892066753805808877591 280888338100130708713316387)
    ·
      refine ⟨421332507150196063069974581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280888338100130708713316387 421332507150196063069974581)
      ·
        refine ⟨39499922545330880912810117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 421332507150196063069974581 39499922545330880912810117)
        ·
          refine ⟨7406235477249540171151897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39499922545330880912810117 7406235477249540171151897)
          ·
            refine ⟨5554676607937155128363923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7406235477249540171151897 5554676607937155128363923)
            ·
              refine ⟨8332014911905732692545885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554676607937155128363923 8332014911905732692545885)
              ·
                refine ⟨3124505591964649759704707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8332014911905732692545885 3124505591964649759704707)
                ·
                  refine ⟨4686758387946974639557061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124505591964649759704707 4686758387946974639557061)
                  ·
                    refine ⟨878767197740057744916949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4686758387946974639557061 878767197740057744916949)
                    ·
                      rfl

theorem cell23_5134179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 4].length) (baseStart_5134179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134179 prefixEnd_5134179 := by exact prefixLift 5134179
  have htrace : WordTrace (prefixWord ++ tailWord_5134179) baseStart_5134179 baseEnd_5134179 := by
    simpa [prefixWord, tailWord_5134179, baseEnd_5134179] using wordTrace_append hprefix tailTrace_5134179
  have hstable : (prefixWord ++ tailWord_5134179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134179).length < 2 ^ (prefixWord ++ tailWord_5134179).sum := by decide
  have hdescent : baseEnd_5134179 < baseStart_5134179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134202 : List Nat := [3, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3]
def baseStart_5134202 : Nat := 118140960795 + 5134202 * 2 ^ 59
def prefixEnd_5134202 : Nat := 4983230072969 + 3 ^ 40 * 5134202 * 2
def baseEnd_5134202 : Nat := 2636313403275226644763241

theorem tailTrace_5134202 : CollatzResearch.WordTrace tailWord_5134202 prefixEnd_5134202 2636313403275226644763241 := by
  unfold tailWord_5134202
  simp only [CollatzResearch.WordTrace]
  refine ⟨46814932736417620184241215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124839820630446987157976573 46814932736417620184241215)
  ·
    refine ⟨70222399104626430276361823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46814932736417620184241215 70222399104626430276361823)
    ·
      refine ⟨105333598656939645414542735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70222399104626430276361823 105333598656939645414542735)
      ·
        refine ⟨158000397985409468121814103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105333598656939645414542735 158000397985409468121814103)
        ·
          refine ⟨237000596978114202182721155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158000397985409468121814103 237000596978114202182721155)
          ·
            refine ⟨355500895467171303274081733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237000596978114202182721155 355500895467171303274081733)
            ·
              refine ⟨66656417900094619363890325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 355500895467171303274081733 66656417900094619363890325)
              ·
                refine ⟨3124519589066935282682359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66656417900094619363890325 3124519589066935282682359)
                ·
                  refine ⟨4686779383600402924023539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124519589066935282682359 4686779383600402924023539)
                  ·
                    refine ⟨7030169075400604386035309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4686779383600402924023539 7030169075400604386035309)
                    ·
                      refine ⟨2636313403275226644763241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7030169075400604386035309 2636313403275226644763241)
                      ·
                        rfl

theorem cell23_5134202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3].length) (baseStart_5134202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134202 prefixEnd_5134202 := by exact prefixLift 5134202
  have htrace : WordTrace (prefixWord ++ tailWord_5134202) baseStart_5134202 baseEnd_5134202 := by
    simpa [prefixWord, tailWord_5134202, baseEnd_5134202] using wordTrace_append hprefix tailTrace_5134202
  have hstable : (prefixWord ++ tailWord_5134202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134202).length < 2 ^ (prefixWord ++ tailWord_5134202).sum := by decide
  have hdescent : baseEnd_5134202 < baseStart_5134202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134208 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_5134208 : Nat := 118140960795 + 5134208 * 2 ^ 59
def prefixEnd_5134208 : Nat := 4983230072969 + 3 ^ 40 * 5134208 * 2
def baseEnd_5134208 : Nat := 2636316484159153621288213

theorem tailTrace_5134208 : CollatzResearch.WordTrace tailWord_5134208 prefixEnd_5134208 2636316484159153621288213 := by
  unfold tailWord_5134208
  simp only [CollatzResearch.WordTrace]
  refine ⟨93629974891824371880841639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124839966522432495841122185 93629974891824371880841639)
  ·
    refine ⟨140444962337736557821262459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93629974891824371880841639 140444962337736557821262459)
    ·
      refine ⟨210667443506604836731893689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140444962337736557821262459 210667443506604836731893689)
      ·
        refine ⟨158000582629953627548920267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210667443506604836731893689 158000582629953627548920267)
        ·
          refine ⟨237000873944930441323380401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158000582629953627548920267 237000873944930441323380401)
          ·
            refine ⟨177750655458697830992535301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237000873944930441323380401 177750655458697830992535301)
            ·
              refine ⟨33328247898505843311100369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177750655458697830992535301 33328247898505843311100369)
              ·
                refine ⟨24996185923879382483325277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33328247898505843311100369 24996185923879382483325277)
                ·
                  refine ⟨9373569721454768431246979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24996185923879382483325277 9373569721454768431246979)
                  ·
                    refine ⟨14060354582182152646870469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9373569721454768431246979 14060354582182152646870469)
                    ·
                      refine ⟨2636316484159153621288213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14060354582182152646870469 2636316484159153621288213)
                      ·
                        rfl

theorem cell23_5134208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_5134208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134208 prefixEnd_5134208 := by exact prefixLift 5134208
  have htrace : WordTrace (prefixWord ++ tailWord_5134208) baseStart_5134208 baseEnd_5134208 := by
    simpa [prefixWord, tailWord_5134208, baseEnd_5134208] using wordTrace_append hprefix tailTrace_5134208
  have hstable : (prefixWord ++ tailWord_5134208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134208).length < 2 ^ (prefixWord ++ tailWord_5134208).sum := by decide
  have hdescent : baseEnd_5134208 < baseStart_5134208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134209 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 6]
def baseStart_5134209 : Nat := 118140960795 + 5134209 * 2 ^ 59
def prefixEnd_5134209 : Nat := 4983230072969 + 3 ^ 40 * 5134209 * 2
def baseEnd_5134209 : Nat := 292924110848867568597301

theorem tailTrace_5134209 : CollatzResearch.WordTrace tailWord_5134209 prefixEnd_5134209 292924110848867568597301 := by
  unfold tailWord_5134209
  simp only [CollatzResearch.WordTrace]
  refine ⟨187259986256645120932469681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124839990837763413954979787 187259986256645120932469681)
  ·
    refine ⟨140444989692483840699352261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187259986256645120932469681 140444989692483840699352261)
    ·
      refine ⟨26333435567340720131128549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140444989692483840699352261 26333435567340720131128549)
      ·
        refine ⟨4937519168876385024586603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26333435567340720131128549 4937519168876385024586603)
        ·
          refine ⟨7406278753314577536879905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4937519168876385024586603 7406278753314577536879905)
          ·
            refine ⟨5554709064985933152659929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7406278753314577536879905 5554709064985933152659929)
            ·
              refine ⟨4166031798739449864494947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5554709064985933152659929 4166031798739449864494947)
              ·
                refine ⟨6249047698109174796742421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166031798739449864494947 6249047698109174796742421)
                ·
                  refine ⟨292924110848867568597301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6249047698109174796742421 292924110848867568597301)
                  ·
                    rfl

theorem cell23_5134209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 6].length) (baseStart_5134209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134209 prefixEnd_5134209 := by exact prefixLift 5134209
  have htrace : WordTrace (prefixWord ++ tailWord_5134209) baseStart_5134209 baseEnd_5134209 := by
    simpa [prefixWord, tailWord_5134209, baseEnd_5134209] using wordTrace_append hprefix tailTrace_5134209
  have hstable : (prefixWord ++ tailWord_5134209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134209).length < 2 ^ (prefixWord ++ tailWord_5134209).sum := by decide
  have hdescent : baseEnd_5134209 < baseStart_5134209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134222 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_5134222 : Nat := 118140960795 + 5134222 * 2 ^ 59
def prefixEnd_5134222 : Nat := 4983230072969 + 3 ^ 40 * 5134222 * 2
def baseEnd_5134222 : Nat := 878774557629438855504383

theorem tailTrace_5134222 : CollatzResearch.WordTrace tailWord_5134222 prefixEnd_5134222 878774557629438855504383 := by
  unfold tailWord_5134222
  simp only [CollatzResearch.WordTrace]
  refine ⟨23407557550699753019086615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124840306937065349435128613 23407557550699753019086615)
  ·
    refine ⟨35111336326049629528629923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23407557550699753019086615 35111336326049629528629923)
    ·
      refine ⟨52667004489074444292944885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35111336326049629528629923 52667004489074444292944885)
      ·
        refine ⟨4937531670850729152463583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52667004489074444292944885 4937531670850729152463583)
        ·
          refine ⟨7406297506276093728695375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4937531670850729152463583 7406297506276093728695375)
          ·
            refine ⟨11109446259414140593043063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7406297506276093728695375 11109446259414140593043063)
            ·
              refine ⟨16664169389121210889564595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11109446259414140593043063 16664169389121210889564595)
              ·
                refine ⟨24996254083681816334346893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16664169389121210889564595 24996254083681816334346893)
                ·
                  refine ⟨9373595281380681125380085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24996254083681816334346893 9373595281380681125380085)
                  ·
                    refine ⟨878774557629438855504383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9373595281380681125380085 878774557629438855504383)
                    ·
                      rfl

theorem cell23_5134222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_5134222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134222 prefixEnd_5134222 := by exact prefixLift 5134222
  have htrace : WordTrace (prefixWord ++ tailWord_5134222) baseStart_5134222 baseEnd_5134222 := by
    simpa [prefixWord, tailWord_5134222, baseEnd_5134222] using wordTrace_append hprefix tailTrace_5134222
  have hstable : (prefixWord ++ tailWord_5134222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134222).length < 2 ^ (prefixWord ++ tailWord_5134222).sum := by decide
  have hdescent : baseEnd_5134222 < baseStart_5134222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134225 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 4]
def baseStart_5134225 : Nat := 118140960795 + 5134225 * 2 ^ 59
def prefixEnd_5134225 : Nat := 4983230072969 + 3 ^ 40 * 5134225 * 2
def baseEnd_5134225 : Nat := 2636325213330280054775635

theorem tailTrace_5134225 : CollatzResearch.WordTrace tailWord_5134225 prefixEnd_5134225 2636325213330280054775635 := by
  unfold tailWord_5134225
  simp only [CollatzResearch.WordTrace]
  refine ⟨187260569824587155665052129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124840379883058103776701419 187260569824587155665052129)
  ·
    refine ⟨140445427368440366748789097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187260569824587155665052129 140445427368440366748789097)
    ·
      refine ⟨105334070526330275061591823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140445427368440366748789097 105334070526330275061591823)
      ·
        refine ⟨158001105789495412592387735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105334070526330275061591823 158001105789495412592387735)
        ·
          refine ⟨237001658684243118888581603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158001105789495412592387735 237001658684243118888581603)
          ·
            refine ⟨355502488026364678332872405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237001658684243118888581603 355502488026364678332872405)
            ·
              refine ⟨8332089563117922148426697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 355502488026364678332872405 8332089563117922148426697)
              ·
                refine ⟨6249067172338441611320023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8332089563117922148426697 6249067172338441611320023)
                ·
                  refine ⟨9373600758507662416980035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6249067172338441611320023 9373600758507662416980035)
                  ·
                    refine ⟨14060401137761493625470053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9373600758507662416980035 14060401137761493625470053)
                    ·
                      refine ⟨2636325213330280054775635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14060401137761493625470053 2636325213330280054775635)
                      ·
                        rfl

theorem cell23_5134225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_5134225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134225 prefixEnd_5134225 := by exact prefixLift 5134225
  have htrace : WordTrace (prefixWord ++ tailWord_5134225) baseStart_5134225 baseEnd_5134225 := by
    simpa [prefixWord, tailWord_5134225, baseEnd_5134225] using wordTrace_append hprefix tailTrace_5134225
  have hstable : (prefixWord ++ tailWord_5134225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134225).length < 2 ^ (prefixWord ++ tailWord_5134225).sum := by decide
  have hdescent : baseEnd_5134225 < baseStart_5134225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134245 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 3]
def baseStart_5134245 : Nat := 118140960795 + 5134245 * 2 ^ 59
def prefixEnd_5134245 : Nat := 4983230072969 + 3 ^ 40 * 5134245 * 2
def baseEnd_5134245 : Nat := 2636335482943369976525543

theorem tailTrace_5134245 : CollatzResearch.WordTrace tailWord_5134245 prefixEnd_5134245 2636335482943369976525543 := by
  unfold tailWord_5134245
  simp only [CollatzResearch.WordTrace]
  refine ⟨187261299284514699080780189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124840866189676466053853459 187261299284514699080780189)
  ·
    refine ⟨70222987231693012155292571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187261299284514699080780189 70222987231693012155292571)
    ·
      refine ⟨105334480847539518232938857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70222987231693012155292571 105334480847539518232938857)
      ·
        refine ⟨79000860635654638674704143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105334480847539518232938857 79000860635654638674704143)
        ·
          refine ⟨118501290953481958012056215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79000860635654638674704143 118501290953481958012056215)
          ·
            refine ⟨177751936430222937018084323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118501290953481958012056215 177751936430222937018084323)
            ·
              refine ⟨266627904645334405527126485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177751936430222937018084323 266627904645334405527126485)
              ·
                refine ⟨6249091515125025129542027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 266627904645334405527126485 6249091515125025129542027)
                ·
                  refine ⟨9373637272687537694313041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6249091515125025129542027 9373637272687537694313041)
                  ·
                    refine ⟨7030227954515653270734781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9373637272687537694313041 7030227954515653270734781)
                    ·
                      refine ⟨2636335482943369976525543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7030227954515653270734781 2636335482943369976525543)
                      ·
                        rfl

theorem cell23_5134245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_5134245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134245 prefixEnd_5134245 := by exact prefixLift 5134245
  have htrace : WordTrace (prefixWord ++ tailWord_5134245) baseStart_5134245 baseEnd_5134245 := by
    simpa [prefixWord, tailWord_5134245, baseEnd_5134245] using wordTrace_append hprefix tailTrace_5134245
  have hstable : (prefixWord ++ tailWord_5134245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134245).length < 2 ^ (prefixWord ++ tailWord_5134245).sum := by decide
  have hdescent : baseEnd_5134245 < baseStart_5134245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134259 : List Nat := [1, 1, 1, 2, 3, 1, 5, 4, 1, 2, 2]
def baseStart_5134259 : Nat := 118140960795 + 5134259 * 2 ^ 59
def prefixEnd_5134259 : Nat := 4983230072969 + 3 ^ 40 * 5134259 * 2
def baseEnd_5134259 : Nat := 2636342671672532921750479

theorem tailTrace_5134259 : CollatzResearch.WordTrace tailWord_5134259 prefixEnd_5134259 2636342671672532921750479 := by
  unfold tailWord_5134259
  simp only [CollatzResearch.WordTrace]
  refine ⟨187261809906463979471789831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124841206604309319647859887 187261809906463979471789831)
  ·
    refine ⟨280892714859695969207684747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187261809906463979471789831 280892714859695969207684747)
    ·
      refine ⟨421339072289543953811527121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280892714859695969207684747 421339072289543953811527121)
      ·
        refine ⟨316004304217157965358645341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421339072289543953811527121 316004304217157965358645341)
        ·
          refine ⟨118501614081434237009492003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316004304217157965358645341 118501614081434237009492003)
          ·
            refine ⟨177752421122151355514238005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118501614081434237009492003 177752421122151355514238005)
            ·
              refine ⟨16664289480201689579459813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177752421122151355514238005 16664289480201689579459813)
              ·
                refine ⟨3124554277537816796148715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16664289480201689579459813 3124554277537816796148715)
                ·
                  refine ⟨4686831416306725194223073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124554277537816796148715 4686831416306725194223073)
                  ·
                    refine ⟨3515123562230043895667305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4686831416306725194223073 3515123562230043895667305)
                    ·
                      refine ⟨2636342671672532921750479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515123562230043895667305 2636342671672532921750479)
                      ·
                        rfl

theorem cell23_5134259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 2, 2].length) (baseStart_5134259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134259 prefixEnd_5134259 := by exact prefixLift 5134259
  have htrace : WordTrace (prefixWord ++ tailWord_5134259) baseStart_5134259 baseEnd_5134259 := by
    simpa [prefixWord, tailWord_5134259, baseEnd_5134259] using wordTrace_append hprefix tailTrace_5134259
  have hstable : (prefixWord ++ tailWord_5134259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134259).length < 2 ^ (prefixWord ++ tailWord_5134259).sum := by decide
  have hdescent : baseEnd_5134259 < baseStart_5134259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134292 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_5134292 : Nat := 118140960795 + 5134292 * 2 ^ 59
def prefixEnd_5134292 : Nat := 4983230072969 + 3 ^ 40 * 5134292 * 2
def baseEnd_5134292 : Nat := 2636359616534131292637827

theorem tailTrace_5134292 : CollatzResearch.WordTrace tailWord_5134292 prefixEnd_5134292 2636359616534131292637827 := by
  unfold tailWord_5134292
  simp only [CollatzResearch.WordTrace]
  refine ⟨93631506757672213053870565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124842009010229617405160753 93631506757672213053870565)
  ·
    refine ⟨17555907517063539947600731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93631506757672213053870565 17555907517063539947600731)
    ·
      refine ⟨26333861275595309921401097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17555907517063539947600731 26333861275595309921401097)
      ·
        refine ⟨19750395956696482441050823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26333861275595309921401097 19750395956696482441050823)
        ·
          refine ⟨29625593935044723661576235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19750395956696482441050823 29625593935044723661576235)
          ·
            refine ⟨44438390902567085492364353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29625593935044723661576235 44438390902567085492364353)
            ·
              refine ⟨33328793176925314119273265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44438390902567085492364353 33328793176925314119273265)
              ·
                refine ⟨24996594882693985589454949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33328793176925314119273265 24996594882693985589454949)
                ·
                  refine ⟨4686861540505122298022803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24996594882693985589454949 4686861540505122298022803)
                  ·
                    refine ⟨7030292310757683447034205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4686861540505122298022803 7030292310757683447034205)
                    ·
                      refine ⟨2636359616534131292637827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7030292310757683447034205 2636359616534131292637827)
                      ·
                        rfl

theorem cell23_5134292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_5134292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134292 prefixEnd_5134292 := by exact prefixLift 5134292
  have htrace : WordTrace (prefixWord ++ tailWord_5134292) baseStart_5134292 baseEnd_5134292 := by
    simpa [prefixWord, tailWord_5134292, baseEnd_5134292] using wordTrace_append hprefix tailTrace_5134292
  have hstable : (prefixWord ++ tailWord_5134292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134292).length < 2 ^ (prefixWord ++ tailWord_5134292).sum := by decide
  have hdescent : baseEnd_5134292 < baseStart_5134292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134308 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_5134308 : Nat := 118140960795 + 5134308 * 2 ^ 59
def prefixEnd_5134308 : Nat := 4983230072969 + 3 ^ 40 * 5134308 * 2
def baseEnd_5134308 : Nat := 878789277408201076679251

theorem tailTrace_5134308 : CollatzResearch.WordTrace tailWord_5134308 prefixEnd_5134308 878789277408201076679251 := by
  unfold tailWord_5134308
  simp only [CollatzResearch.WordTrace]
  refine ⟨93631798541643230420161789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124842398055524307226882385 93631798541643230420161789)
  ·
    refine ⟨35111924453116211407560671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93631798541643230420161789 35111924453116211407560671)
    ·
      refine ⟨52667886679674317111341007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35111924453116211407560671 52667886679674317111341007)
      ·
        refine ⟨79001830019511475667011511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52667886679674317111341007 79001830019511475667011511)
        ·
          refine ⟨118502745029267213500517267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79001830019511475667011511 118502745029267213500517267)
          ·
            refine ⟨177754117543900820250775901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118502745029267213500517267 177754117543900820250775901)
            ·
              refine ⟨66657794078962807594040963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177754117543900820250775901 66657794078962807594040963)
              ·
                refine ⟨99986691118444211391061445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66657794078962807594040963 99986691118444211391061445)
                ·
                  refine ⟨18747504584708289635824021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99986691118444211391061445 18747504584708289635824021)
                  ·
                    refine ⟨878789277408201076679251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18747504584708289635824021 878789277408201076679251)
                    ·
                      rfl

theorem cell23_5134308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_5134308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134308 prefixEnd_5134308 := by exact prefixLift 5134308
  have htrace : WordTrace (prefixWord ++ tailWord_5134308) baseStart_5134308 baseEnd_5134308 := by
    simpa [prefixWord, tailWord_5134308, baseEnd_5134308] using wordTrace_append hprefix tailTrace_5134308
  have hstable : (prefixWord ++ tailWord_5134308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134308).length < 2 ^ (prefixWord ++ tailWord_5134308).sum := by decide
  have hdescent : baseEnd_5134308 < baseStart_5134308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134315 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 3, 4, 2]
def baseStart_5134315 : Nat := 118140960795 + 5134315 * 2 ^ 59
def prefixEnd_5134315 : Nat := 4983230072969 + 3 ^ 40 * 5134315 * 2
def baseEnd_5134315 : Nat := 2636371426589184702650221

theorem tailTrace_5134315 : CollatzResearch.WordTrace tailWord_5134315 prefixEnd_5134315 2636371426589184702650221 := by
  unfold tailWord_5134315
  simp only [CollatzResearch.WordTrace]
  refine ⟨187263852394261101035828399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124842568262840734023885599 187263852394261101035828399)
  ·
    refine ⟨280895778591391651553742599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187263852394261101035828399 280895778591391651553742599)
    ·
      refine ⟨421343667887087477330613899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280895778591391651553742599 421343667887087477330613899)
      ·
        refine ⟨632015501830631215995920849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421343667887087477330613899 632015501830631215995920849)
        ·
          refine ⟨474011626372973411996940637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632015501830631215995920849 474011626372973411996940637)
          ·
            refine ⟨177754359889865029498852739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474011626372973411996940637 177754359889865029498852739)
            ·
              refine ⟨266631539834797544248279109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177754359889865029498852739 266631539834797544248279109)
              ·
                refine ⟨49993413719024539546552333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266631539834797544248279109 49993413719024539546552333)
                ·
                  refine ⟨18747530144634202329957125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49993413719024539546552333 18747530144634202329957125)
                  ·
                    refine ⟨3515161902118912936866961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18747530144634202329957125 3515161902118912936866961)
                    ·
                      refine ⟨2636371426589184702650221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515161902118912936866961 2636371426589184702650221)
                      ·
                        rfl

theorem cell23_5134315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 4, 2].length) (baseStart_5134315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134315 prefixEnd_5134315 := by exact prefixLift 5134315
  have htrace : WordTrace (prefixWord ++ tailWord_5134315) baseStart_5134315 baseEnd_5134315 := by
    simpa [prefixWord, tailWord_5134315, baseEnd_5134315] using wordTrace_append hprefix tailTrace_5134315
  have hstable : (prefixWord ++ tailWord_5134315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134315).length < 2 ^ (prefixWord ++ tailWord_5134315).sum := by decide
  have hdescent : baseEnd_5134315 < baseStart_5134315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134326 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_5134326 : Nat := 118140960795 + 5134326 * 2 ^ 59
def prefixEnd_5134326 : Nat := 4983230072969 + 3 ^ 40 * 5134326 * 2
def baseEnd_5134326 : Nat := 2636377074876384159612671

theorem tailTrace_5134326 : CollatzResearch.WordTrace tailWord_5134326 prefixEnd_5134326 2636377074876384159612671 := by
  unfold tailWord_5134326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11704015849826328119654927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124842835731480833276319221 11704015849826328119654927)
  ·
    refine ⟨17556023774739492179482391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11704015849826328119654927 17556023774739492179482391)
    ·
      refine ⟨26334035662109238269223587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17556023774739492179482391 26334035662109238269223587)
      ·
        refine ⟨39501053493163857403835381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26334035662109238269223587 39501053493163857403835381)
        ·
          refine ⟨3703223764984111631609567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39501053493163857403835381 3703223764984111631609567)
          ·
            refine ⟨5554835647476167447414351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703223764984111631609567 5554835647476167447414351)
            ·
              refine ⟨8332253471214251171121527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554835647476167447414351 8332253471214251171121527)
              ·
                refine ⟨12498380206821376756682291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8332253471214251171121527 12498380206821376756682291)
                ·
                  refine ⟨18747570310232065135023437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12498380206821376756682291 18747570310232065135023437)
                  ·
                    refine ⟨7030338866337024425633789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18747570310232065135023437 7030338866337024425633789)
                    ·
                      refine ⟨2636377074876384159612671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7030338866337024425633789 2636377074876384159612671)
                      ·
                        rfl

theorem cell23_5134326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_5134326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134326 prefixEnd_5134326 := by exact prefixLift 5134326
  have htrace : WordTrace (prefixWord ++ tailWord_5134326) baseStart_5134326 baseEnd_5134326 := by
    simpa [prefixWord, tailWord_5134326, baseEnd_5134326] using wordTrace_append hprefix tailTrace_5134326
  have hstable : (prefixWord ++ tailWord_5134326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134326).length < 2 ^ (prefixWord ++ tailWord_5134326).sum := by decide
  have hdescent : baseEnd_5134326 < baseStart_5134326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134415 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 5, 4]
def baseStart_5134415 : Nat := 118140960795 + 5134415 * 2 ^ 59
def prefixEnd_5134415 : Nat := 4983230072969 + 3 ^ 40 * 5134415 * 2
def baseEnd_5134415 : Nat := 878807591551544770466587

theorem tailTrace_5134415 : CollatzResearch.WordTrace tailWord_5134415 prefixEnd_5134415 878807591551544770466587 := by
  unfold tailWord_5134415
  simp only [CollatzResearch.WordTrace]
  refine ⟨187267499693898818114468699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124844999795932545409645799 187267499693898818114468699)
  ·
    refine ⟨280901249540848227171703049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187267499693898818114468699 280901249540848227171703049)
    ·
      refine ⟨210675937155636170378777287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280901249540848227171703049 210675937155636170378777287)
      ·
        refine ⟨316013905733454255568165931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210675937155636170378777287 316013905733454255568165931)
        ·
          refine ⟨474020858600181383352248897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316013905733454255568165931 474020858600181383352248897)
          ·
            refine ⟨355515643950136037514186673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474020858600181383352248897 355515643950136037514186673)
            ·
              refine ⟨266636732962602028135640005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355515643950136037514186673 266636732962602028135640005)
              ·
                refine ⟨49994387430487880275432501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266636732962602028135640005 49994387430487880275432501)
                ·
                  refine ⟨4686973821608238775821797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49994387430487880275432501 4686973821608238775821797)
                  ·
                    refine ⟨878807591551544770466587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4686973821608238775821797 878807591551544770466587)
                    ·
                      rfl

theorem cell23_5134415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 4].length) (baseStart_5134415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134415 prefixEnd_5134415 := by exact prefixLift 5134415
  have htrace : WordTrace (prefixWord ++ tailWord_5134415) baseStart_5134415 baseEnd_5134415 := by
    simpa [prefixWord, tailWord_5134415, baseEnd_5134415] using wordTrace_append hprefix tailTrace_5134415
  have hstable : (prefixWord ++ tailWord_5134415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134415).length < 2 ^ (prefixWord ++ tailWord_5134415).sum := by decide
  have hdescent : baseEnd_5134415 < baseStart_5134415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134509 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_5134509 : Nat := 118140960795 + 5134509 * 2 ^ 59
def prefixEnd_5134509 : Nat := 4983230072969 + 3 ^ 40 * 5134509 * 2
def baseEnd_5134509 : Nat := 878823680612052314541443

theorem tailTrace_5134509 : CollatzResearch.WordTrace tailWord_5134509 prefixEnd_5134509 878823680612052314541443 := by
  unfold tailWord_5134509
  simp only [CollatzResearch.WordTrace]
  refine ⟨187270928155558272168390581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124847285437038848112260387 187270928155558272168390581)
  ·
    refine ⟨17556649514583588015786617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187270928155558272168390581 17556649514583588015786617)
    ·
      refine ⟨13167487135937691011839963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17556649514583588015786617 13167487135937691011839963)
      ·
        refine ⟨19751230703906536517759945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13167487135937691011839963 19751230703906536517759945)
        ·
          refine ⟨14813423027929902388319959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19751230703906536517759945 14813423027929902388319959)
          ·
            refine ⟨22220134541894853582479939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14813423027929902388319959 22220134541894853582479939)
            ·
              refine ⟨33330201812842280373719909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22220134541894853582479939 33330201812842280373719909)
              ·
                refine ⟨6249412839907927570072483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33330201812842280373719909 6249412839907927570072483)
                ·
                  refine ⟨9374119259861891355108725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6249412839907927570072483 9374119259861891355108725)
                  ·
                    refine ⟨878823680612052314541443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9374119259861891355108725 878823680612052314541443)
                    ·
                      rfl

theorem cell23_5134509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_5134509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134509 prefixEnd_5134509 := by exact prefixLift 5134509
  have htrace : WordTrace (prefixWord ++ tailWord_5134509) baseStart_5134509 baseEnd_5134509 := by
    simpa [prefixWord, tailWord_5134509, baseEnd_5134509] using wordTrace_append hprefix tailTrace_5134509
  have hstable : (prefixWord ++ tailWord_5134509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134509).length < 2 ^ (prefixWord ++ tailWord_5134509).sum := by decide
  have hdescent : baseEnd_5134509 < baseStart_5134509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134515 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 5]
def baseStart_5134515 : Nat := 118140960795 + 5134515 * 2 ^ 59
def prefixEnd_5134515 : Nat := 4983230072969 + 3 ^ 40 * 5134515 * 2
def baseEnd_5134515 : Nat := 2636474122720083920149301

theorem tailTrace_5134515 : CollatzResearch.WordTrace tailWord_5134515 prefixEnd_5134515 2636474122720083920149301 := by
  unfold tailWord_5134515
  simp only [CollatzResearch.WordTrace]
  refine ⟨187271146993536535193108999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124847431329024356795405999 187271146993536535193108999)
  ·
    refine ⟨280906720490304802789663499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187271146993536535193108999 280906720490304802789663499)
    ·
      refine ⟨421360080735457204184495249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280906720490304802789663499 421360080735457204184495249)
      ·
        refine ⟨316020060551592903138371437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421360080735457204184495249 316020060551592903138371437)
        ·
          refine ⟨118507522706847338676889289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316020060551592903138371437 118507522706847338676889289)
          ·
            refine ⟨88880642030135504007666967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118507522706847338676889289 88880642030135504007666967)
            ·
              refine ⟨133320963045203256011500451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88880642030135504007666967 133320963045203256011500451)
              ·
                refine ⟨199981444567804884017250677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133320963045203256011500451 199981444567804884017250677)
                ·
                  refine ⟨18748260428231707876617251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199981444567804884017250677 18748260428231707876617251)
                  ·
                    refine ⟨28122390642347561814925877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18748260428231707876617251 28122390642347561814925877)
                    ·
                      refine ⟨2636474122720083920149301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28122390642347561814925877 2636474122720083920149301)
                      ·
                        rfl

theorem cell23_5134515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_5134515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134515 prefixEnd_5134515 := by exact prefixLift 5134515
  have htrace : WordTrace (prefixWord ++ tailWord_5134515) baseStart_5134515 baseEnd_5134515 := by
    simpa [prefixWord, tailWord_5134515, baseEnd_5134515] using wordTrace_append hprefix tailTrace_5134515
  have hstable : (prefixWord ++ tailWord_5134515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134515).length < 2 ^ (prefixWord ++ tailWord_5134515).sum := by decide
  have hdescent : baseEnd_5134515 < baseStart_5134515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134522 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_5134522 : Nat := 118140960795 + 5134522 * 2 ^ 59
def prefixEnd_5134522 : Nat := 4983230072969 + 3 ^ 40 * 5134522 * 2
def baseEnd_5134522 : Nat := 878825905694888464253923

theorem tailTrace_5134522 : CollatzResearch.WordTrace tailWord_5134522 prefixEnd_5134522 878825905694888464253923 := by
  unfold tailWord_5134522
  simp only [CollatzResearch.WordTrace]
  refine ⟨46817850576127793847153455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124847601536340783592409213 46817850576127793847153455)
  ·
    refine ⟨70226775864191690770730183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46817850576127793847153455 70226775864191690770730183)
    ·
      refine ⟨105340163796287536156095275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70226775864191690770730183 105340163796287536156095275)
      ·
        refine ⟨158010245694431304234142913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105340163796287536156095275 158010245694431304234142913)
        ·
          refine ⟨118507684270823478175607185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158010245694431304234142913 118507684270823478175607185)
          ·
            refine ⟨88880763203117608631705389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118507684270823478175607185 88880763203117608631705389)
            ·
              refine ⟨33330286201169103236889521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88880763203117608631705389 33330286201169103236889521)
              ·
                refine ⟨24997714650876827427667141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33330286201169103236889521 24997714650876827427667141)
                ·
                  refine ⟨4687071497039405142687589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24997714650876827427667141 4687071497039405142687589)
                  ·
                    refine ⟨878825905694888464253923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687071497039405142687589 878825905694888464253923)
                    ·
                      rfl

theorem cell23_5134522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_5134522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134522 prefixEnd_5134522 := by exact prefixLift 5134522
  have htrace : WordTrace (prefixWord ++ tailWord_5134522) baseStart_5134522 baseEnd_5134522 := by
    simpa [prefixWord, tailWord_5134522, baseEnd_5134522] using wordTrace_append hprefix tailTrace_5134522
  have hstable : (prefixWord ++ tailWord_5134522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134522).length < 2 ^ (prefixWord ++ tailWord_5134522).sum := by decide
  have hdescent : baseEnd_5134522 < baseStart_5134522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134540 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5134540 : Nat := 118140960795 + 5134540 * 2 ^ 59
def prefixEnd_5134540 : Nat := 4983230072969 + 3 ^ 40 * 5134540 * 2
def baseEnd_5134540 : Nat := 2636486959736446322336687

theorem tailTrace_5134540 : CollatzResearch.WordTrace tailWord_5134540 prefixEnd_5134540 2636486959736446322336687 := by
  unfold tailWord_5134540
  simp only [CollatzResearch.WordTrace]
  refine ⟨93636029409222982231384537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124848039212297309641846049 93636029409222982231384537)
  ·
    refine ⟨70227022056917236673538403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93636029409222982231384537 70227022056917236673538403)
    ·
      refine ⟨105340533085375855010307605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70227022056917236673538403 105340533085375855010307605)
      ·
        refine ⟨4937837488376993203608169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105340533085375855010307605 4937837488376993203608169)
        ·
          refine ⟨3703378116282744902706127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4937837488376993203608169 3703378116282744902706127)
          ·
            refine ⟨5555067174424117354059191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703378116282744902706127 5555067174424117354059191)
            ·
              refine ⟨8332600761636176031088787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555067174424117354059191 8332600761636176031088787)
              ·
                refine ⟨12498901142454264046633181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8332600761636176031088787 12498901142454264046633181)
                ·
                  refine ⟨4687087928420349017487443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12498901142454264046633181 4687087928420349017487443)
                  ·
                    refine ⟨7030631892630523526231165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4687087928420349017487443 7030631892630523526231165)
                    ·
                      refine ⟨2636486959736446322336687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7030631892630523526231165 2636486959736446322336687)
                      ·
                        rfl

theorem cell23_5134540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5134540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134540 prefixEnd_5134540 := by exact prefixLift 5134540
  have htrace : WordTrace (prefixWord ++ tailWord_5134540) baseStart_5134540 baseEnd_5134540 := by
    simpa [prefixWord, tailWord_5134540, baseEnd_5134540] using wordTrace_append hprefix tailTrace_5134540
  have hstable : (prefixWord ++ tailWord_5134540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134540).length < 2 ^ (prefixWord ++ tailWord_5134540).sum := by decide
  have hdescent : baseEnd_5134540 < baseStart_5134540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134542 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_5134542 : Nat := 118140960795 + 5134542 * 2 ^ 59
def prefixEnd_5134542 : Nat := 4983230072969 + 3 ^ 40 * 5134542 * 2
def baseEnd_5134542 : Nat := 2636487986697755314511677

theorem tailTrace_5134542 : CollatzResearch.WordTrace tailWord_5134542 prefixEnd_5134542 2636487986697755314511677 := by
  unfold tailWord_5134542
  simp only [CollatzResearch.WordTrace]
  refine ⟨23409016470554839850542735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124848087842959145869561253 23409016470554839850542735)
  ·
    refine ⟨35113524705832259775814103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23409016470554839850542735 35113524705832259775814103)
    ·
      refine ⟨52670287058748389663721155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35113524705832259775814103 52670287058748389663721155)
      ·
        refine ⟨79005430588122584495581733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52670287058748389663721155 79005430588122584495581733)
        ·
          refine ⟨14813518235272984592921575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79005430588122584495581733 14813518235272984592921575)
          ·
            refine ⟨22220277352909476889382363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14813518235272984592921575 22220277352909476889382363)
            ·
              refine ⟨33330416029364215334073545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22220277352909476889382363 33330416029364215334073545)
              ·
                refine ⟨24997812022023161500555159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33330416029364215334073545 24997812022023161500555159)
                ·
                  refine ⟨37496718033034742250832739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24997812022023161500555159 37496718033034742250832739)
                  ·
                    refine ⟨56245077049552113376249109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37496718033034742250832739 56245077049552113376249109)
                    ·
                      refine ⟨2636487986697755314511677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56245077049552113376249109 2636487986697755314511677)
                      ·
                        rfl

theorem cell23_5134542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_5134542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134542 prefixEnd_5134542 := by exact prefixLift 5134542
  have htrace : WordTrace (prefixWord ++ tailWord_5134542) baseStart_5134542 baseEnd_5134542 := by
    simpa [prefixWord, tailWord_5134542, baseEnd_5134542] using wordTrace_append hprefix tailTrace_5134542
  have hstable : (prefixWord ++ tailWord_5134542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134542).length < 2 ^ (prefixWord ++ tailWord_5134542).sum := by decide
  have hdescent : baseEnd_5134542 < baseStart_5134542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134552 : List Nat := [2, 1, 2, 2, 4, 2, 2, 8]
def baseStart_5134552 : Nat := 118140960795 + 5134552 * 2 ^ 59
def prefixEnd_5134552 : Nat := 4983230072969 + 3 ^ 40 * 5134552 * 2
def baseEnd_5134552 : Nat := 97647893389048158347653

theorem tailTrace_5134552 : CollatzResearch.WordTrace tailWord_5134552 prefixEnd_5134552 97647893389048158347653 := by
  unfold tailWord_5134552
  simp only [CollatzResearch.WordTrace]
  refine ⟨93636248247201245256102955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124848330996268327008137273 93636248247201245256102955)
  ·
    refine ⟨140454372370801867884154433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93636248247201245256102955 140454372370801867884154433)
    ·
      refine ⟨105340779278101400913115825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140454372370801867884154433 105340779278101400913115825)
      ·
        refine ⟨79005584458576050684836869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105340779278101400913115825 79005584458576050684836869)
        ·
          refine ⟨14813547085983009503406913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79005584458576050684836869 14813547085983009503406913)
          ·
            refine ⟨11110160314487257127555185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14813547085983009503406913 11110160314487257127555185)
            ·
              refine ⟨8332620235865442845666389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11110160314487257127555185 8332620235865442845666389)
              ·
                refine ⟨97647893389048158347653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8332620235865442845666389 97647893389048158347653)
                ·
                  rfl

theorem cell23_5134552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 8].length) (baseStart_5134552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134552 prefixEnd_5134552 := by exact prefixLift 5134552
  have htrace : WordTrace (prefixWord ++ tailWord_5134552) baseStart_5134552 baseEnd_5134552 := by
    simpa [prefixWord, tailWord_5134552, baseEnd_5134552] using wordTrace_append hprefix tailTrace_5134552
  have hstable : (prefixWord ++ tailWord_5134552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134552).length < 2 ^ (prefixWord ++ tailWord_5134552).sum := by decide
  have hdescent : baseEnd_5134552 < baseStart_5134552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134563 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5134563 : Nat := 118140960795 + 5134563 * 2 ^ 59
def prefixEnd_5134563 : Nat := 4983230072969 + 3 ^ 40 * 5134563 * 2
def baseEnd_5134563 : Nat := 2636498769791499732349081

theorem tailTrace_5134563 : CollatzResearch.WordTrace tailWord_5134563 prefixEnd_5134563 2636498769791499732349081 := by
  unfold tailWord_5134563
  simp only [CollatzResearch.WordTrace]
  refine ⟨187272897697362639390856343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124848598464908426260570895 187272897697362639390856343)
  ·
    refine ⟨280909346546043959086284515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187272897697362639390856343 280909346546043959086284515)
    ·
      refine ⟨421364019819065938629426773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280909346546043959086284515 421364019819065938629426773)
      ·
        refine ⟨4937859607254678968313595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 421364019819065938629426773 4937859607254678968313595)
        ·
          refine ⟨7406789410882018452470393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4937859607254678968313595 7406789410882018452470393)
          ·
            refine ⟨5555092058161513839352795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7406789410882018452470393 5555092058161513839352795)
            ·
              refine ⟨8332638087242270759029193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555092058161513839352795 8332638087242270759029193)
              ·
                refine ⟨6249478565431703069271895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8332638087242270759029193 6249478565431703069271895)
                ·
                  refine ⟨9374217848147554603907843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6249478565431703069271895 9374217848147554603907843)
                  ·
                    refine ⟨14061326772221331905861765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9374217848147554603907843 14061326772221331905861765)
                    ·
                      refine ⟨2636498769791499732349081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14061326772221331905861765 2636498769791499732349081)
                      ·
                        rfl

theorem cell23_5134563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5134563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134563 prefixEnd_5134563 := by exact prefixLift 5134563
  have htrace : WordTrace (prefixWord ++ tailWord_5134563) baseStart_5134563 baseEnd_5134563 := by
    simpa [prefixWord, tailWord_5134563, baseEnd_5134563] using wordTrace_append hprefix tailTrace_5134563
  have hstable : (prefixWord ++ tailWord_5134563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134563).length < 2 ^ (prefixWord ++ tailWord_5134563).sum := by decide
  have hdescent : baseEnd_5134563 < baseStart_5134563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134602 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_5134602 : Nat := 118140960795 + 5134602 * 2 ^ 59
def prefixEnd_5134602 : Nat := 4983230072969 + 3 ^ 40 * 5134602 * 2
def baseEnd_5134602 : Nat := 2636518795537025079761401

theorem tailTrace_5134602 : CollatzResearch.WordTrace tailWord_5134602 prefixEnd_5134602 2636518795537025079761401 := by
  unfold tailWord_5134602
  simp only [CollatzResearch.WordTrace]
  refine ⟨46818580036055337262881515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124849546762814232701017373 46818580036055337262881515)
  ·
    refine ⟨70227870054083005894322273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46818580036055337262881515 70227870054083005894322273)
    ·
      refine ⟨52670902540562254420741705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70227870054083005894322273 52670902540562254420741705)
      ·
        refine ⟨39503176905421690815556279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52670902540562254420741705 39503176905421690815556279)
        ·
          refine ⟨59254765358132536223334419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39503176905421690815556279 59254765358132536223334419)
          ·
            refine ⟨88882148037198804335001629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59254765358132536223334419 88882148037198804335001629)
            ·
              refine ⟨33330805513949551625625611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88882148037198804335001629 33330805513949551625625611)
              ·
                refine ⟨49996208270924327438438417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33330805513949551625625611 49996208270924327438438417)
                ·
                  refine ⟨37497156203193245578828813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49996208270924327438438417 37497156203193245578828813)
                  ·
                    refine ⟨14061433576197467092060805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37497156203193245578828813 14061433576197467092060805)
                    ·
                      refine ⟨2636518795537025079761401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14061433576197467092060805 2636518795537025079761401)
                      ·
                        rfl

theorem cell23_5134602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_5134602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134602 prefixEnd_5134602 := by exact prefixLift 5134602
  have htrace : WordTrace (prefixWord ++ tailWord_5134602) baseStart_5134602 baseEnd_5134602 := by
    simpa [prefixWord, tailWord_5134602, baseEnd_5134602] using wordTrace_append hprefix tailTrace_5134602
  have hstable : (prefixWord ++ tailWord_5134602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134602).length < 2 ^ (prefixWord ++ tailWord_5134602).sum := by decide
  have hdescent : baseEnd_5134602 < baseStart_5134602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134619 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 1, 4, 2]
def baseStart_5134619 : Nat := 118140960795 + 5134619 * 2 ^ 59
def prefixEnd_5134619 : Nat := 4983230072969 + 3 ^ 40 * 5134619 * 2
def baseEnd_5134619 : Nat := 2636527524708151513248823

theorem tailTrace_5134619 : CollatzResearch.WordTrace tailWord_5134619 prefixEnd_5134619 2636527524708151513248823 := by
  unfold tailWord_5134619
  simp only [CollatzResearch.WordTrace]
  refine ⟨187274940185159760954894911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124849960123439840636596607 187274940185159760954894911)
  ·
    refine ⟨280912410277739641432342367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187274940185159760954894911 280912410277739641432342367)
    ·
      refine ⟨421368615416609462148513551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280912410277739641432342367 421368615416609462148513551)
      ·
        refine ⟨632052923124914193222770327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421368615416609462148513551 632052923124914193222770327)
        ·
          refine ⟨948079384687371289834155491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632052923124914193222770327 948079384687371289834155491)
          ·
            refine ⟨1422119077031056934751233237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948079384687371289834155491 1422119077031056934751233237)
            ·
              refine ⟨33330915867915396908232029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1422119077031056934751233237 33330915867915396908232029)
              ·
                refine ⟨12499093450468273840587011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33330915867915396908232029 12499093450468273840587011)
                ·
                  refine ⟨18748640175702410760880517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12499093450468273840587011 18748640175702410760880517)
                  ·
                    refine ⟨3515370032944202017665097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18748640175702410760880517 3515370032944202017665097)
                    ·
                      refine ⟨2636527524708151513248823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515370032944202017665097 2636527524708151513248823)
                      ·
                        rfl

theorem cell23_5134619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 4, 2].length) (baseStart_5134619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134619 prefixEnd_5134619 := by exact prefixLift 5134619
  have htrace : WordTrace (prefixWord ++ tailWord_5134619) baseStart_5134619 baseEnd_5134619 := by
    simpa [prefixWord, tailWord_5134619, baseEnd_5134619] using wordTrace_append hprefix tailTrace_5134619
  have hstable : (prefixWord ++ tailWord_5134619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134619).length < 2 ^ (prefixWord ++ tailWord_5134619).sum := by decide
  have hdescent : baseEnd_5134619 < baseStart_5134619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134649 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5134649 : Nat := 118140960795 + 5134649 * 2 ^ 59
def prefixEnd_5134649 : Nat := 4983230072969 + 3 ^ 40 * 5134649 * 2
def baseEnd_5134649 : Nat := 2636542929127786395873685

theorem tailTrace_5134649 : CollatzResearch.WordTrace tailWord_5134649 prefixEnd_5134649 2636542929127786395873685 := by
  unfold tailWord_5134649
  simp only [CollatzResearch.WordTrace]
  refine ⟨187276034375051076078487001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124850689583367384052324667 187276034375051076078487001)
  ·
    refine ⟨140457025781288307058865251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187276034375051076078487001 140457025781288307058865251)
    ·
      refine ⟨210685538671932460588297877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140457025781288307058865251 210685538671932460588297877)
      ·
        refine ⟨9875884625246834090076463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 210685538671932460588297877 9875884625246834090076463)
        ·
          refine ⟨14813826937870251135114695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9875884625246834090076463 14813826937870251135114695)
          ·
            refine ⟨22220740406805376702672043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14813826937870251135114695 22220740406805376702672043)
            ·
              refine ⟨33331110610208065054008065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22220740406805376702672043 33331110610208065054008065)
              ·
                refine ⟨24998332957656048790506049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33331110610208065054008065 24998332957656048790506049)
                ·
                  refine ⟨18748749718242036592879537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24998332957656048790506049 18748749718242036592879537)
                  ·
                    refine ⟨14061562288681527444659653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18748749718242036592879537 14061562288681527444659653)
                    ·
                      refine ⟨2636542929127786395873685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14061562288681527444659653 2636542929127786395873685)
                      ·
                        rfl

theorem cell23_5134649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5134649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134649 prefixEnd_5134649 := by exact prefixLift 5134649
  have htrace : WordTrace (prefixWord ++ tailWord_5134649) baseStart_5134649 baseEnd_5134649 := by
    simpa [prefixWord, tailWord_5134649, baseEnd_5134649] using wordTrace_append hprefix tailTrace_5134649
  have hstable : (prefixWord ++ tailWord_5134649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134649).length < 2 ^ (prefixWord ++ tailWord_5134649).sum := by decide
  have hdescent : baseEnd_5134649 < baseStart_5134649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134659 : List Nat := [1, 1, 1, 3, 1, 3, 4, 4, 5]
def baseStart_5134659 : Nat := 118140960795 + 5134659 * 2 ^ 59
def prefixEnd_5134659 : Nat := 4983230072969 + 3 ^ 40 * 5134659 * 2
def baseEnd_5134659 : Nat := 292949784881592372972071

theorem tailTrace_5134659 : CollatzResearch.WordTrace tailWord_5134659 prefixEnd_5134659 292949784881592372972071 := by
  unfold tailWord_5134659
  simp only [CollatzResearch.WordTrace]
  refine ⟨187276399105014847786351031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124850932736676565190900687 187276399105014847786351031)
  ·
    refine ⟨280914598657522271679526547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187276399105014847786351031 280914598657522271679526547)
    ·
      refine ⟨421371897986283407519289821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280914598657522271679526547 421371897986283407519289821)
      ·
        refine ⟨158014461744856277819733683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421371897986283407519289821 158014461744856277819733683)
        ·
          refine ⟨237021692617284416729600525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158014461744856277819733683 237021692617284416729600525)
          ·
            refine ⟨88883134731481656273600197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237021692617284416729600525 88883134731481656273600197)
            ·
              refine ⟨16665587762152810551300037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88883134731481656273600197 16665587762152810551300037)
              ·
                refine ⟨3124797705403651978368757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16665587762152810551300037 3124797705403651978368757)
                ·
                  refine ⟨292949784881592372972071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3124797705403651978368757 292949784881592372972071)
                  ·
                    rfl

theorem cell23_5134659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 5].length) (baseStart_5134659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134659 prefixEnd_5134659 := by exact prefixLift 5134659
  have htrace : WordTrace (prefixWord ++ tailWord_5134659) baseStart_5134659 baseEnd_5134659 := by
    simpa [prefixWord, tailWord_5134659, baseEnd_5134659] using wordTrace_append hprefix tailTrace_5134659
  have hstable : (prefixWord ++ tailWord_5134659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134659).length < 2 ^ (prefixWord ++ tailWord_5134659).sum := by decide
  have hdescent : baseEnd_5134659 < baseStart_5134659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134672 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 1, 7]
def baseStart_5134672 : Nat := 118140960795 + 5134672 * 2 ^ 59
def prefixEnd_5134672 : Nat := 4983230072969 + 3 ^ 40 * 5134672 * 2
def baseEnd_5134672 : Nat := 878851579727613268628693

theorem tailTrace_5134672 : CollatzResearch.WordTrace tailWord_5134672 prefixEnd_5134672 878851579727613268628693 := by
  unfold tailWord_5134672
  simp only [CollatzResearch.WordTrace]
  refine ⟨93638436626983875503287135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124851248835978500671049513 93638436626983875503287135)
  ·
    refine ⟨140457654940475813254930703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93638436626983875503287135 140457654940475813254930703)
    ·
      refine ⟨210686482410713719882396055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140457654940475813254930703 210686482410713719882396055)
      ·
        refine ⟨316029723616070579823594083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210686482410713719882396055 316029723616070579823594083)
        ·
          refine ⟨474044585424105869735391125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316029723616070579823594083 474044585424105869735391125)
          ·
            refine ⟨22220839941754962643846459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 474044585424105869735391125 22220839941754962643846459)
            ·
              refine ⟨33331259912632443965769689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22220839941754962643846459 33331259912632443965769689)
              ·
                refine ⟨24998444934474332974327267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33331259912632443965769689 24998444934474332974327267)
                ·
                  refine ⟨37497667401711499461490901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24998444934474332974327267 37497667401711499461490901)
                  ·
                    refine ⟨878851579727613268628693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37497667401711499461490901 878851579727613268628693)
                    ·
                      rfl

theorem cell23_5134672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_5134672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134672 prefixEnd_5134672 := by exact prefixLift 5134672
  have htrace : WordTrace (prefixWord ++ tailWord_5134672) baseStart_5134672 baseEnd_5134672 := by
    simpa [prefixWord, tailWord_5134672, baseEnd_5134672] using wordTrace_append hprefix tailTrace_5134672
  have hstable : (prefixWord ++ tailWord_5134672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134672).length < 2 ^ (prefixWord ++ tailWord_5134672).sum := by decide
  have hdescent : baseEnd_5134672 < baseStart_5134672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134682 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_5134682 : Nat := 118140960795 + 5134682 * 2 ^ 59
def prefixEnd_5134682 : Nat := 4983230072969 + 3 ^ 40 * 5134682 * 2
def baseEnd_5134682 : Nat := 2636559873989384766761033

theorem tailTrace_5134682 : CollatzResearch.WordTrace tailWord_5134682 prefixEnd_5134682 2636559873989384766761033 := by
  unfold tailWord_5134682
  simp only [CollatzResearch.WordTrace]
  refine ⟨46819309495982880678609575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124851491989287681809625533 46819309495982880678609575)
  ·
    refine ⟨70228964243974321017914363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46819309495982880678609575 70228964243974321017914363)
    ·
      refine ⟨105343446365961481526871545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70228964243974321017914363 105343446365961481526871545)
      ·
        refine ⟨79007584774471111145153659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105343446365961481526871545 79007584774471111145153659)
        ·
          refine ⟨118511377161706666717730489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79007584774471111145153659 118511377161706666717730489)
          ·
            refine ⟨88883532871280000038297867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118511377161706666717730489 88883532871280000038297867)
            ·
              refine ⟨133325299306920000057446801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88883532871280000038297867 133325299306920000057446801)
              ·
                refine ⟨99993974480190000043085101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133325299306920000057446801 99993974480190000043085101)
                ·
                  refine ⟨37497740430071250016156913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99993974480190000043085101 37497740430071250016156913)
                  ·
                    refine ⟨28123305322553437512117685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37497740430071250016156913 28123305322553437512117685)
                    ·
                      refine ⟨2636559873989384766761033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28123305322553437512117685 2636559873989384766761033)
                      ·
                        rfl

theorem cell23_5134682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_5134682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134682 prefixEnd_5134682 := by exact prefixLift 5134682
  have htrace : WordTrace (prefixWord ++ tailWord_5134682) baseStart_5134682 baseEnd_5134682 := by
    simpa [prefixWord, tailWord_5134682, baseEnd_5134682] using wordTrace_append hprefix tailTrace_5134682
  have hstable : (prefixWord ++ tailWord_5134682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134682).length < 2 ^ (prefixWord ++ tailWord_5134682).sum := by decide
  have hdescent : baseEnd_5134682 < baseStart_5134682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134710 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_5134710 : Nat := 118140960795 + 5134710 * 2 ^ 59
def prefixEnd_5134710 : Nat := 4983230072969 + 3 ^ 40 * 5134710 * 2
def baseEnd_5134710 : Nat := 292952694605301184134545

theorem tailTrace_5134710 : CollatzResearch.WordTrace tailWord_5134710 prefixEnd_5134710 292952694605301184134545 := by
  unfold tailWord_5134710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11704891201739380218528599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124852172818553388997638389 11704891201739380218528599)
  ·
    refine ⟨17557336802609070327792899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11704891201739380218528599 17557336802609070327792899)
    ·
      refine ⟨26336005203913605491689349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17557336802609070327792899 26336005203913605491689349)
      ·
        refine ⟨4938000975733801029691753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26336005203913605491689349 4938000975733801029691753)
        ·
          refine ⟨3703500731800350772268815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4938000975733801029691753 3703500731800350772268815)
          ·
            refine ⟨5555251097700526158403223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703500731800350772268815 5555251097700526158403223)
            ·
              refine ⟨8332876646550789237604835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555251097700526158403223 8332876646550789237604835)
              ·
                refine ⟨12499314969826183856407253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8332876646550789237604835 12499314969826183856407253)
                ·
                  refine ⟨292952694605301184134545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12499314969826183856407253 292952694605301184134545)
                  ·
                    rfl

theorem cell23_5134710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_5134710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134710 prefixEnd_5134710 := by exact prefixLift 5134710
  have htrace : WordTrace (prefixWord ++ tailWord_5134710) baseStart_5134710 baseEnd_5134710 := by
    simpa [prefixWord, tailWord_5134710, baseEnd_5134710] using wordTrace_append hprefix tailTrace_5134710
  have hstable : (prefixWord ++ tailWord_5134710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134710).length < 2 ^ (prefixWord ++ tailWord_5134710).sum := by decide
  have hdescent : baseEnd_5134710 < baseStart_5134710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134746 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_5134746 : Nat := 118140960795 + 5134746 * 2 ^ 59
def prefixEnd_5134746 : Nat := 4983230072969 + 3 ^ 40 * 5134746 * 2
def baseEnd_5134746 : Nat := 2636592736751272516360739

theorem tailTrace_5134746 : CollatzResearch.WordTrace tailWord_5134746 prefixEnd_5134746 2636592736751272516360739 := by
  unfold tailWord_5134746
  simp only [CollatzResearch.WordTrace]
  refine ⟨46819893063924915411192023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124853048170466441096512061 46819893063924915411192023)
  ·
    refine ⟨70229839595887373116788035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46819893063924915411192023 70229839595887373116788035)
    ·
      refine ⟨105344759393831059675182053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70229839595887373116788035 105344759393831059675182053)
      ·
        refine ⟨19752142386343323689096635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105344759393831059675182053 19752142386343323689096635)
        ·
          refine ⟨29628213579514985533644953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19752142386343323689096635 29628213579514985533644953)
          ·
            refine ⟨22221160184636239150233715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29628213579514985533644953 22221160184636239150233715)
            ·
              refine ⟨33331740276954358725350573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22221160184636239150233715 33331740276954358725350573)
              ·
                refine ⟨12499402603857884522006465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33331740276954358725350573 12499402603857884522006465)
                ·
                  refine ⟨9374551952893413391504849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12499402603857884522006465 9374551952893413391504849)
                  ·
                    refine ⟨7030913964670060043628637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9374551952893413391504849 7030913964670060043628637)
                    ·
                      refine ⟨2636592736751272516360739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7030913964670060043628637 2636592736751272516360739)
                      ·
                        rfl

theorem cell23_5134746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_5134746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134746 prefixEnd_5134746 := by exact prefixLift 5134746
  have htrace : WordTrace (prefixWord ++ tailWord_5134746) baseStart_5134746 baseEnd_5134746 := by
    simpa [prefixWord, tailWord_5134746, baseEnd_5134746] using wordTrace_append hprefix tailTrace_5134746
  have hstable : (prefixWord ++ tailWord_5134746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134746).length < 2 ^ (prefixWord ++ tailWord_5134746).sum := by decide
  have hdescent : baseEnd_5134746 < baseStart_5134746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134776 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 3, 1, 3]
def baseStart_5134776 : Nat := 118140960795 + 5134776 * 2 ^ 59
def prefixEnd_5134776 : Nat := 4983230072969 + 3 ^ 40 * 5134776 * 2
def baseEnd_5134776 : Nat := 2636608141170907398985601

theorem tailTrace_5134776 : CollatzResearch.WordTrace tailWord_5134776 prefixEnd_5134776 2636608141170907398985601 := by
  unfold tailWord_5134776
  simp only [CollatzResearch.WordTrace]
  refine ⟨93640333222795488384180091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124853777630393984512240121 93640333222795488384180091)
  ·
    refine ⟨140460499834193232576270137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93640333222795488384180091 140460499834193232576270137)
    ·
      refine ⟨105345374875644924432202603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140460499834193232576270137 105345374875644924432202603)
      ·
        refine ⟨158018062313467386648303905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105345374875644924432202603 158018062313467386648303905)
        ·
          refine ⟨118513546735100539986227929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158018062313467386648303905 118513546735100539986227929)
          ·
            refine ⟨88885160051325404989670947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118513546735100539986227929 88885160051325404989670947)
            ·
              refine ⟨133327740076988107484506421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88885160051325404989670947 133327740076988107484506421)
              ·
                refine ⟨12499475632217635076672477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133327740076988107484506421 12499475632217635076672477)
                ·
                  refine ⟨4687303362081613153752179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12499475632217635076672477 4687303362081613153752179)
                  ·
                    refine ⟨7030955043122419730628269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4687303362081613153752179 7030955043122419730628269)
                    ·
                      refine ⟨2636608141170907398985601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7030955043122419730628269 2636608141170907398985601)
                      ·
                        rfl

theorem cell23_5134776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_5134776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134776 prefixEnd_5134776 := by exact prefixLift 5134776
  have htrace : WordTrace (prefixWord ++ tailWord_5134776) baseStart_5134776 baseEnd_5134776 := by
    simpa [prefixWord, tailWord_5134776, baseEnd_5134776] using wordTrace_append hprefix tailTrace_5134776
  have hstable : (prefixWord ++ tailWord_5134776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134776).length < 2 ^ (prefixWord ++ tailWord_5134776).sum := by decide
  have hdescent : baseEnd_5134776 < baseStart_5134776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134809 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 1, 6]
def baseStart_5134809 : Nat := 118140960795 + 5134809 * 2 ^ 59
def prefixEnd_5134809 : Nat := 4983230072969 + 3 ^ 40 * 5134809 * 2
def baseEnd_5134809 : Nat := 878875028677501923290983

theorem tailTrace_5134809 : CollatzResearch.WordTrace tailWord_5134809 prefixEnd_5134809 878875028677501923290983 := by
  unfold tailWord_5134809
  simp only [CollatzResearch.WordTrace]
  refine ⟨187281870054471423404311481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124854580036314282269540987 187281870054471423404311481)
  ·
    refine ⟨140461402540853567553233611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187281870054471423404311481 140461402540853567553233611)
    ·
      refine ⟨210692103811280351329850417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140461402540853567553233611 210692103811280351329850417)
      ·
        refine ⟨158019077858460263497387813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210692103811280351329850417 158019077858460263497387813)
        ·
          refine ⟨29628577098461299405760215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158019077858460263497387813 29628577098461299405760215)
          ·
            refine ⟨44442865647691949108640323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29628577098461299405760215 44442865647691949108640323)
            ·
              refine ⟨66664298471537923662960485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44442865647691949108640323 66664298471537923662960485)
              ·
                refine ⟨12499555963413360686805091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66664298471537923662960485 12499555963413360686805091)
                ·
                  refine ⟨18749333945120041030207637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12499555963413360686805091 18749333945120041030207637)
                  ·
                    refine ⟨878875028677501923290983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18749333945120041030207637 878875028677501923290983)
                    ·
                      rfl

theorem cell23_5134809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_5134809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134809 prefixEnd_5134809 := by exact prefixLift 5134809
  have htrace : WordTrace (prefixWord ++ tailWord_5134809) baseStart_5134809 baseEnd_5134809 := by
    simpa [prefixWord, tailWord_5134809, baseEnd_5134809] using wordTrace_append hprefix tailTrace_5134809
  have hstable : (prefixWord ++ tailWord_5134809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134809).length < 2 ^ (prefixWord ++ tailWord_5134809).sum := by decide
  have hdescent : baseEnd_5134809 < baseStart_5134809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134810 : List Nat := [3, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3]
def baseStart_5134810 : Nat := 118140960795 + 5134810 * 2 ^ 59
def prefixEnd_5134810 : Nat := 4983230072969 + 3 ^ 40 * 5134810 * 2
def baseEnd_5134810 : Nat := 2636625599513160265960445

theorem tailTrace_5134810 : CollatzResearch.WordTrace tailWord_5134810 prefixEnd_5134810 2636625599513160265960445 := by
  unfold tailWord_5134810
  simp only [CollatzResearch.WordTrace]
  refine ⟨46820476631866950143774471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124854604351645200383398589 46820476631866950143774471)
  ·
    refine ⟨70230714947800425215661707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46820476631866950143774471 70230714947800425215661707)
    ·
      refine ⟨105346072421700637823492561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70230714947800425215661707 105346072421700637823492561)
      ·
        refine ⟨79009554316275478367619421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105346072421700637823492561 79009554316275478367619421)
        ·
          refine ⟨29628582868603304387857283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79009554316275478367619421 29628582868603304387857283)
          ·
            refine ⟨44442874302904956581785925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29628582868603304387857283 44442874302904956581785925)
            ·
              refine ⟨8333038931794679359084861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44442874302904956581785925 8333038931794679359084861)
              ·
                refine ⟨3124889599423004759656823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8333038931794679359084861 3124889599423004759656823)
                ·
                  refine ⟨4687334399134507139485235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124889599423004759656823 4687334399134507139485235)
                  ·
                    refine ⟨7031001598701760709227853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4687334399134507139485235 7031001598701760709227853)
                    ·
                      refine ⟨2636625599513160265960445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031001598701760709227853 2636625599513160265960445)
                      ·
                        rfl

theorem cell23_5134810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_5134810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134810 prefixEnd_5134810 := by exact prefixLift 5134810
  have htrace : WordTrace (prefixWord ++ tailWord_5134810) baseStart_5134810 baseEnd_5134810 := by
    simpa [prefixWord, tailWord_5134810, baseEnd_5134810] using wordTrace_append hprefix tailTrace_5134810
  have hstable : (prefixWord ++ tailWord_5134810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134810).length < 2 ^ (prefixWord ++ tailWord_5134810).sum := by decide
  have hdescent : baseEnd_5134810 < baseStart_5134810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134816 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 4]
def baseStart_5134816 : Nat := 118140960795 + 5134816 * 2 ^ 59
def prefixEnd_5134816 : Nat := 4983230072969 + 3 ^ 40 * 5134816 * 2
def baseEnd_5134816 : Nat := 2636628680397087242485417

theorem tailTrace_5134816 : CollatzResearch.WordTrace tailWord_5134816 prefixEnd_5134816 2636628680397087242485417 := by
  unfold tailWord_5134816
  simp only [CollatzResearch.WordTrace]
  refine ⟨93641062682723031799908151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124854750243630709066544201 93641062682723031799908151)
  ·
    refine ⟨140461594024084547699862227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93641062682723031799908151 140461594024084547699862227)
    ·
      refine ⟨210692391036126821549793341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140461594024084547699862227 210692391036126821549793341)
      ·
        refine ⟨79009646638547558081172503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210692391036126821549793341 79009646638547558081172503)
        ·
          refine ⟨118514469957821337121758755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79009646638547558081172503 118514469957821337121758755)
          ·
            refine ⟨177771704936732005682638133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118514469957821337121758755 177771704936732005682638133)
            ·
              refine ⟨16666097337818625532747325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177771704936732005682638133 16666097337818625532747325)
              ·
                refine ⟨6249786501681984574780247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16666097337818625532747325 6249786501681984574780247)
                ·
                  refine ⟨9374679752522976862170371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6249786501681984574780247 9374679752522976862170371)
                  ·
                    refine ⟨14062019628784465293255557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9374679752522976862170371 14062019628784465293255557)
                    ·
                      refine ⟨2636628680397087242485417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14062019628784465293255557 2636628680397087242485417)
                      ·
                        rfl

theorem cell23_5134816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_5134816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134816 prefixEnd_5134816 := by exact prefixLift 5134816
  have htrace : WordTrace (prefixWord ++ tailWord_5134816) baseStart_5134816 baseEnd_5134816 := by
    simpa [prefixWord, tailWord_5134816, baseEnd_5134816] using wordTrace_append hprefix tailTrace_5134816
  have hstable : (prefixWord ++ tailWord_5134816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134816).length < 2 ^ (prefixWord ++ tailWord_5134816).sum := by decide
  have hdescent : baseEnd_5134816 < baseStart_5134816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134861 : List Nat := [1, 7, 1, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5134861 : Nat := 118140960795 + 5134861 * 2 ^ 59
def prefixEnd_5134861 : Nat := 4983230072969 + 3 ^ 40 * 5134861 * 2
def baseEnd_5134861 : Nat := 2636651787026539566422711

theorem tailTrace_5134861 : CollatzResearch.WordTrace tailWord_5134861 prefixEnd_5134861 2636651787026539566422711 := by
  unfold tailWord_5134861
  simp only [CollatzResearch.WordTrace]
  refine ⟨187283766650283036285204437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124855844433522024190136291 187283766650283036285204437)
  ·
    refine ⟨4389463280866008662934479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 187283766650283036285204437 4389463280866008662934479)
    ·
      refine ⟨6584194921299012994401719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4389463280866008662934479 6584194921299012994401719)
      ·
        refine ⟨9876292381948519491602579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6584194921299012994401719 9876292381948519491602579)
        ·
          refine ⟨14814438572922779237403869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9876292381948519491602579 14814438572922779237403869)
          ·
            refine ⟨5555414464846042214026451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14814438572922779237403869 5555414464846042214026451)
            ·
              refine ⟨8333121697269063321039677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555414464846042214026451 8333121697269063321039677)
              ·
                refine ⟨3124920636475898745389879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8333121697269063321039677 3124920636475898745389879)
                ·
                  refine ⟨4687380954713848118084819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124920636475898745389879 4687380954713848118084819)
                  ·
                    refine ⟨7031071432070772177127229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4687380954713848118084819 7031071432070772177127229)
                    ·
                      refine ⟨2636651787026539566422711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031071432070772177127229 2636651787026539566422711)
                      ·
                        rfl

theorem cell23_5134861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5134861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134861 prefixEnd_5134861 := by exact prefixLift 5134861
  have htrace : WordTrace (prefixWord ++ tailWord_5134861) baseStart_5134861 baseEnd_5134861 := by
    simpa [prefixWord, tailWord_5134861, baseEnd_5134861] using wordTrace_append hprefix tailTrace_5134861
  have hstable : (prefixWord ++ tailWord_5134861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134861).length < 2 ^ (prefixWord ++ tailWord_5134861).sum := by decide
  have hdescent : baseEnd_5134861 < baseStart_5134861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134879 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_5134879 : Nat := 118140960795 + 5134879 * 2 ^ 59
def prefixEnd_5134879 : Nat := 4983230072969 + 3 ^ 40 * 5134879 * 2
def baseEnd_5134879 : Nat := 2636661029678320495997627

theorem tailTrace_5134879 : CollatzResearch.WordTrace tailWord_5134879 prefixEnd_5134879 2636661029678320495997627 := by
  unfold tailWord_5134879
  simp only [CollatzResearch.WordTrace]
  refine ⟨187284423164217825359359691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124856282109478550239573127 187284423164217825359359691)
  ·
    refine ⟨280926634746326738039039537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187284423164217825359359691 280926634746326738039039537)
    ·
      refine ⟨210694976059745053529279653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280926634746326738039039537 210694976059745053529279653)
      ·
        refine ⟨39505308011202197536739935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210694976059745053529279653 39505308011202197536739935)
        ·
          refine ⟨59257962016803296305109903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39505308011202197536739935 59257962016803296305109903)
          ·
            refine ⟨88886943025204944457664855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59257962016803296305109903 88886943025204944457664855)
            ·
              refine ⟨133330414537807416686497283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88886943025204944457664855 133330414537807416686497283)
              ·
                refine ⟨199995621806711125029745925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133330414537807416686497283 199995621806711125029745925)
                ·
                  refine ⟨37499179088758335943077361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199995621806711125029745925 37499179088758335943077361)
                  ·
                    refine ⟨28124384316568751957308021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37499179088758335943077361 28124384316568751957308021)
                    ·
                      refine ⟨2636661029678320495997627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28124384316568751957308021 2636661029678320495997627)
                      ·
                        rfl

theorem cell23_5134879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_5134879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134879 prefixEnd_5134879 := by exact prefixLift 5134879
  have htrace : WordTrace (prefixWord ++ tailWord_5134879) baseStart_5134879 baseEnd_5134879 := by
    simpa [prefixWord, tailWord_5134879, baseEnd_5134879] using wordTrace_append hprefix tailTrace_5134879
  have hstable : (prefixWord ++ tailWord_5134879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134879).length < 2 ^ (prefixWord ++ tailWord_5134879).sum := by decide
  have hdescent : baseEnd_5134879 < baseStart_5134879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134883 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 3]
def baseStart_5134883 : Nat := 118140960795 + 5134883 * 2 ^ 59
def prefixEnd_5134883 : Nat := 4983230072969 + 3 ^ 40 * 5134883 * 2
def baseEnd_5134883 : Nat := 2636663083600938480347609

theorem tailTrace_5134883 : CollatzResearch.WordTrace tailWord_5134883 prefixEnd_5134883 2636663083600938480347609 := by
  unfold tailWord_5134883
  simp only [CollatzResearch.WordTrace]
  refine ⟨187284569056203334042505303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124856379370802222695003535 187284569056203334042505303)
  ·
    refine ⟨280926853584305001063757955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187284569056203334042505303 280926853584305001063757955)
    ·
      refine ⟨421390280376457501595636933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280926853584305001063757955 421390280376457501595636933)
      ·
        refine ⟨79010677570585781549181925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 421390280376457501595636933 79010677570585781549181925)
        ·
          refine ⟨14814502044484834040471611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79010677570585781549181925 14814502044484834040471611)
          ·
            refine ⟨22221753066727251060707417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14814502044484834040471611 22221753066727251060707417)
            ·
              refine ⟨16666314800045438295530563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22221753066727251060707417 16666314800045438295530563)
              ·
                refine ⟨24999472200068157443295845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16666314800045438295530563 24999472200068157443295845)
                ·
                  refine ⟨4687401037512779520617971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24999472200068157443295845 4687401037512779520617971)
                  ·
                    refine ⟨7031101556269169280926957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4687401037512779520617971 7031101556269169280926957)
                    ·
                      refine ⟨2636663083600938480347609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031101556269169280926957 2636663083600938480347609)
                      ·
                        rfl

theorem cell23_5134883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_5134883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134883 prefixEnd_5134883 := by exact prefixLift 5134883
  have htrace : WordTrace (prefixWord ++ tailWord_5134883) baseStart_5134883 baseEnd_5134883 := by
    simpa [prefixWord, tailWord_5134883, baseEnd_5134883] using wordTrace_append hprefix tailTrace_5134883
  have hstable : (prefixWord ++ tailWord_5134883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134883).length < 2 ^ (prefixWord ++ tailWord_5134883).sum := by decide
  have hdescent : baseEnd_5134883 < baseStart_5134883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134884 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5134884 : Nat := 118140960795 + 5134884 * 2 ^ 59
def prefixEnd_5134884 : Nat := 4983230072969 + 3 ^ 40 * 5134884 * 2
def baseEnd_5134884 : Nat := 2636663597081592976435105

theorem tailTrace_5134884 : CollatzResearch.WordTrace tailWord_5134884 prefixEnd_5134884 2636663597081592976435105 := by
  unfold tailWord_5134884
  simp only [CollatzResearch.WordTrace]
  refine ⟨93642302764599855606645853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124856403686133140808861137 93642302764599855606645853)
  ·
    refine ⟨35115863536724945852492195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93642302764599855606645853 35115863536724945852492195)
    ·
      refine ⟨52673795305087418778738293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35115863536724945852492195 52673795305087418778738293)
      ·
        refine ⟨4938168309851945510506715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52673795305087418778738293 4938168309851945510506715)
        ·
          refine ⟨7407252464777918265760073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4938168309851945510506715 7407252464777918265760073)
          ·
            refine ⟨5555439348583438699320055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7407252464777918265760073 5555439348583438699320055)
            ·
              refine ⟨8333159022875158048980083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555439348583438699320055 8333159022875158048980083)
              ·
                refine ⟨12499738534312737073470125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8333159022875158048980083 12499738534312737073470125)
                ·
                  refine ⟨4687401950367276402551297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12499738534312737073470125 4687401950367276402551297)
                  ·
                    refine ⟨3515551462775457301913473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4687401950367276402551297 3515551462775457301913473)
                    ·
                      refine ⟨2636663597081592976435105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515551462775457301913473 2636663597081592976435105)
                      ·
                        rfl

theorem cell23_5134884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5134884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134884 prefixEnd_5134884 := by exact prefixLift 5134884
  have htrace : WordTrace (prefixWord ++ tailWord_5134884) baseStart_5134884 baseEnd_5134884 := by
    simpa [prefixWord, tailWord_5134884, baseEnd_5134884] using wordTrace_append hprefix tailTrace_5134884
  have hstable : (prefixWord ++ tailWord_5134884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134884).length < 2 ^ (prefixWord ++ tailWord_5134884).sum := by decide
  have hdescent : baseEnd_5134884 < baseStart_5134884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134894 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_5134894 : Nat := 118140960795 + 5134894 * 2 ^ 59
def prefixEnd_5134894 : Nat := 4983230072969 + 3 ^ 40 * 5134894 * 2
def baseEnd_5134894 : Nat := 878889577296045979103353

theorem tailTrace_5134894 : CollatzResearch.WordTrace tailWord_5134894 prefixEnd_5134894 878889577296045979103353 := by
  unfold tailWord_5134894
  simp only [CollatzResearch.WordTrace]
  refine ⟨23410621282395435365144467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124856646839442321947437157 23410621282395435365144467)
  ·
    refine ⟨35115931923593153047716701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23410621282395435365144467 35115931923593153047716701)
    ·
      refine ⟨13168474471347432392893763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35115931923593153047716701 13168474471347432392893763)
      ·
        refine ⟨19752711707021148589340645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13168474471347432392893763 19752711707021148589340645)
        ·
          refine ⟨3703633445066465360501371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19752711707021148589340645 3703633445066465360501371)
          ·
            refine ⟨5555450167599698040752057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703633445066465360501371 5555450167599698040752057)
            ·
              refine ⟨4166587625699773530564043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5555450167599698040752057 4166587625699773530564043)
              ·
                refine ⟨6249881438549660295846065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166587625699773530564043 6249881438549660295846065)
                ·
                  refine ⟨4687411078912245221884549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6249881438549660295846065 4687411078912245221884549)
                  ·
                    refine ⟨878889577296045979103353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687411078912245221884549 878889577296045979103353)
                    ·
                      rfl

theorem cell23_5134894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_5134894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134894 prefixEnd_5134894 := by exact prefixLift 5134894
  have htrace : WordTrace (prefixWord ++ tailWord_5134894) baseStart_5134894 baseEnd_5134894 := by
    simpa [prefixWord, tailWord_5134894, baseEnd_5134894] using wordTrace_append hprefix tailTrace_5134894
  have hstable : (prefixWord ++ tailWord_5134894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134894).length < 2 ^ (prefixWord ++ tailWord_5134894).sum := by decide
  have hdescent : baseEnd_5134894 < baseStart_5134894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134899 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 1, 8]
def baseStart_5134899 : Nat := 118140960795 + 5134899 * 2 ^ 59
def prefixEnd_5134899 : Nat := 4983230072969 + 3 ^ 40 * 5134899 * 2
def baseEnd_5134899 : Nat := 878890433097136805915845

theorem tailTrace_5134899 : CollatzResearch.WordTrace tailWord_5134899 prefixEnd_5134899 878890433097136805915845 := by
  unfold tailWord_5134899
  simp only [CollatzResearch.WordTrace]
  refine ⟨187285152624145368775087751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124856768416096912516725167 187285152624145368775087751)
  ·
    refine ⟨280927728936218053162631627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187285152624145368775087751 280927728936218053162631627)
    ·
      refine ⟨421391593404327079743947441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280927728936218053162631627 421391593404327079743947441)
      ·
        refine ⟨316043695053245309807960581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421391593404327079743947441 316043695053245309807960581)
        ·
          refine ⟨59258192822483495588992609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 316043695053245309807960581 59258192822483495588992609)
          ·
            refine ⟨44443644616862621691744457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59258192822483495588992609 44443644616862621691744457)
            ·
              refine ⟨33332733462646966268808343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44443644616862621691744457 33332733462646966268808343)
              ·
                refine ⟨49999100193970449403212515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33332733462646966268808343 49999100193970449403212515)
                ·
                  refine ⟨74998650290955674104818773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49999100193970449403212515 74998650290955674104818773)
                  ·
                    refine ⟨878890433097136805915845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74998650290955674104818773 878890433097136805915845)
                    ·
                      rfl

theorem cell23_5134899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 8].length) (baseStart_5134899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134899 prefixEnd_5134899 := by exact prefixLift 5134899
  have htrace : WordTrace (prefixWord ++ tailWord_5134899) baseStart_5134899 baseEnd_5134899 := by
    simpa [prefixWord, tailWord_5134899, baseEnd_5134899] using wordTrace_append hprefix tailTrace_5134899
  have hstable : (prefixWord ++ tailWord_5134899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134899).length < 2 ^ (prefixWord ++ tailWord_5134899).sum := by decide
  have hdescent : baseEnd_5134899 < baseStart_5134899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134923 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 6, 2, 2]
def baseStart_5134923 : Nat := 118140960795 + 5134923 * 2 ^ 59
def prefixEnd_5134923 : Nat := 4983230072969 + 3 ^ 40 * 5134923 * 2
def baseEnd_5134923 : Nat := 2636683622827118323847425

theorem tailTrace_5134923 : CollatzResearch.WordTrace tailWord_5134923 prefixEnd_5134923 2636683622827118323847425 := by
  unfold tailWord_5134923
  simp only [CollatzResearch.WordTrace]
  refine ⟨187286027976058420873961423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124857351984038947249307615 187286027976058420873961423)
  ·
    refine ⟨280929041964087631310942135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187286027976058420873961423 280929041964087631310942135)
    ·
      refine ⟨421393562946131446966413203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280929041964087631310942135 421393562946131446966413203)
      ·
        refine ⟨632090344419197170449619805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421393562946131446966413203 632090344419197170449619805)
        ·
          refine ⟨237033879157198938918607427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 632090344419197170449619805 237033879157198938918607427)
          ·
            refine ⟨355550818735798408377911141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237033879157198938918607427 355550818735798408377911141)
            ·
              refine ⟨66665778512962201570858339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 355550818735798408377911141 66665778512962201570858339)
              ·
                refine ⟨99998667769443302356287509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66665778512962201570858339 99998667769443302356287509)
                ·
                  refine ⟨4687437551692654797950977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99998667769443302356287509 4687437551692654797950977)
                  ·
                    refine ⟨3515578163769491098463233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4687437551692654797950977 3515578163769491098463233)
                    ·
                      refine ⟨2636683622827118323847425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515578163769491098463233 2636683622827118323847425)
                      ·
                        rfl

theorem cell23_5134923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 2, 2].length) (baseStart_5134923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134923 prefixEnd_5134923 := by exact prefixLift 5134923
  have htrace : WordTrace (prefixWord ++ tailWord_5134923) baseStart_5134923 baseEnd_5134923 := by
    simpa [prefixWord, tailWord_5134923, baseEnd_5134923] using wordTrace_append hprefix tailTrace_5134923
  have hstable : (prefixWord ++ tailWord_5134923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134923).length < 2 ^ (prefixWord ++ tailWord_5134923).sum := by decide
  have hdescent : baseEnd_5134923 < baseStart_5134923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134926 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_5134926 : Nat := 118140960795 + 5134926 * 2 ^ 59
def prefixEnd_5134926 : Nat := 4983230072969 + 3 ^ 40 * 5134926 * 2
def baseEnd_5134926 : Nat := 2636685163269081812109911

theorem tailTrace_5134926 : CollatzResearch.WordTrace tailWord_5134926 prefixEnd_5134926 2636685163269081812109911 := by
  unfold tailWord_5134926
  simp only [CollatzResearch.WordTrace]
  refine ⟨23410767174380944048290079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124857424930031701590880421 23410767174380944048290079)
  ·
    refine ⟨35116150761571416072435119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23410767174380944048290079 35116150761571416072435119)
    ·
      refine ⟨52674226142357124108652679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35116150761571416072435119 52674226142357124108652679)
      ·
        refine ⟨79011339213535686162979019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52674226142357124108652679 79011339213535686162979019)
        ·
          refine ⟨118517008820303529244468529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79011339213535686162979019 118517008820303529244468529)
          ·
            refine ⟨88887756615227646933351397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118517008820303529244468529 88887756615227646933351397)
            ·
              refine ⟨16666454365355183800003387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88887756615227646933351397 16666454365355183800003387)
              ·
                refine ⟨24999681548032775700005081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16666454365355183800003387 24999681548032775700005081)
                ·
                  refine ⟨18749761161024581775003811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24999681548032775700005081 18749761161024581775003811)
                  ·
                    refine ⟨28124641741536872662505717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18749761161024581775003811 28124641741536872662505717)
                    ·
                      refine ⟨2636685163269081812109911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28124641741536872662505717 2636685163269081812109911)
                      ·
                        rfl

theorem cell23_5134926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_5134926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134926 prefixEnd_5134926 := by exact prefixLift 5134926
  have htrace : WordTrace (prefixWord ++ tailWord_5134926) baseStart_5134926 baseEnd_5134926 := by
    simpa [prefixWord, tailWord_5134926, baseEnd_5134926] using wordTrace_append hprefix tailTrace_5134926
  have hstable : (prefixWord ++ tailWord_5134926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134926).length < 2 ^ (prefixWord ++ tailWord_5134926).sum := by decide
  have hdescent : baseEnd_5134926 < baseStart_5134926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134956 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_5134956 : Nat := 118140960795 + 5134956 * 2 ^ 59
def prefixEnd_5134956 : Nat := 4983230072969 + 3 ^ 40 * 5134956 * 2
def baseEnd_5134956 : Nat := 2636700567688716694734773

theorem tailTrace_5134956 : CollatzResearch.WordTrace tailWord_5134956 prefixEnd_5134956 2636700567688716694734773 := by
  unfold tailWord_5134956
  simp only [CollatzResearch.WordTrace]
  refine ⟨93643615792469433754956361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124858154389959245006608481 93643615792469433754956361)
  ·
    refine ⟨70232711844352075316217271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93643615792469433754956361 70232711844352075316217271)
    ·
      refine ⟨105349067766528112974325907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70232711844352075316217271 105349067766528112974325907)
      ·
        refine ⟨158023601649792169461488861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105349067766528112974325907 158023601649792169461488861)
        ·
          refine ⟨59258850618672063548058323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158023601649792169461488861 59258850618672063548058323)
          ·
            refine ⟨88888275928008095322087485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59258850618672063548058323 88888275928008095322087485)
            ·
              refine ⟨33333103473003035745782807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88888275928008095322087485 33333103473003035745782807)
              ·
                refine ⟨49999655209504553618674211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33333103473003035745782807 49999655209504553618674211)
                ·
                  refine ⟨74999482814256830428011317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49999655209504553618674211 74999482814256830428011317)
                  ·
                    refine ⟨7031201513836577852626061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74999482814256830428011317 7031201513836577852626061)
                    ·
                      refine ⟨2636700567688716694734773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031201513836577852626061 2636700567688716694734773)
                      ·
                        rfl

theorem cell23_5134956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_5134956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134956 prefixEnd_5134956 := by exact prefixLift 5134956
  have htrace : WordTrace (prefixWord ++ tailWord_5134956) baseStart_5134956 baseEnd_5134956 := by
    simpa [prefixWord, tailWord_5134956, baseEnd_5134956] using wordTrace_append hprefix tailTrace_5134956
  have hstable : (prefixWord ++ tailWord_5134956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134956).length < 2 ^ (prefixWord ++ tailWord_5134956).sum := by decide
  have hdescent : baseEnd_5134956 < baseStart_5134956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134957 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_5134957 : Nat := 118140960795 + 5134957 * 2 ^ 59
def prefixEnd_5134957 : Nat := 4983230072969 + 3 ^ 40 * 5134957 * 2
def baseEnd_5134957 : Nat := 2636701081169371190822269

theorem tailTrace_5134957 : CollatzResearch.WordTrace tailWord_5134957 prefixEnd_5134957 2636701081169371190822269 := by
  unfold tailWord_5134957
  simp only [CollatzResearch.WordTrace]
  refine ⟨187287268057935244680699125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124858178705290163120466083 187287268057935244680699125)
  ·
    refine ⟨17558181380431429188815543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187287268057935244680699125 17558181380431429188815543)
    ·
      refine ⟨26337272070647143783223315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17558181380431429188815543 26337272070647143783223315)
      ·
        refine ⟨39505908105970715674834973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26337272070647143783223315 39505908105970715674834973)
        ·
          refine ⟨14814715539739018378063115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39505908105970715674834973 14814715539739018378063115)
          ·
            refine ⟨22222073309608527567094673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14814715539739018378063115 22222073309608527567094673)
            ·
              refine ⟨16666554982206395675321005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22222073309608527567094673 16666554982206395675321005)
              ·
                refine ⟨6249958118327398378245377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16666554982206395675321005 6249958118327398378245377)
                ·
                  refine ⟨4687468588745548783684033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6249958118327398378245377 4687468588745548783684033)
                  ·
                    refine ⟨3515601441559161587763025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4687468588745548783684033 3515601441559161587763025)
                    ·
                      refine ⟨2636701081169371190822269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515601441559161587763025 2636701081169371190822269)
                      ·
                        rfl

theorem cell23_5134957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_5134957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134957 prefixEnd_5134957 := by exact prefixLift 5134957
  have htrace : WordTrace (prefixWord ++ tailWord_5134957) baseStart_5134957 baseEnd_5134957 := by
    simpa [prefixWord, tailWord_5134957, baseEnd_5134957] using wordTrace_append hprefix tailTrace_5134957
  have hstable : (prefixWord ++ tailWord_5134957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134957).length < 2 ^ (prefixWord ++ tailWord_5134957).sum := by decide
  have hdescent : baseEnd_5134957 < baseStart_5134957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134976 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 1, 7]
def baseStart_5134976 : Nat := 118140960795 + 5134976 * 2 ^ 59
def prefixEnd_5134976 : Nat := 4983230072969 + 3 ^ 40 * 5134976 * 2
def baseEnd_5134976 : Nat := 878903612433935538828227

theorem tailTrace_5134976 : CollatzResearch.WordTrace tailWord_5134976 prefixEnd_5134976 878903612433935538828227 := by
  unfold tailWord_5134976
  simp only [CollatzResearch.WordTrace]
  refine ⟨93643980522433205462820391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124858640696577607283760521 93643980522433205462820391)
  ·
    refine ⟨140465970783649808194230587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93643980522433205462820391 140465970783649808194230587)
    ·
      refine ⟨210698956175474712291345881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140465970783649808194230587 210698956175474712291345881)
      ·
        refine ⟨158024217131606034218509411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210698956175474712291345881 158024217131606034218509411)
        ·
          refine ⟨237036325697409051327764117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158024217131606034218509411 237036325697409051327764117)
          ·
            refine ⟨11111077767066049280988943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 237036325697409051327764117 11111077767066049280988943)
            ·
              refine ⟨16666616650599073921483415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11111077767066049280988943 16666616650599073921483415)
              ·
                refine ⟨24999924975898610882225123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16666616650599073921483415 24999924975898610882225123)
                ·
                  refine ⟨37499887463847916323337685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24999924975898610882225123 37499887463847916323337685)
                  ·
                    refine ⟨878903612433935538828227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37499887463847916323337685 878903612433935538828227)
                    ·
                      rfl

theorem cell23_5134976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_5134976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134976 prefixEnd_5134976 := by exact prefixLift 5134976
  have htrace : WordTrace (prefixWord ++ tailWord_5134976) baseStart_5134976 baseEnd_5134976 := by
    simpa [prefixWord, tailWord_5134976, baseEnd_5134976] using wordTrace_append hprefix tailTrace_5134976
  have hstable : (prefixWord ++ tailWord_5134976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134976).length < 2 ^ (prefixWord ++ tailWord_5134976).sum := by decide
  have hdescent : baseEnd_5134976 < baseStart_5134976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134980 : List Nat := [2, 3, 2, 1, 3, 2, 2, 3, 5]
def baseStart_5134980 : Nat := 118140960795 + 5134980 * 2 ^ 59
def prefixEnd_5134980 : Nat := 4983230072969 + 3 ^ 40 * 5134980 * 2
def baseEnd_5134980 : Nat := 292968099024936066759407

theorem tailTrace_5134980 : CollatzResearch.WordTrace tailWord_5134980 prefixEnd_5134980 292968099024936066759407 := by
  unfold tailWord_5134980
  simp only [CollatzResearch.WordTrace]
  refine ⟨93644053468425959804393197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124858737957901279739190929 93644053468425959804393197)
  ·
    refine ⟨35116520050659734926647449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93644053468425959804393197 35116520050659734926647449)
    ·
      refine ⟨26337390037994801194985587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35116520050659734926647449 26337390037994801194985587)
      ·
        refine ⟨39506085056992201792478381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26337390037994801194985587 39506085056992201792478381)
        ·
          refine ⟨14814781896372075672179393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39506085056992201792478381 14814781896372075672179393)
          ·
            refine ⟨11111086422279056754134545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14814781896372075672179393 11111086422279056754134545)
            ·
              refine ⟨8333314816709292565600909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11111086422279056754134545 8333314816709292565600909)
              ·
                refine ⟨3124993056265984712100341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8333314816709292565600909 3124993056265984712100341)
                ·
                  refine ⟨292968099024936066759407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3124993056265984712100341 292968099024936066759407)
                  ·
                    rfl

theorem cell23_5134980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_5134980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134980 prefixEnd_5134980 := by exact prefixLift 5134980
  have htrace : WordTrace (prefixWord ++ tailWord_5134980) baseStart_5134980 baseEnd_5134980 := by
    simpa [prefixWord, tailWord_5134980, baseEnd_5134980] using wordTrace_append hprefix tailTrace_5134980
  have hstable : (prefixWord ++ tailWord_5134980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134980).length < 2 ^ (prefixWord ++ tailWord_5134980).sum := by decide
  have hdescent : baseEnd_5134980 < baseStart_5134980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135023 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 3, 4]
def baseStart_5135023 : Nat := 118140960795 + 5135023 * 2 ^ 59
def prefixEnd_5135023 : Nat := 4983230072969 + 3 ^ 40 * 5135023 * 2
def baseEnd_5135023 : Nat := 878911656964189310865655

theorem tailTrace_5135023 : CollatzResearch.WordTrace tailWord_5135023 prefixEnd_5135023 878911656964189310865655 := by
  unfold tailWord_5135023
  simp only [CollatzResearch.WordTrace]
  refine ⟨187289675275696137952601723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124859783517130758635067815 187289675275696137952601723)
  ·
    refine ⟨280934512913544206928902585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187289675275696137952601723 280934512913544206928902585)
    ·
      refine ⟨210700884685158155196676939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280934512913544206928902585 210700884685158155196676939)
      ·
        refine ⟨316051327027737232795015409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210700884685158155196676939 316051327027737232795015409)
        ·
          refine ⟨237038495270802924596261557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316051327027737232795015409 237038495270802924596261557)
          ·
            refine ⟨22222358931637774180899521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237038495270802924596261557 22222358931637774180899521)
            ·
              refine ⟨16666769198728330635674641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22222358931637774180899521 16666769198728330635674641)
              ·
                refine ⟨12500076899046247976755981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16666769198728330635674641 12500076899046247976755981)
                ·
                  refine ⟨4687528837142342991283493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12500076899046247976755981 4687528837142342991283493)
                  ·
                    refine ⟨878911656964189310865655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687528837142342991283493 878911656964189310865655)
                    ·
                      rfl

theorem cell23_5135023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 4].length) (baseStart_5135023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135023 prefixEnd_5135023 := by exact prefixLift 5135023
  have htrace : WordTrace (prefixWord ++ tailWord_5135023) baseStart_5135023 baseEnd_5135023 := by
    simpa [prefixWord, tailWord_5135023, baseEnd_5135023] using wordTrace_append hprefix tailTrace_5135023
  have hstable : (prefixWord ++ tailWord_5135023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135023).length < 2 ^ (prefixWord ++ tailWord_5135023).sum := by decide
  have hdescent : baseEnd_5135023 < baseStart_5135023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135026 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_5135026 : Nat := 118140960795 + 5135026 * 2 ^ 59
def prefixEnd_5135026 : Nat := 4983230072969 + 3 ^ 40 * 5135026 * 2
def baseEnd_5135026 : Nat := 2636736511334531420859451

theorem tailTrace_5135026 : CollatzResearch.WordTrace tailWord_5135026 prefixEnd_5135026 2636736511334531420859451 := by
  unfold tailWord_5135026
  simp only [CollatzResearch.WordTrace]
  refine ⟨46822446173671317366240233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124859856463123512976640621 46822446173671317366240233)
  ·
    refine ⟨35116834630253488024680175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46822446173671317366240233 35116834630253488024680175)
    ·
      refine ⟨52675251945380232037020263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35116834630253488024680175 52675251945380232037020263)
      ·
        refine ⟨79012877918070348055530395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52675251945380232037020263 79012877918070348055530395)
        ·
          refine ⟨118519316877105522083295593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79012877918070348055530395 118519316877105522083295593)
          ·
            refine ⟨88889487657829141562471695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118519316877105522083295593 88889487657829141562471695)
            ·
              refine ⟨133334231486743712343707543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88889487657829141562471695 133334231486743712343707543)
              ·
                refine ⟨200001347230115568515561315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133334231486743712343707543 200001347230115568515561315)
                ·
                  refine ⟨300002020845173352773341973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200001347230115568515561315 300002020845173352773341973)
                  ·
                    refine ⟨14062594727117500911250405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 300002020845173352773341973 14062594727117500911250405)
                    ·
                      refine ⟨2636736511334531420859451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14062594727117500911250405 2636736511334531420859451)
                      ·
                        rfl

theorem cell23_5135026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_5135026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135026 prefixEnd_5135026 := by exact prefixLift 5135026
  have htrace : WordTrace (prefixWord ++ tailWord_5135026) baseStart_5135026 baseEnd_5135026 := by
    simpa [prefixWord, tailWord_5135026, baseEnd_5135026] using wordTrace_append hprefix tailTrace_5135026
  have hstable : (prefixWord ++ tailWord_5135026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135026).length < 2 ^ (prefixWord ++ tailWord_5135026).sum := by decide
  have hdescent : baseEnd_5135026 < baseStart_5135026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135033 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 3]
def baseStart_5135033 : Nat := 118140960795 + 5135033 * 2 ^ 59
def prefixEnd_5135033 : Nat := 4983230072969 + 3 ^ 40 * 5135033 * 2
def baseEnd_5135033 : Nat := 2636740105699112893471919

theorem tailTrace_5135033 : CollatzResearch.WordTrace tailWord_5135033 prefixEnd_5135033 2636740105699112893471919 := by
  unfold tailWord_5135033
  simp only [CollatzResearch.WordTrace]
  refine ⟨187290040005659909660465753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124860026670439939773643835 187290040005659909660465753)
  ·
    refine ⟨140467530004244932245349315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187290040005659909660465753 140467530004244932245349315)
    ·
      refine ⟨210701295006367398368023973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140467530004244932245349315 210701295006367398368023973)
      ·
        refine ⟨39506492813693887194004495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210701295006367398368023973 39506492813693887194004495)
        ·
          refine ⟨59259739220540830791006743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39506492813693887194004495 59259739220540830791006743)
          ·
            refine ⟨88889608830811246186510115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59259739220540830791006743 88889608830811246186510115)
            ·
              refine ⟨133334413246216869279765173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88889608830811246186510115 133334413246216869279765173)
              ·
                refine ⟨12500101241832831494977985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133334413246216869279765173 12500101241832831494977985)
                ·
                  refine ⟨9375075931374623621233489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12500101241832831494977985 9375075931374623621233489)
                  ·
                    refine ⟨7031306948530967715925117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9375075931374623621233489 7031306948530967715925117)
                    ·
                      refine ⟨2636740105699112893471919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031306948530967715925117 2636740105699112893471919)
                      ·
                        rfl

theorem cell23_5135033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_5135033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135033 prefixEnd_5135033 := by exact prefixLift 5135033
  have htrace : WordTrace (prefixWord ++ tailWord_5135033) baseStart_5135033 baseEnd_5135033 := by
    simpa [prefixWord, tailWord_5135033, baseEnd_5135033] using wordTrace_append hprefix tailTrace_5135033
  have hstable : (prefixWord ++ tailWord_5135033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135033).length < 2 ^ (prefixWord ++ tailWord_5135033).sum := by decide
  have hdescent : baseEnd_5135033 < baseStart_5135033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135036 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 10]
def baseStart_5135036 : Nat := 118140960795 + 5135036 * 2 ^ 59
def prefixEnd_5135036 : Nat := 4983230072969 + 3 ^ 40 * 5135036 * 2
def baseEnd_5135036 : Nat := 292971294015675153526045

theorem tailTrace_5135036 : CollatzResearch.WordTrace tailWord_5135036 prefixEnd_5135036 292971294015675153526045 := by
  unfold tailWord_5135036
  simp only [CollatzResearch.WordTrace]
  refine ⟨93645074712324520586412481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124860099616432694115216641 93645074712324520586412481)
  ·
    refine ⟨70233806034243390439809361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93645074712324520586412481 70233806034243390439809361)
    ·
      refine ⟨52675354525682542829857021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70233806034243390439809361 52675354525682542829857021)
      ·
        refine ⟨19753257947130953561196383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52675354525682542829857021 19753257947130953561196383)
        ·
          refine ⟨29629886920696430341794575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19753257947130953561196383 29629886920696430341794575)
          ·
            refine ⟨44444830381044645512691863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29629886920696430341794575 44444830381044645512691863)
            ·
              refine ⟨66667245571566968269037795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44444830381044645512691863 66667245571566968269037795)
              ·
                refine ⟨100000868357350452403556693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66667245571566968269037795 100000868357350452403556693)
                ·
                  refine ⟨292971294015675153526045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 100000868357350452403556693 292971294015675153526045)
                  ·
                    rfl

theorem cell23_5135036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_5135036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135036 prefixEnd_5135036 := by exact prefixLift 5135036
  have htrace : WordTrace (prefixWord ++ tailWord_5135036) baseStart_5135036 baseEnd_5135036 := by
    simpa [prefixWord, tailWord_5135036, baseEnd_5135036] using wordTrace_append hprefix tailTrace_5135036
  have hstable : (prefixWord ++ tailWord_5135036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135036).length < 2 ^ (prefixWord ++ tailWord_5135036).sum := by decide
  have hdescent : baseEnd_5135036 < baseStart_5135036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135050 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_5135050 : Nat := 118140960795 + 5135050 * 2 ^ 59
def prefixEnd_5135050 : Nat := 4983230072969 + 3 ^ 40 * 5135050 * 2
def baseEnd_5135050 : Nat := 2636748834870239326959341

theorem tailTrace_5135050 : CollatzResearch.WordTrace tailWord_5135050 prefixEnd_5135050 2636748834870239326959341 := by
  unfold tailWord_5135050
  simp only [CollatzResearch.WordTrace]
  refine ⟨46822665011649580390958651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124860440031065547709223069 46822665011649580390958651)
  ·
    refine ⟨70233997517474370586437977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46822665011649580390958651 70233997517474370586437977)
    ·
      refine ⟨52675498138105777939828483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70233997517474370586437977 52675498138105777939828483)
      ·
        refine ⟨79013247207158666909742725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52675498138105777939828483 79013247207158666909742725)
        ·
          refine ⟨14814983851342250045576761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79013247207158666909742725 14814983851342250045576761)
          ·
            refine ⟨11111237888506687534182571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14814983851342250045576761 11111237888506687534182571)
            ·
              refine ⟨16666856832760031301273857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11111237888506687534182571 16666856832760031301273857)
              ·
                refine ⟨12500142624570023475955393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16666856832760031301273857 12500142624570023475955393)
                ·
                  refine ⟨9375106968427517606966545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12500142624570023475955393 9375106968427517606966545)
                  ·
                    refine ⟨7031330226320638205224909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9375106968427517606966545 7031330226320638205224909)
                    ·
                      refine ⟨2636748834870239326959341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031330226320638205224909 2636748834870239326959341)
                      ·
                        rfl

theorem cell23_5135050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_5135050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135050 prefixEnd_5135050 := by exact prefixLift 5135050
  have htrace : WordTrace (prefixWord ++ tailWord_5135050) baseStart_5135050 baseEnd_5135050 := by
    simpa [prefixWord, tailWord_5135050, baseEnd_5135050] using wordTrace_append hprefix tailTrace_5135050
  have hstable : (prefixWord ++ tailWord_5135050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135050).length < 2 ^ (prefixWord ++ tailWord_5135050).sum := by decide
  have hdescent : baseEnd_5135050 < baseStart_5135050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135057 : List Nat := [1, 2, 2, 1, 2, 3, 5, 2, 1, 4]
def baseStart_5135057 : Nat := 118140960795 + 5135057 * 2 ^ 59
def prefixEnd_5135057 : Nat := 4983230072969 + 3 ^ 40 * 5135057 * 2
def baseEnd_5135057 : Nat := 878917476411606933190603

theorem tailTrace_5135057 : CollatzResearch.WordTrace tailWord_5135057 prefixEnd_5135057 878917476411606933190603 := by
  unfold tailWord_5135057
  simp only [CollatzResearch.WordTrace]
  refine ⟨187290915357572961759339425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124860610238381974506226283 187290915357572961759339425)
  ·
    refine ⟨140468186518179721319504569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187290915357572961759339425 140468186518179721319504569)
    ·
      refine ⟨105351139888634790989628427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140468186518179721319504569 105351139888634790989628427)
      ·
        refine ⟨158026709832952186484442641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105351139888634790989628427 158026709832952186484442641)
        ·
          refine ⟨118520032374714139863331981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158026709832952186484442641 118520032374714139863331981)
          ·
            refine ⟨44445012140517802448749493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118520032374714139863331981 44445012140517802448749493)
            ·
              refine ⟨4166719888173543979570265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44445012140517802448749493 4166719888173543979570265)
              ·
                refine ⟨3125039916130157984677699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4166719888173543979570265 3125039916130157984677699)
                ·
                  refine ⟨4687559874195236977016549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125039916130157984677699 4687559874195236977016549)
                  ·
                    refine ⟨878917476411606933190603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687559874195236977016549 878917476411606933190603)
                    ·
                      rfl

theorem cell23_5135057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_5135057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135057 prefixEnd_5135057 := by exact prefixLift 5135057
  have htrace : WordTrace (prefixWord ++ tailWord_5135057) baseStart_5135057 baseEnd_5135057 := by
    simpa [prefixWord, tailWord_5135057, baseEnd_5135057] using wordTrace_append hprefix tailTrace_5135057
  have hstable : (prefixWord ++ tailWord_5135057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135057).length < 2 ^ (prefixWord ++ tailWord_5135057).sum := by decide
  have hdescent : baseEnd_5135057 < baseStart_5135057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135113 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 4, 4]
def baseStart_5135113 : Nat := 118140960795 + 5135113 * 2 ^ 59
def prefixEnd_5135113 : Nat := 4983230072969 + 3 ^ 40 * 5135113 * 2
def baseEnd_5135113 : Nat := 878927061383824193490517

theorem tailTrace_5135113 : CollatzResearch.WordTrace tailWord_5135113 prefixEnd_5135113 878927061383824193490517 := by
  unfold tailWord_5135113
  simp only [CollatzResearch.WordTrace]
  refine ⟨187292957845370083323377993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124861971896913388882251995 187292957845370083323377993)
  ·
    refine ⟨140469718384027562492533495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187292957845370083323377993 140469718384027562492533495)
    ·
      refine ⟨210704577576041343738800243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140469718384027562492533495 210704577576041343738800243)
      ·
        refine ⟨316056866364062015608200365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210704577576041343738800243 316056866364062015608200365)
        ·
          refine ⟨118521324886523255853075137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316056866364062015608200365 118521324886523255853075137)
          ·
            refine ⟨88890993664892441889806353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118521324886523255853075137 88890993664892441889806353)
            ·
              refine ⟨66668245248669331417354765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88890993664892441889806353 66668245248669331417354765)
              ·
                refine ⟨25000591968250999281508037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66668245248669331417354765 25000591968250999281508037)
                ·
                  refine ⟨4687610994047062365282757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25000591968250999281508037 4687610994047062365282757)
                  ·
                    refine ⟨878927061383824193490517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687610994047062365282757 878927061383824193490517)
                    ·
                      rfl

theorem cell23_5135113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 4].length) (baseStart_5135113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135113 prefixEnd_5135113 := by exact prefixLift 5135113
  have htrace : WordTrace (prefixWord ++ tailWord_5135113) baseStart_5135113 baseEnd_5135113 := by
    simpa [prefixWord, tailWord_5135113, baseEnd_5135113] using wordTrace_append hprefix tailTrace_5135113
  have hstable : (prefixWord ++ tailWord_5135113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135113).length < 2 ^ (prefixWord ++ tailWord_5135113).sum := by decide
  have hdescent : baseEnd_5135113 < baseStart_5135113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135123 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 3]
def baseStart_5135123 : Nat := 118140960795 + 5135123 * 2 ^ 59
def prefixEnd_5135123 : Nat := 4983230072969 + 3 ^ 40 * 5135123 * 2
def baseEnd_5135123 : Nat := 2636786318958017541346505

theorem tailTrace_5135123 : CollatzResearch.WordTrace tailWord_5135123 prefixEnd_5135123 2636786318958017541346505 := by
  unfold tailWord_5135123
  simp only [CollatzResearch.WordTrace]
  refine ⟨187293322575333855031242023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124862215050222570020828015 187293322575333855031242023)
  ·
    refine ⟨280939983863000782546863035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187293322575333855031242023 280939983863000782546863035)
    ·
      refine ⟨421409975794501173820294553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280939983863000782546863035 421409975794501173820294553)
      ·
        refine ⟨316057481845875880365220915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421409975794501173820294553 316057481845875880365220915)
        ·
          refine ⟨474086222768813820547831373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316057481845875880365220915 474086222768813820547831373)
          ·
            refine ⟨177782333538305182705436765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474086222768813820547831373 177782333538305182705436765)
            ·
              refine ⟨66668375076864443514538787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177782333538305182705436765 66668375076864443514538787)
              ·
                refine ⟨100002562615296665271808181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66668375076864443514538787 100002562615296665271808181)
                ·
                  refine ⟨9375240245184062369232017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100002562615296665271808181 9375240245184062369232017)
                  ·
                    refine ⟨7031430183888046776924013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9375240245184062369232017 7031430183888046776924013)
                    ·
                      refine ⟨2636786318958017541346505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031430183888046776924013 2636786318958017541346505)
                      ·
                        rfl

theorem cell23_5135123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_5135123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135123 prefixEnd_5135123 := by exact prefixLift 5135123
  have htrace : WordTrace (prefixWord ++ tailWord_5135123) baseStart_5135123 baseEnd_5135123 := by
    simpa [prefixWord, tailWord_5135123, baseEnd_5135123] using wordTrace_append hprefix tailTrace_5135123
  have hstable : (prefixWord ++ tailWord_5135123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135123).length < 2 ^ (prefixWord ++ tailWord_5135123).sum := by decide
  have hdescent : baseEnd_5135123 < baseStart_5135123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135130 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_5135130 : Nat := 118140960795 + 5135130 * 2 ^ 59
def prefixEnd_5135130 : Nat := 4983230072969 + 3 ^ 40 * 5135130 * 2
def baseEnd_5135130 : Nat := 878929971107533004652991

theorem tailTrace_5135130 : CollatzResearch.WordTrace tailWord_5135130 prefixEnd_5135130 878929971107533004652991 := by
  unfold tailWord_5135130
  simp only [CollatzResearch.WordTrace]
  refine ⟨46823394471577123806686711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124862385257538996817831229 46823394471577123806686711)
  ·
    refine ⟨70235091707365685710030067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46823394471577123806686711 70235091707365685710030067)
    ·
      refine ⟨105352637561048528565045101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70235091707365685710030067 105352637561048528565045101)
      ·
        refine ⟨39507239085393198211891913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105352637561048528565045101 39507239085393198211891913)
        ·
          refine ⟨29630429314044898658918935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39507239085393198211891913 29630429314044898658918935)
          ·
            refine ⟨44445643971067347988378403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29630429314044898658918935 44445643971067347988378403)
            ·
              refine ⟨66668465956601021982567605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44445643971067347988378403 66668465956601021982567605)
              ·
                refine ⟨6250168683431345810865713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66668465956601021982567605 6250168683431345810865713)
                ·
                  refine ⟨4687626512573509358149285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6250168683431345810865713 4687626512573509358149285)
                  ·
                    refine ⟨878929971107533004652991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687626512573509358149285 878929971107533004652991)
                    ·
                      rfl

theorem cell23_5135130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_5135130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135130 prefixEnd_5135130 := by exact prefixLift 5135130
  have htrace : WordTrace (prefixWord ++ tailWord_5135130) baseStart_5135130 baseEnd_5135130 := by
    simpa [prefixWord, tailWord_5135130, baseEnd_5135130] using wordTrace_append hprefix tailTrace_5135130
  have hstable : (prefixWord ++ tailWord_5135130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135130).length < 2 ^ (prefixWord ++ tailWord_5135130).sum := by decide
  have hdescent : baseEnd_5135130 < baseStart_5135130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135137 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_5135137 : Nat := 118140960795 + 5135137 * 2 ^ 59
def prefixEnd_5135137 : Nat := 4983230072969 + 3 ^ 40 * 5135137 * 2
def baseEnd_5135137 : Nat := 2636793507687180486571441

theorem tailTrace_5135137 : CollatzResearch.WordTrace tailWord_5135137 prefixEnd_5135137 2636793507687180486571441 := by
  unfold tailWord_5135137
  simp only [CollatzResearch.WordTrace]
  refine ⟨187293833197283135422251665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124862555464855423614834443 187293833197283135422251665)
  ·
    refine ⟨140470374897962351566688749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187293833197283135422251665 140470374897962351566688749)
    ·
      refine ⟨52676390586735881837508281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140470374897962351566688749 52676390586735881837508281)
      ·
        refine ⟨39507292940051911378131211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52676390586735881837508281 39507292940051911378131211)
        ·
          refine ⟨59260939410077867067196817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39507292940051911378131211 59260939410077867067196817)
          ·
            refine ⟨44445704557558400300397613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59260939410077867067196817 44445704557558400300397613)
            ·
              refine ⟨16667139209084400112649105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44445704557558400300397613 16667139209084400112649105)
              ·
                refine ⟨12500354406813300084486829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16667139209084400112649105 12500354406813300084486829)
                ·
                  refine ⟨4687632902554987531682561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12500354406813300084486829 4687632902554987531682561)
                  ·
                    refine ⟨3515724676916240648761921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4687632902554987531682561 3515724676916240648761921)
                    ·
                      refine ⟨2636793507687180486571441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515724676916240648761921 2636793507687180486571441)
                      ·
                        rfl

theorem cell23_5135137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_5135137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135137 prefixEnd_5135137 := by exact prefixLift 5135137
  have htrace : WordTrace (prefixWord ++ tailWord_5135137) baseStart_5135137 baseEnd_5135137 := by
    simpa [prefixWord, tailWord_5135137, baseEnd_5135137] using wordTrace_append hprefix tailTrace_5135137
  have hstable : (prefixWord ++ tailWord_5135137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135137).length < 2 ^ (prefixWord ++ tailWord_5135137).sum := by decide
  have hdescent : baseEnd_5135137 < baseStart_5135137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135157 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_5135157 : Nat := 118140960795 + 5135157 * 2 ^ 59
def prefixEnd_5135157 : Nat := 4983230072969 + 3 ^ 40 * 5135157 * 2
def baseEnd_5135157 : Nat := 2636803777300270408321349

theorem tailTrace_5135157 : CollatzResearch.WordTrace tailWord_5135157 prefixEnd_5135157 2636803777300270408321349 := by
  unfold tailWord_5135157
  simp only [CollatzResearch.WordTrace]
  refine ⟨187294562657210678837979725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124863041771473785891986483 187294562657210678837979725)
  ·
    refine ⟨70235460996454004564242397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187294562657210678837979725 70235460996454004564242397)
    ·
      refine ⟨26338297873670251711590899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70235460996454004564242397 26338297873670251711590899)
      ·
        refine ⟨39507446810505377567386349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26338297873670251711590899 39507446810505377567386349)
        ·
          refine ⟨14815292553939516587769881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39507446810505377567386349 14815292553939516587769881)
          ·
            refine ⟨11111469415454637440827411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14815292553939516587769881 11111469415454637440827411)
            ·
              refine ⟨16667204123181956161241117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11111469415454637440827411 16667204123181956161241117)
              ·
                refine ⟨6250201546193233560465419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16667204123181956161241117 6250201546193233560465419)
                ·
                  refine ⟨9375302319289850340698129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6250201546193233560465419 9375302319289850340698129)
                  ·
                    refine ⟨7031476739467387755523597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9375302319289850340698129 7031476739467387755523597)
                    ·
                      refine ⟨2636803777300270408321349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031476739467387755523597 2636803777300270408321349)
                      ·
                        rfl

theorem cell23_5135157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_5135157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135157 prefixEnd_5135157 := by exact prefixLift 5135157
  have htrace : WordTrace (prefixWord ++ tailWord_5135157) baseStart_5135157 baseEnd_5135157 := by
    simpa [prefixWord, tailWord_5135157, baseEnd_5135157] using wordTrace_append hprefix tailTrace_5135157
  have hstable : (prefixWord ++ tailWord_5135157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135157).length < 2 ^ (prefixWord ++ tailWord_5135157).sum := by decide
  have hdescent : baseEnd_5135157 < baseStart_5135157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135174 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5135174 : Nat := 118140960795 + 5135174 * 2 ^ 59
def prefixEnd_5135174 : Nat := 4983230072969 + 3 ^ 40 * 5135174 * 2
def baseEnd_5135174 : Nat := 2636812506471396841808771

theorem tailTrace_5135174 : CollatzResearch.WordTrace tailWord_5135174 prefixEnd_5135174 2636812506471396841808771 := by
  unfold tailWord_5135174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852974459317159085667143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124863455132099393827565717 5852974459317159085667143)
  ·
    refine ⟨8779461688975738628500715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5852974459317159085667143 8779461688975738628500715)
    ·
      refine ⟨13169192533463607942751073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8779461688975738628500715 13169192533463607942751073)
      ·
        refine ⟨9876894400097705957063305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13169192533463607942751073 9876894400097705957063305)
        ·
          refine ⟨7407670800073279467797479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9876894400097705957063305 7407670800073279467797479)
          ·
            refine ⟨11111506200109919201696219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7407670800073279467797479 11111506200109919201696219)
            ·
              refine ⟨16667259300164878802544329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11111506200109919201696219 16667259300164878802544329)
              ·
                refine ⟨12500444475123659101908247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16667259300164878802544329 12500444475123659101908247)
                ·
                  refine ⟨18750666712685488652862371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12500444475123659101908247 18750666712685488652862371)
                  ·
                    refine ⟨28126000069028232979293557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18750666712685488652862371 28126000069028232979293557)
                    ·
                      refine ⟨2636812506471396841808771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28126000069028232979293557 2636812506471396841808771)
                      ·
                        rfl

theorem cell23_5135174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5135174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135174 prefixEnd_5135174 := by exact prefixLift 5135174
  have htrace : WordTrace (prefixWord ++ tailWord_5135174) baseStart_5135174 baseEnd_5135174 := by
    simpa [prefixWord, tailWord_5135174, baseEnd_5135174] using wordTrace_append hprefix tailTrace_5135174
  have hstable : (prefixWord ++ tailWord_5135174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135174).length < 2 ^ (prefixWord ++ tailWord_5135174).sum := by decide
  have hdescent : baseEnd_5135174 < baseStart_5135174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135181 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5135181 : Nat := 118140960795 + 5135181 * 2 ^ 59
def prefixEnd_5135181 : Nat := 4983230072969 + 3 ^ 40 * 5135181 * 2
def baseEnd_5135181 : Nat := 878938700278659438140413

theorem tailTrace_5135181 : CollatzResearch.WordTrace tailWord_5135181 prefixEnd_5135181 878938700278659438140413 := by
  unfold tailWord_5135181
  simp only [CollatzResearch.WordTrace]
  refine ⟨187295438009123730936853397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124863625339415820624568931 187295438009123730936853397)
  ·
    refine ⟨8779473656677674887665003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 187295438009123730936853397 8779473656677674887665003)
    ·
      refine ⟨13169210485016512331497505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8779473656677674887665003 13169210485016512331497505)
      ·
        refine ⟨9876907863762384248623129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13169210485016512331497505 9876907863762384248623129)
        ·
          refine ⟨7407680897821788186467347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9876907863762384248623129 7407680897821788186467347)
          ·
            refine ⟨11111521346732682279701021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7407680897821788186467347 11111521346732682279701021)
            ·
              refine ⟨4166820505024755854887883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11111521346732682279701021 4166820505024755854887883)
              ·
                refine ⟨6250230757537133782331825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166820505024755854887883 6250230757537133782331825)
                ·
                  refine ⟨4687673068152850336748869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6250230757537133782331825 4687673068152850336748869)
                  ·
                    refine ⟨878938700278659438140413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687673068152850336748869 878938700278659438140413)
                    ·
                      rfl

theorem cell23_5135181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5135181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135181 prefixEnd_5135181 := by exact prefixLift 5135181
  have htrace : WordTrace (prefixWord ++ tailWord_5135181) baseStart_5135181 baseEnd_5135181 := by
    simpa [prefixWord, tailWord_5135181, baseEnd_5135181] using wordTrace_append hprefix tailTrace_5135181
  have hstable : (prefixWord ++ tailWord_5135181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135181).length < 2 ^ (prefixWord ++ tailWord_5135181).sum := by decide
  have hdescent : baseEnd_5135181 < baseStart_5135181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135223 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_5135223 : Nat := 118140960795 + 5135223 * 2 ^ 59
def prefixEnd_5135223 : Nat := 4983230072969 + 3 ^ 40 * 5135223 * 2
def baseEnd_5135223 : Nat := 2636837667023467150096045

theorem tailTrace_5135223 : CollatzResearch.WordTrace tailWord_5135223 prefixEnd_5135223 2636837667023467150096045 := by
  unfold tailWord_5135223
  simp only [CollatzResearch.WordTrace]
  refine ⟨187296969874971572109882323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124864646583314381406588215 187296969874971572109882323)
  ·
    refine ⟨280945454812457358164823485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187296969874971572109882323 280945454812457358164823485)
    ·
      refine ⟨105354545554671509311808807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280945454812457358164823485 105354545554671509311808807)
      ·
        refine ⟨158031818332007263967713211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105354545554671509311808807 158031818332007263967713211)
        ·
          refine ⟨237047727498010895951569817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158031818332007263967713211 237047727498010895951569817)
          ·
            refine ⟨177785795623508171963677363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237047727498010895951569817 177785795623508171963677363)
            ·
              refine ⟨266678693435262257945516045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177785795623508171963677363 266678693435262257945516045)
              ·
                refine ⟨100004510038223346729568517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266678693435262257945516045 100004510038223346729568517)
                ·
                  refine ⟨18750845632166877511794097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100004510038223346729568517 18750845632166877511794097)
                  ·
                    refine ⟨14063134224125158133845573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18750845632166877511794097 14063134224125158133845573)
                    ·
                      refine ⟨2636837667023467150096045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14063134224125158133845573 2636837667023467150096045)
                      ·
                        rfl

theorem cell23_5135223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_5135223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135223 prefixEnd_5135223 := by exact prefixLift 5135223
  have htrace : WordTrace (prefixWord ++ tailWord_5135223) baseStart_5135223 baseEnd_5135223 := by
    simpa [prefixWord, tailWord_5135223, baseEnd_5135223] using wordTrace_append hprefix tailTrace_5135223
  have hstable : (prefixWord ++ tailWord_5135223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135223).length < 2 ^ (prefixWord ++ tailWord_5135223).sum := by decide
  have hdescent : baseEnd_5135223 < baseStart_5135223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135227 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 4, 2, 2]
def baseStart_5135227 : Nat := 118140960795 + 5135227 * 2 ^ 59
def prefixEnd_5135227 : Nat := 4983230072969 + 3 ^ 40 * 5135227 * 2
def baseEnd_5135227 : Nat := 2636839720946085134446027

theorem tailTrace_5135227 : CollatzResearch.WordTrace tailWord_5135227 prefixEnd_5135227 2636839720946085134446027 := by
  unfold tailWord_5135227
  simp only [CollatzResearch.WordTrace]
  refine ⟨187297115766957080793027935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124864743844638053862018623 187297115766957080793027935)
  ·
    refine ⟨280945673650435621189541903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187297115766957080793027935 280945673650435621189541903)
    ·
      refine ⟨421418510475653431784312855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280945673650435621189541903 421418510475653431784312855)
      ·
        refine ⟨632127765713480147676469283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421418510475653431784312855 632127765713480147676469283)
        ·
          refine ⟨948191648570220221514703925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632127765713480147676469283 948191648570220221514703925)
          ·
            refine ⟨88892967053458145767003493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 948191648570220221514703925 88892967053458145767003493)
            ·
              refine ⟨16667431322523402331313155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88892967053458145767003493 16667431322523402331313155)
              ·
                refine ⟨25001146983785103496969733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16667431322523402331313155 25001146983785103496969733)
                ·
                  refine ⟨4687715059459706905681825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25001146983785103496969733 4687715059459706905681825)
                  ·
                    refine ⟨3515786294594780179261369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4687715059459706905681825 3515786294594780179261369)
                    ·
                      refine ⟨2636839720946085134446027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515786294594780179261369 2636839720946085134446027)
                      ·
                        rfl

theorem cell23_5135227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 2, 2].length) (baseStart_5135227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135227 prefixEnd_5135227 := by exact prefixLift 5135227
  have htrace : WordTrace (prefixWord ++ tailWord_5135227) baseStart_5135227 baseEnd_5135227 := by
    simpa [prefixWord, tailWord_5135227, baseEnd_5135227] using wordTrace_append hprefix tailTrace_5135227
  have hstable : (prefixWord ++ tailWord_5135227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135227).length < 2 ^ (prefixWord ++ tailWord_5135227).sum := by decide
  have hdescent : baseEnd_5135227 < baseStart_5135227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135273 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_5135273 : Nat := 118140960795 + 5135273 * 2 ^ 59
def prefixEnd_5135273 : Nat := 4983230072969 + 3 ^ 40 * 5135273 * 2
def baseEnd_5135273 : Nat := 2636863341056191954470815

theorem tailTrace_5135273 : CollatzResearch.WordTrace tailWord_5135273 prefixEnd_5135273 2636863341056191954470815 := by
  unfold tailWord_5135273
  simp only [CollatzResearch.WordTrace]
  refine ⟨187298793524790430649202473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124865862349860287099468315 187298793524790430649202473)
  ·
    refine ⟨140474095143592822986901855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187298793524790430649202473 140474095143592822986901855)
    ·
      refine ⟨210711142715389234480352783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140474095143592822986901855 210711142715389234480352783)
      ·
        refine ⟨316066714073083851720529175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210711142715389234480352783 316066714073083851720529175)
        ·
          refine ⟨474100071109625777580793763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316066714073083851720529175 474100071109625777580793763)
          ·
            refine ⟨711150106664438666371190645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474100071109625777580793763 711150106664438666371190645)
            ·
              refine ⟨66670322499791124972299123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 711150106664438666371190645 66670322499791124972299123)
              ·
                refine ⟨100005483749686687458448685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66670322499791124972299123 100005483749686687458448685)
                ·
                  refine ⟨37502056406132507796918257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100005483749686687458448685 37502056406132507796918257)
                  ·
                    refine ⟨28126542304599380847688693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37502056406132507796918257 28126542304599380847688693)
                    ·
                      refine ⟨2636863341056191954470815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28126542304599380847688693 2636863341056191954470815)
                      ·
                        rfl

theorem cell23_5135273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_5135273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135273 prefixEnd_5135273 := by exact prefixLift 5135273
  have htrace : WordTrace (prefixWord ++ tailWord_5135273) baseStart_5135273 baseEnd_5135273 := by
    simpa [prefixWord, tailWord_5135273, baseEnd_5135273] using wordTrace_append hprefix tailTrace_5135273
  have hstable : (prefixWord ++ tailWord_5135273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135273).length < 2 ^ (prefixWord ++ tailWord_5135273).sum := by decide
  have hdescent : baseEnd_5135273 < baseStart_5135273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135314 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_5135314 : Nat := 118140960795 + 5135314 * 2 ^ 59
def prefixEnd_5135314 : Nat := 4983230072969 + 3 ^ 40 * 5135314 * 2
def baseEnd_5135314 : Nat := 878961464587675431352709

theorem tailTrace_5135314 : CollatzResearch.WordTrace tailWord_5135314 prefixEnd_5135314 878961464587675431352709 := by
  unfold tailWord_5135314
  simp only [CollatzResearch.WordTrace]
  refine ⟨46825072229410473662861249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124866859278427929767629997 46825072229410473662861249)
  ·
    refine ⟨35118804172057855247145937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46825072229410473662861249 35118804172057855247145937)
    ·
      refine ⟨26339103129043391435359453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35118804172057855247145937 26339103129043391435359453)
      ·
        refine ⟨9877163673391271788259795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26339103129043391435359453 9877163673391271788259795)
        ·
          refine ⟨14815745510086907682389693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9877163673391271788259795 14815745510086907682389693)
          ·
            refine ⟨5555904566282590380896135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14815745510086907682389693 5555904566282590380896135)
            ·
              refine ⟨8333856849423885571344203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555904566282590380896135 8333856849423885571344203)
              ·
                refine ⟨12500785274135828357016305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8333856849423885571344203 12500785274135828357016305)
                ·
                  refine ⟨9375588955601871267762229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12500785274135828357016305 9375588955601871267762229)
                  ·
                    refine ⟨878961464587675431352709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9375588955601871267762229 878961464587675431352709)
                    ·
                      rfl

theorem cell23_5135314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_5135314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135314 prefixEnd_5135314 := by exact prefixLift 5135314
  have htrace : WordTrace (prefixWord ++ tailWord_5135314) baseStart_5135314 baseEnd_5135314 := by
    simpa [prefixWord, tailWord_5135314, baseEnd_5135314] using wordTrace_append hprefix tailTrace_5135314
  have hstable : (prefixWord ++ tailWord_5135314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135314).length < 2 ^ (prefixWord ++ tailWord_5135314).sum := by decide
  have hdescent : baseEnd_5135314 < baseStart_5135314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135317 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_5135317 : Nat := 118140960795 + 5135317 * 2 ^ 59
def prefixEnd_5135317 : Nat := 4983230072969 + 3 ^ 40 * 5135317 * 2
def baseEnd_5135317 : Nat := 2636885934204989782320613

theorem tailTrace_5135317 : CollatzResearch.WordTrace tailWord_5135317 prefixEnd_5135317 2636885934204989782320613 := by
  unfold tailWord_5135317
  simp only [CollatzResearch.WordTrace]
  refine ⟨187300398336631026163804205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124866932224420684109202803 187300398336631026163804205)
  ·
    refine ⟨70237649376236634811426577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187300398336631026163804205 70237649376236634811426577)
    ·
      refine ⟨52678237032177476108569933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70237649376236634811426577 52678237032177476108569933)
      ·
        refine ⟨19754338887066553540713725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52678237032177476108569933 19754338887066553540713725)
        ·
          refine ⟨7407877082649957577767647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19754338887066553540713725 7407877082649957577767647)
          ·
            refine ⟨11111815623974936366651471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7407877082649957577767647 11111815623974936366651471)
            ·
              refine ⟨16667723435962404549977207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11111815623974936366651471 16667723435962404549977207)
              ·
                refine ⟨25001585153943606824965811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16667723435962404549977207 25001585153943606824965811)
                ·
                  refine ⟨37502377730915410237448717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25001585153943606824965811 37502377730915410237448717)
                  ·
                    refine ⟨14063391649093278839043269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37502377730915410237448717 14063391649093278839043269)
                    ·
                      refine ⟨2636885934204989782320613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14063391649093278839043269 2636885934204989782320613)
                      ·
                        rfl

theorem cell23_5135317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_5135317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135317 prefixEnd_5135317 := by exact prefixLift 5135317
  have htrace : WordTrace (prefixWord ++ tailWord_5135317) baseStart_5135317 baseEnd_5135317 := by
    simpa [prefixWord, tailWord_5135317, baseEnd_5135317] using wordTrace_append hprefix tailTrace_5135317
  have hstable : (prefixWord ++ tailWord_5135317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135317).length < 2 ^ (prefixWord ++ tailWord_5135317).sum := by decide
  have hdescent : baseEnd_5135317 < baseStart_5135317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135377 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 6, 3, 2]
def baseStart_5135377 : Nat := 118140960795 + 5135377 * 2 ^ 59
def prefixEnd_5135377 : Nat := 4983230072969 + 3 ^ 40 * 5135377 * 2
def baseEnd_5135377 : Nat := 2636916743044259547570337

theorem tailTrace_5135377 : CollatzResearch.WordTrace tailWord_5135377 prefixEnd_5135377 2636916743044259547570337 := by
  unfold tailWord_5135377
  simp only [CollatzResearch.WordTrace]
  refine ⟨187302586716413656410988385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124868391144275770940658923 187302586716413656410988385)
  ·
    refine ⟨140476940037310242308241289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187302586716413656410988385 140476940037310242308241289)
    ·
      refine ⟨105357705027982681731180967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140476940037310242308241289 105357705027982681731180967)
      ·
        refine ⟨158036557541974022596771451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105357705027982681731180967 158036557541974022596771451)
        ·
          refine ⟨237054836312961033895157177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158036557541974022596771451 237054836312961033895157177)
          ·
            refine ⟨177791127234720775421367883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237054836312961033895157177 177791127234720775421367883)
            ·
              refine ⟨266686690852081163132051825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177791127234720775421367883 266686690852081163132051825)
              ·
                refine ⟨200015018139060872349038869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266686690852081163132051825 200015018139060872349038869)
                ·
                  refine ⟨9375703975268478391361197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 200015018139060872349038869 9375703975268478391361197)
                  ·
                    refine ⟨3515888990725679396760449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9375703975268478391361197 3515888990725679396760449)
                    ·
                      refine ⟨2636916743044259547570337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515888990725679396760449 2636916743044259547570337)
                      ·
                        rfl

theorem cell23_5135377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_5135377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135377 prefixEnd_5135377 := by exact prefixLift 5135377
  have htrace : WordTrace (prefixWord ++ tailWord_5135377) baseStart_5135377 baseEnd_5135377 := by
    simpa [prefixWord, tailWord_5135377, baseEnd_5135377] using wordTrace_append hprefix tailTrace_5135377
  have hstable : (prefixWord ++ tailWord_5135377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135377).length < 2 ^ (prefixWord ++ tailWord_5135377).sum := by decide
  have hdescent : baseEnd_5135377 < baseStart_5135377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135394 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_5135394 : Nat := 118140960795 + 5135394 * 2 ^ 59
def prefixEnd_5135394 : Nat := 4983230072969 + 3 ^ 40 * 5135394 * 2
def baseEnd_5135394 : Nat := 2636925472215385981057759

theorem tailTrace_5135394 : CollatzResearch.WordTrace tailWord_5135394 prefixEnd_5135394 2636925472215385981057759 := by
  unfold tailWord_5135394
  simp only [CollatzResearch.WordTrace]
  refine ⟨46825801689338017078589309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124868804504901378876238157 46825801689338017078589309)
  ·
    refine ⟨17559675633501756404470991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46825801689338017078589309 17559675633501756404470991)
    ·
      refine ⟨26339513450252634606706487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17559675633501756404470991 26339513450252634606706487)
      ·
        refine ⟨39509270175378951910059731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26339513450252634606706487 39509270175378951910059731)
        ·
          refine ⟨59263905263068427865089597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39509270175378951910059731 59263905263068427865089597)
          ·
            refine ⟨22223964473650660449408599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59263905263068427865089597 22223964473650660449408599)
            ·
              refine ⟨33335946710475990674112899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22223964473650660449408599 33335946710475990674112899)
              ·
                refine ⟨50003920065713986011169349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33335946710475990674112899 50003920065713986011169349)
                ·
                  refine ⟨9375735012321372377094253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50003920065713986011169349 9375735012321372377094253)
                  ·
                    refine ⟨3515900629620514641410345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9375735012321372377094253 3515900629620514641410345)
                    ·
                      refine ⟨2636925472215385981057759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515900629620514641410345 2636925472215385981057759)
                      ·
                        rfl

theorem cell23_5135394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_5135394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135394 prefixEnd_5135394 := by exact prefixLift 5135394
  have htrace : WordTrace (prefixWord ++ tailWord_5135394) baseStart_5135394 baseEnd_5135394 := by
    simpa [prefixWord, tailWord_5135394, baseEnd_5135394] using wordTrace_append hprefix tailTrace_5135394
  have hstable : (prefixWord ++ tailWord_5135394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135394).length < 2 ^ (prefixWord ++ tailWord_5135394).sum := by decide
  have hdescent : baseEnd_5135394 < baseStart_5135394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135424 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 5, 2, 2]
def baseStart_5135424 : Nat := 118140960795 + 5135424 * 2 ^ 59
def prefixEnd_5135424 : Nat := 4983230072969 + 3 ^ 40 * 5135424 * 2
def baseEnd_5135424 : Nat := 2636940876635020863682621

theorem tailTrace_5135424 : CollatzResearch.WordTrace tailWord_5135424 prefixEnd_5135424 2636940876635020863682621 := by
  unfold tailWord_5135424
  simp only [CollatzResearch.WordTrace]
  refine ⟨93652150473621691718974663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124869533964828922291966217 93652150473621691718974663)
  ·
    refine ⟨140478225710432537578461995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93652150473621691718974663 140478225710432537578461995)
    ·
      refine ⟨210717338565648806367692993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140478225710432537578461995 210717338565648806367692993)
      ·
        refine ⟨158038003924236604775769745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210717338565648806367692993 158038003924236604775769745)
        ·
          refine ⟨118528502943177453581827309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158038003924236604775769745 118528502943177453581827309)
          ·
            refine ⟨44448188603691545093185241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118528502943177453581827309 44448188603691545093185241)
            ·
              refine ⟨33336141452768658819888931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44448188603691545093185241 33336141452768658819888931)
              ·
                refine ⟨50004212179152988229833397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33336141452768658819888931 50004212179152988229833397)
                ·
                  refine ⟨4687894891795592646546881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50004212179152988229833397 4687894891795592646546881)
                  ·
                    refine ⟨3515921168846694484910161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4687894891795592646546881 3515921168846694484910161)
                    ·
                      refine ⟨2636940876635020863682621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515921168846694484910161 2636940876635020863682621)
                      ·
                        rfl

theorem cell23_5135424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_5135424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135424 prefixEnd_5135424 := by exact prefixLift 5135424
  have htrace : WordTrace (prefixWord ++ tailWord_5135424) baseStart_5135424 baseEnd_5135424 := by
    simpa [prefixWord, tailWord_5135424, baseEnd_5135424] using wordTrace_append hprefix tailTrace_5135424
  have hstable : (prefixWord ++ tailWord_5135424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135424).length < 2 ^ (prefixWord ++ tailWord_5135424).sum := by decide
  have hdescent : baseEnd_5135424 < baseStart_5135424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135427 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 3]
def baseStart_5135427 : Nat := 118140960795 + 5135427 * 2 ^ 59
def prefixEnd_5135427 : Nat := 4983230072969 + 3 ^ 40 * 5135427 * 2
def baseEnd_5135427 : Nat := 2636942417076984351945107

theorem tailTrace_5135427 : CollatzResearch.WordTrace tailWord_5135427 prefixEnd_5135427 2636942417076984351945107 := by
  unfold tailWord_5135427
  simp only [CollatzResearch.WordTrace]
  refine ⟨187304410366232514950308535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124869606910821676633539023 187304410366232514950308535)
  ·
    refine ⟨280956615549348772425462803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187304410366232514950308535 280956615549348772425462803)
    ·
      refine ⟨421434923324023158638194205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280956615549348772425462803 421434923324023158638194205)
      ·
        refine ⟨158038096246508684489322827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421434923324023158638194205 158038096246508684489322827)
        ·
          refine ⟨237057144369763026733984241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158038096246508684489322827 237057144369763026733984241)
          ·
            refine ⟨177792858277322270050488181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237057144369763026733984241 177792858277322270050488181)
            ·
              refine ⟨16668080463498962817233267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177792858277322270050488181 16668080463498962817233267)
              ·
                refine ⟨25002120695248444225849901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16668080463498962817233267 25002120695248444225849901)
                ·
                  refine ⟨9375795260718166584693713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25002120695248444225849901 9375795260718166584693713)
                  ·
                    refine ⟨7031846445538624938520285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9375795260718166584693713 7031846445538624938520285)
                    ·
                      refine ⟨2636942417076984351945107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031846445538624938520285 2636942417076984351945107)
                      ·
                        rfl

theorem cell23_5135427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_5135427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135427 prefixEnd_5135427 := by exact prefixLift 5135427
  have htrace : WordTrace (prefixWord ++ tailWord_5135427) baseStart_5135427 baseEnd_5135427 := by
    simpa [prefixWord, tailWord_5135427, baseEnd_5135427] using wordTrace_append hprefix tailTrace_5135427
  have hstable : (prefixWord ++ tailWord_5135427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135427).length < 2 ^ (prefixWord ++ tailWord_5135427).sum := by decide
  have hdescent : baseEnd_5135427 < baseStart_5135427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135444 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_5135444 : Nat := 118140960795 + 5135444 * 2 ^ 59
def prefixEnd_5135444 : Nat := 4983230072969 + 3 ^ 40 * 5135444 * 2
def baseEnd_5135444 : Nat := 2636951146248110785432529

theorem tailTrace_5135444 : CollatzResearch.WordTrace tailWord_5135444 prefixEnd_5135444 2636951146248110785432529 := by
  unfold tailWord_5135444
  simp only [CollatzResearch.WordTrace]
  refine ⟨93652515203585463426838693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124870020271447284569118257 93652515203585463426838693)
  ·
    refine ⟨17559846600672274392532255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93652515203585463426838693 17559846600672274392532255)
    ·
      refine ⟨26339769901008411588798383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17559846600672274392532255 26339769901008411588798383)
      ·
        refine ⟨39509654851512617383197575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26339769901008411588798383 39509654851512617383197575)
        ·
          refine ⟨59264482277268926074796363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39509654851512617383197575 59264482277268926074796363)
          ·
            refine ⟨88896723415903389112194545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59264482277268926074796363 88896723415903389112194545)
            ·
              refine ⟨66672542561927541834145909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88896723415903389112194545 66672542561927541834145909)
              ·
                refine ⟨6250550865180707046951179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66672542561927541834145909 6250550865180707046951179)
                ·
                  refine ⟨9375826297771060570426769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6250550865180707046951179 9375826297771060570426769)
                  ·
                    refine ⟨7031869723328295427820077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9375826297771060570426769 7031869723328295427820077)
                    ·
                      refine ⟨2636951146248110785432529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031869723328295427820077 2636951146248110785432529)
                      ·
                        rfl

theorem cell23_5135444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_5135444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135444 prefixEnd_5135444 := by exact prefixLift 5135444
  have htrace : WordTrace (prefixWord ++ tailWord_5135444) baseStart_5135444 baseEnd_5135444 := by
    simpa [prefixWord, tailWord_5135444, baseEnd_5135444] using wordTrace_append hprefix tailTrace_5135444
  have hstable : (prefixWord ++ tailWord_5135444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135444).length < 2 ^ (prefixWord ++ tailWord_5135444).sum := by decide
  have hdescent : baseEnd_5135444 < baseStart_5135444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135450 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_5135450 : Nat := 118140960795 + 5135450 * 2 ^ 59
def prefixEnd_5135450 : Nat := 4983230072969 + 3 ^ 40 * 5135450 * 2
def baseEnd_5135450 : Nat := 2636954227132037761957501

theorem tailTrace_5135450 : CollatzResearch.WordTrace tailWord_5135450 prefixEnd_5135450 2636954227132037761957501 := by
  unfold tailWord_5135450
  simp only [CollatzResearch.WordTrace]
  refine ⟨46826312311287297469598951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124870166163432793252263869 46826312311287297469598951)
  ·
    refine ⟨70239468466930946204398427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46826312311287297469598951 70239468466930946204398427)
    ·
      refine ⟨105359202700396419306597641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70239468466930946204398427 105359202700396419306597641)
      ·
        refine ⟨79019402025297314479948231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105359202700396419306597641 79019402025297314479948231)
        ·
          refine ⟨118529103037945971719922347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79019402025297314479948231 118529103037945971719922347)
          ·
            refine ⟨177793654556918957579883521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118529103037945971719922347 177793654556918957579883521)
            ·
              refine ⟨133345240917689218184912641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177793654556918957579883521 133345240917689218184912641)
              ·
                refine ⟨100008930688266913638684481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133345240917689218184912641 100008930688266913638684481)
                ·
                  refine ⟨75006698016200185229013361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100008930688266913638684481 75006698016200185229013361)
                  ·
                    refine ⟨56255023512150138921760021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75006698016200185229013361 56255023512150138921760021)
                    ·
                      refine ⟨2636954227132037761957501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56255023512150138921760021 2636954227132037761957501)
                      ·
                        rfl

theorem cell23_5135450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_5135450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135450 prefixEnd_5135450 := by exact prefixLift 5135450
  have htrace : WordTrace (prefixWord ++ tailWord_5135450) baseStart_5135450 baseEnd_5135450 := by
    simpa [prefixWord, tailWord_5135450, baseEnd_5135450] using wordTrace_append hprefix tailTrace_5135450
  have hstable : (prefixWord ++ tailWord_5135450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135450).length < 2 ^ (prefixWord ++ tailWord_5135450).sum := by decide
  have hdescent : baseEnd_5135450 < baseStart_5135450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135474 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_5135474 : Nat := 118140960795 + 5135474 * 2 ^ 59
def prefixEnd_5135474 : Nat := 4983230072969 + 3 ^ 40 * 5135474 * 2
def baseEnd_5135474 : Nat := 2636966550667745668057391

theorem tailTrace_5135474 : CollatzResearch.WordTrace tailWord_5135474 prefixEnd_5135474 2636966550667745668057391 := by
  unfold tailWord_5135474
  simp only [CollatzResearch.WordTrace]
  refine ⟨46826531149265560494317369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124870749731374827984846317 46826531149265560494317369)
  ·
    refine ⟨35119898361949170370738027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46826531149265560494317369 35119898361949170370738027)
    ·
      refine ⟨52679847542923755556107041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35119898361949170370738027 52679847542923755556107041)
      ·
        refine ⟨39509885657192816667080281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52679847542923755556107041 39509885657192816667080281)
        ·
          refine ⟨29632414242894612500310211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39509885657192816667080281 29632414242894612500310211)
          ·
            refine ⟨44448621364341918750465317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29632414242894612500310211 44448621364341918750465317)
            ·
              refine ⟨8334116505814109765712247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44448621364341918750465317 8334116505814109765712247)
              ·
                refine ⟨12501174758721164648568371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8334116505814109765712247 12501174758721164648568371)
                ·
                  refine ⟨18751762138081746972852557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12501174758721164648568371 18751762138081746972852557)
                  ·
                    refine ⟨7031910801780655114819709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18751762138081746972852557 7031910801780655114819709)
                    ·
                      refine ⟨2636966550667745668057391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7031910801780655114819709 2636966550667745668057391)
                      ·
                        rfl

theorem cell23_5135474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_5135474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135474 prefixEnd_5135474 := by exact prefixLift 5135474
  have htrace : WordTrace (prefixWord ++ tailWord_5135474) baseStart_5135474 baseEnd_5135474 := by
    simpa [prefixWord, tailWord_5135474, baseEnd_5135474] using wordTrace_append hprefix tailTrace_5135474
  have hstable : (prefixWord ++ tailWord_5135474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135474).length < 2 ^ (prefixWord ++ tailWord_5135474).sum := by decide
  have hdescent : baseEnd_5135474 < baseStart_5135474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135484 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_5135484 : Nat := 118140960795 + 5135484 * 2 ^ 59
def prefixEnd_5135484 : Nat := 4983230072969 + 3 ^ 40 * 5135484 * 2
def baseEnd_5135484 : Nat := 2636971685474290628932345

theorem tailTrace_5135484 : CollatzResearch.WordTrace tailWord_5135484 prefixEnd_5135484 2636971685474290628932345 := by
  unfold tailWord_5135484
  simp only [CollatzResearch.WordTrace]
  refine ⟨93653244663513006842566753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124870992884684009123422337 93653244663513006842566753)
  ·
    refine ⟨70239933497634755131925065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93653244663513006842566753 70239933497634755131925065)
    ·
      refine ⟨52679950123226066348943799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70239933497634755131925065 52679950123226066348943799)
      ·
        refine ⟨79019925184839099523415699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52679950123226066348943799 79019925184839099523415699)
        ·
          refine ⟨118529887777258649285123549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79019925184839099523415699 118529887777258649285123549)
          ·
            refine ⟨44448707916471993481921331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118529887777258649285123549 44448707916471993481921331)
            ·
              refine ⟨66673061874707990222881997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44448707916471993481921331 66673061874707990222881997)
              ·
                refine ⟨25002398203015496333580749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66673061874707990222881997 25002398203015496333580749)
                ·
                  refine ⟨9375899326130811125092781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25002398203015496333580749 9375899326130811125092781)
                  ·
                    refine ⟨3515962247299054171909793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9375899326130811125092781 3515962247299054171909793)
                    ·
                      refine ⟨2636971685474290628932345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3515962247299054171909793 2636971685474290628932345)
                      ·
                        rfl

theorem cell23_5135484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_5135484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135484 prefixEnd_5135484 := by exact prefixLift 5135484
  have htrace : WordTrace (prefixWord ++ tailWord_5135484) baseStart_5135484 baseEnd_5135484 := by
    simpa [prefixWord, tailWord_5135484, baseEnd_5135484] using wordTrace_append hprefix tailTrace_5135484
  have hstable : (prefixWord ++ tailWord_5135484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135484).length < 2 ^ (prefixWord ++ tailWord_5135484).sum := by decide
  have hdescent : baseEnd_5135484 < baseStart_5135484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135547 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 3]
def baseStart_5135547 : Nat := 118140960795 + 5135547 * 2 ^ 59
def prefixEnd_5135547 : Nat := 4983230072969 + 3 ^ 40 * 5135547 * 2
def baseEnd_5135547 : Nat := 2637004034755523882444555

theorem tailTrace_5135547 : CollatzResearch.WordTrace tailWord_5135547 prefixEnd_5135547 2637004034755523882444555 := by
  unfold tailWord_5135547
  simp only [CollatzResearch.WordTrace]
  refine ⟨187308787125797775444676895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124872524750531850296451263 187308787125797775444676895)
  ·
    refine ⟨280963180688696663167015343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187308787125797775444676895 280963180688696663167015343)
    ·
      refine ⟨421444771033044994750523015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280963180688696663167015343 421444771033044994750523015)
      ·
        refine ⟨632167156549567492125784523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421444771033044994750523015 632167156549567492125784523)
        ·
          refine ⟨948250734824351238188676785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632167156549567492125784523 948250734824351238188676785)
          ·
            refine ⟨711188051118263428641507589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 948250734824351238188676785 711188051118263428641507589)
            ·
              refine ⟨133347759584674392870282673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 711188051118263428641507589 133347759584674392870282673)
              ·
                refine ⟨100010819688505794652712005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133347759584674392870282673 100010819688505794652712005)
                ·
                  refine ⟨18752028691594836497383501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100010819688505794652712005 18752028691594836497383501)
                  ·
                    refine ⟨7032010759348063686518813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18752028691594836497383501 7032010759348063686518813)
                    ·
                      refine ⟨2637004034755523882444555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7032010759348063686518813 2637004034755523882444555)
                      ·
                        rfl

theorem cell23_5135547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 3].length) (baseStart_5135547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135547 prefixEnd_5135547 := by exact prefixLift 5135547
  have htrace : WordTrace (prefixWord ++ tailWord_5135547) baseStart_5135547 baseEnd_5135547 := by
    simpa [prefixWord, tailWord_5135547, baseEnd_5135547] using wordTrace_append hprefix tailTrace_5135547
  have hstable : (prefixWord ++ tailWord_5135547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135547).length < 2 ^ (prefixWord ++ tailWord_5135547).sum := by decide
  have hdescent : baseEnd_5135547 < baseStart_5135547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135644 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 6]
def baseStart_5135644 : Nat := 118140960795 + 5135644 * 2 ^ 59
def prefixEnd_5135644 : Nat := 4983230072969 + 3 ^ 40 * 5135644 * 2
def baseEnd_5135644 : Nat := 293005982486556666992401

theorem tailTrace_5135644 : CollatzResearch.WordTrace tailWord_5135644 prefixEnd_5135644 293005982486556666992401 := by
  unfold tailWord_5135644
  simp only [CollatzResearch.WordTrace]
  refine ⟨93656162503223180505478993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124874883337630907340638657 93656162503223180505478993)
  ·
    refine ⟨70242121877417385379109245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93656162503223180505478993 70242121877417385379109245)
    ·
      refine ⟨26340795704031519517165967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70242121877417385379109245 26340795704031519517165967)
      ·
        refine ⟨39511193556047279275748951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26340795704031519517165967 39511193556047279275748951)
        ·
          refine ⟨59266790334070918913623427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39511193556047279275748951 59266790334070918913623427)
          ·
            refine ⟨88900185501106378370435141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59266790334070918913623427 88900185501106378370435141)
            ·
              refine ⟨16668784781457445944456589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88900185501106378370435141 16668784781457445944456589)
              ·
                refine ⟨6250794293046542229171221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16668784781457445944456589 6250794293046542229171221)
                ·
                  refine ⟨293005982486556666992401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6250794293046542229171221 293005982486556666992401)
                  ·
                    rfl

theorem cell23_5135644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_5135644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135644 prefixEnd_5135644 := by exact prefixLift 5135644
  have htrace : WordTrace (prefixWord ++ tailWord_5135644) baseStart_5135644 baseEnd_5135644 := by
    simpa [prefixWord, tailWord_5135644, baseEnd_5135644] using wordTrace_append hprefix tailTrace_5135644
  have hstable : (prefixWord ++ tailWord_5135644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135644).length < 2 ^ (prefixWord ++ tailWord_5135644).sum := by decide
  have hdescent : baseEnd_5135644 < baseStart_5135644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135658 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5135658 : Nat := 118140960795 + 5135658 * 2 ^ 59
def prefixEnd_5135658 : Nat := 4983230072969 + 3 ^ 40 * 5135658 * 2
def baseEnd_5135658 : Nat := 2637061031108172948156545

theorem tailTrace_5135658 : CollatzResearch.WordTrace tailWord_5135658 prefixEnd_5135658 2637061031108172948156545 := by
  unfold tailWord_5135658
  simp only [CollatzResearch.WordTrace]
  refine ⟨46828208907098910350491907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124875223752263760934645085 46828208907098910350491907)
  ·
    refine ⟨70242313360648365525737861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46828208907098910350491907 70242313360648365525737861)
    ·
      refine ⟨13170433755121568536075849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70242313360648365525737861 13170433755121568536075849)
      ·
        refine ⟨9877825316341176402056887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13170433755121568536075849 9877825316341176402056887)
        ·
          refine ⟨14816737974511764603085331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9877825316341176402056887 14816737974511764603085331)
          ·
            refine ⟨22225106961767646904627997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14816737974511764603085331 22225106961767646904627997)
            ·
              refine ⟨8334415110662867589235499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22225106961767646904627997 8334415110662867589235499)
              ·
                refine ⟨12501622665994301383853249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8334415110662867589235499 12501622665994301383853249)
                ·
                  refine ⟨9376216999495726037889937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12501622665994301383853249 9376216999495726037889937)
                  ·
                    refine ⟨7032162749621794528417453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9376216999495726037889937 7032162749621794528417453)
                    ·
                      refine ⟨2637061031108172948156545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7032162749621794528417453 2637061031108172948156545)
                      ·
                        rfl

theorem cell23_5135658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5135658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135658 prefixEnd_5135658 := by exact prefixLift 5135658
  have htrace : WordTrace (prefixWord ++ tailWord_5135658) baseStart_5135658 baseEnd_5135658 := by
    simpa [prefixWord, tailWord_5135658, baseEnd_5135658] using wordTrace_append hprefix tailTrace_5135658
  have hstable : (prefixWord ++ tailWord_5135658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135658).length < 2 ^ (prefixWord ++ tailWord_5135658).sum := by decide
  have hdescent : baseEnd_5135658 < baseStart_5135658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135762 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5135762 : Nat := 118140960795 + 5135762 * 2 ^ 59
def prefixEnd_5135762 : Nat := 4983230072969 + 3 ^ 40 * 5135762 * 2
def baseEnd_5135762 : Nat := 2637114433096240541256067

theorem tailTrace_5135762 : CollatzResearch.WordTrace tailWord_5135762 prefixEnd_5135762 2637114433096240541256067 := by
  unfold tailWord_5135762
  simp only [CollatzResearch.WordTrace]
  refine ⟨46829157205004716790938385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124877752546679244775835693 46829157205004716790938385)
  ·
    refine ⟨35121867903753537593203789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46829157205004716790938385 35121867903753537593203789)
    ·
      refine ⟨13170700463907576597451421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35121867903753537593203789 13170700463907576597451421)
      ·
        refine ⟨4939012673965341224044283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13170700463907576597451421 4939012673965341224044283)
        ·
          refine ⟨7408519010948011836066425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4939012673965341224044283 7408519010948011836066425)
          ·
            refine ⟨5556389258211008877049819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7408519010948011836066425 5556389258211008877049819)
            ·
              refine ⟨8334583887316513315574729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5556389258211008877049819 8334583887316513315574729)
              ·
                refine ⟨6250937915487384986681047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8334583887316513315574729 6250937915487384986681047)
                ·
                  refine ⟨9376406873231077480021571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6250937915487384986681047 9376406873231077480021571)
                  ·
                    refine ⟨14064610309846616220032357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9376406873231077480021571 14064610309846616220032357)
                    ·
                      refine ⟨2637114433096240541256067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14064610309846616220032357 2637114433096240541256067)
                      ·
                        rfl

theorem cell23_5135762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5135762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135762 prefixEnd_5135762 := by exact prefixLift 5135762
  have htrace : WordTrace (prefixWord ++ tailWord_5135762) baseStart_5135762 baseEnd_5135762 := by
    simpa [prefixWord, tailWord_5135762, baseEnd_5135762] using wordTrace_append hprefix tailTrace_5135762
  have hstable : (prefixWord ++ tailWord_5135762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135762).length < 2 ^ (prefixWord ++ tailWord_5135762).sum := by decide
  have hdescent : baseEnd_5135762 < baseStart_5135762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135771 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 9, 3, 2]
def baseStart_5135771 : Nat := 118140960795 + 5135771 * 2 ^ 59
def prefixEnd_5135771 : Nat := 4983230072969 + 3 ^ 40 * 5135771 * 2
def baseEnd_5135771 : Nat := 2637119054422131006043525

theorem tailTrace_5135771 : CollatzResearch.WordTrace tailWord_5135771 prefixEnd_5135771 2637119054422131006043525 := by
  unfold tailWord_5135771
  simp only [CollatzResearch.WordTrace]
  refine ⟨187316957076986261700831167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124877971384657507800554111 187316957076986261700831167)
  ·
    refine ⟨280975435615479392551246751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187316957076986261700831167 280975435615479392551246751)
    ·
      refine ⟨421463153423219088826870127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280975435615479392551246751 421463153423219088826870127)
      ·
        refine ⟨632194730134828633240305191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421463153423219088826870127 632194730134828633240305191)
        ·
          refine ⟨948292095202242949860457787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632194730134828633240305191 948292095202242949860457787)
          ·
            refine ⟨1422438142803364424790686681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948292095202242949860457787 1422438142803364424790686681)
            ·
              refine ⟨1066828607102523318593015011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422438142803364424790686681 1066828607102523318593015011)
              ·
                refine ⟨1600242910653784977889522517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066828607102523318593015011 1600242910653784977889522517)
                ·
                  refine ⟨9376423304612021354821421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1600242910653784977889522517 9376423304612021354821421)
                  ·
                    refine ⟨3516158739229508008058033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9376423304612021354821421 3516158739229508008058033)
                    ·
                      refine ⟨2637119054422131006043525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516158739229508008058033 2637119054422131006043525)
                      ·
                        rfl

theorem cell23_5135771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 3, 2].length) (baseStart_5135771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135771 prefixEnd_5135771 := by exact prefixLift 5135771
  have htrace : WordTrace (prefixWord ++ tailWord_5135771) baseStart_5135771 baseEnd_5135771 := by
    simpa [prefixWord, tailWord_5135771, baseEnd_5135771] using wordTrace_append hprefix tailTrace_5135771
  have hstable : (prefixWord ++ tailWord_5135771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135771).length < 2 ^ (prefixWord ++ tailWord_5135771).sum := by decide
  have hdescent : baseEnd_5135771 < baseStart_5135771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135778 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_5135778 : Nat := 118140960795 + 5135778 * 2 ^ 59
def prefixEnd_5135778 : Nat := 4983230072969 + 3 ^ 40 * 5135778 * 2
def baseEnd_5135778 : Nat := 2637122648786712478655993

theorem tailTrace_5135778 : CollatzResearch.WordTrace tailWord_5135778 prefixEnd_5135778 2637122648786712478655993 := by
  unfold tailWord_5135778
  simp only [CollatzResearch.WordTrace]
  refine ⟨46829303096990225474083997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124878141591973934597557325 46829303096990225474083997)
  ·
    refine ⟨17560988661371334552781499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46829303096990225474083997 17560988661371334552781499)
    ·
      refine ⟨26341482992057001829172249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17560988661371334552781499 26341482992057001829172249)
      ·
        refine ⟨19756112244042751371879187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26341482992057001829172249 19756112244042751371879187)
        ·
          refine ⟨29634168366064127057818781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19756112244042751371879187 29634168366064127057818781)
          ·
            refine ⟨11112813137274047646682043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29634168366064127057818781 11112813137274047646682043)
            ·
              refine ⟨16669219705911071470023065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11112813137274047646682043 16669219705911071470023065)
              ·
                refine ⟨12501914779433303602517299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16669219705911071470023065 12501914779433303602517299)
                ·
                  refine ⟨18752872169149955403775949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12501914779433303602517299 18752872169149955403775949)
                  ·
                    refine ⟨7032327063431233276415981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18752872169149955403775949 7032327063431233276415981)
                    ·
                      refine ⟨2637122648786712478655993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7032327063431233276415981 2637122648786712478655993)
                      ·
                        rfl

theorem cell23_5135778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_5135778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135778 prefixEnd_5135778 := by exact prefixLift 5135778
  have htrace : WordTrace (prefixWord ++ tailWord_5135778) baseStart_5135778 baseEnd_5135778 := by
    simpa [prefixWord, tailWord_5135778, baseEnd_5135778] using wordTrace_append hprefix tailTrace_5135778
  have hstable : (prefixWord ++ tailWord_5135778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135778).length < 2 ^ (prefixWord ++ tailWord_5135778).sum := by decide
  have hdescent : baseEnd_5135778 < baseStart_5135778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135788 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 1, 3, 2]
def baseStart_5135788 : Nat := 118140960795 + 5135788 * 2 ^ 59
def prefixEnd_5135788 : Nat := 4983230072969 + 3 ^ 40 * 5135788 * 2
def baseEnd_5135788 : Nat := 2637127783593257439530947

theorem tailTrace_5135788 : CollatzResearch.WordTrace tailWord_5135788 prefixEnd_5135788 2637127783593257439530947 := by
  unfold tailWord_5135788
  simp only [CollatzResearch.WordTrace]
  refine ⟨93658788558962336802100009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124878384745283115736133345 93658788558962336802100009)
  ·
    refine ⟨70244091419221752601575007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93658788558962336802100009 70244091419221752601575007)
    ·
      refine ⟨105366137128832628902362511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70244091419221752601575007 105366137128832628902362511)
      ·
        refine ⟨158049205693248943353543767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105366137128832628902362511 158049205693248943353543767)
        ·
          refine ⟨237073808539873415030315651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158049205693248943353543767 237073808539873415030315651)
          ·
            refine ⟨355610712809810122545473477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237073808539873415030315651 355610712809810122545473477)
            ·
              refine ⟨66677008651839397977276277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 355610712809810122545473477 66677008651839397977276277)
              ·
                refine ⟨6250969561109943560369651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66677008651839397977276277 6250969561109943560369651)
                ·
                  refine ⟨9376454341664915340554477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6250969561109943560369651 9376454341664915340554477)
                  ·
                    refine ⟨3516170378124343252707929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9376454341664915340554477 3516170378124343252707929)
                    ·
                      refine ⟨2637127783593257439530947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516170378124343252707929 2637127783593257439530947)
                      ·
                        rfl

theorem cell23_5135788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_5135788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135788 prefixEnd_5135788 := by exact prefixLift 5135788
  have htrace : WordTrace (prefixWord ++ tailWord_5135788) baseStart_5135788 baseEnd_5135788 := by
    simpa [prefixWord, tailWord_5135788, baseEnd_5135788] using wordTrace_append hprefix tailTrace_5135788
  have hstable : (prefixWord ++ tailWord_5135788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135788).length < 2 ^ (prefixWord ++ tailWord_5135788).sum := by decide
  have hdescent : baseEnd_5135788 < baseStart_5135788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135818 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_5135818 : Nat := 118140960795 + 5135818 * 2 ^ 59
def prefixEnd_5135818 : Nat := 4983230072969 + 3 ^ 40 * 5135818 * 2
def baseEnd_5135818 : Nat := 2637143188012892322155809

theorem tailTrace_5135818 : CollatzResearch.WordTrace tailWord_5135818 prefixEnd_5135818 2637143188012892322155809 := by
  unfold tailWord_5135818
  simp only [CollatzResearch.WordTrace]
  refine ⟨46829667826953997181948027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124879114205210659151861405 46829667826953997181948027)
  ·
    refine ⟨70244501740430995772922041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46829667826953997181948027 70244501740430995772922041)
    ·
      refine ⟨52683376305323246829691531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70244501740430995772922041 52683376305323246829691531)
      ·
        refine ⟨79025064457984870244537297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52683376305323246829691531 79025064457984870244537297)
        ·
          refine ⟨59268798343488652683402973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79025064457984870244537297 59268798343488652683402973)
          ·
            refine ⟨22225799378808244756276115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59268798343488652683402973 22225799378808244756276115)
            ·
              refine ⟨33338699068212367134414173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22225799378808244756276115 33338699068212367134414173)
              ·
                refine ⟨12502012150579637675405315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33338699068212367134414173 12502012150579637675405315)
                ·
                  refine ⟨18753018225869456513107973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12502012150579637675405315 18753018225869456513107973)
                  ·
                    refine ⟨3516190917350523096207745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18753018225869456513107973 3516190917350523096207745)
                    ·
                      refine ⟨2637143188012892322155809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516190917350523096207745 2637143188012892322155809)
                      ·
                        rfl

theorem cell23_5135818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_5135818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135818 prefixEnd_5135818 := by exact prefixLift 5135818
  have htrace : WordTrace (prefixWord ++ tailWord_5135818) baseStart_5135818 baseEnd_5135818 := by
    simpa [prefixWord, tailWord_5135818, baseEnd_5135818] using wordTrace_append hprefix tailTrace_5135818
  have hstable : (prefixWord ++ tailWord_5135818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135818).length < 2 ^ (prefixWord ++ tailWord_5135818).sum := by decide
  have hdescent : baseEnd_5135818 < baseStart_5135818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135824 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 7]
def baseStart_5135824 : Nat := 118140960795 + 5135824 * 2 ^ 59
def prefixEnd_5135824 : Nat := 4983230072969 + 3 ^ 40 * 5135824 * 2
def baseEnd_5135824 : Nat := 293016252099646588742309

theorem tailTrace_5135824 : CollatzResearch.WordTrace tailWord_5135824 prefixEnd_5135824 293016252099646588742309 := by
  unfold tailWord_5135824
  simp only [CollatzResearch.WordTrace]
  refine ⟨93659445072897125876255263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124879260097196167835007017 93659445072897125876255263)
  ·
    refine ⟨140489167609345688814382895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93659445072897125876255263 140489167609345688814382895)
    ·
      refine ⟨210733751414018533221574343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140489167609345688814382895 210733751414018533221574343)
      ·
        refine ⟨316100627121027799832361515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210733751414018533221574343 316100627121027799832361515)
        ·
          refine ⟨474150940681541699748542273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316100627121027799832361515 474150940681541699748542273)
          ·
            refine ⟨355613205511156274811406705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474150940681541699748542273 355613205511156274811406705)
            ·
              refine ⟨266709904133367206108555029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355613205511156274811406705 266709904133367206108555029)
              ·
                refine ⟨12502026756251587786338517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 266709904133367206108555029 12502026756251587786338517)
                ·
                  refine ⟨293016252099646588742309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12502026756251587786338517 293016252099646588742309)
                  ·
                    rfl

theorem cell23_5135824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 7].length) (baseStart_5135824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135824 prefixEnd_5135824 := by exact prefixLift 5135824
  have htrace : WordTrace (prefixWord ++ tailWord_5135824) baseStart_5135824 baseEnd_5135824 := by
    simpa [prefixWord, tailWord_5135824, baseEnd_5135824] using wordTrace_append hprefix tailTrace_5135824
  have hstable : (prefixWord ++ tailWord_5135824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135824).length < 2 ^ (prefixWord ++ tailWord_5135824).sum := by decide
  have hdescent : baseEnd_5135824 < baseStart_5135824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135858 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 7]
def baseStart_5135858 : Nat := 118140960795 + 5135858 * 2 ^ 59
def prefixEnd_5135858 : Nat := 4983230072969 + 3 ^ 40 * 5135858 * 2
def baseEnd_5135858 : Nat := 293018191915452462850625

theorem tailTrace_5135858 : CollatzResearch.WordTrace tailWord_5135858 prefixEnd_5135858 293018191915452462850625 := by
  unfold tailWord_5135858
  simp only [CollatzResearch.WordTrace]
  refine ⟨46830032556917768889812057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124880086818447383706165485 46830032556917768889812057)
  ·
    refine ⟨35122524417688326667359043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46830032556917768889812057 35122524417688326667359043)
    ·
      refine ⟨52683786626532490001038565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35122524417688326667359043 52683786626532490001038565)
      ·
        refine ⟨9878209992474841875194731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52683786626532490001038565 9878209992474841875194731)
        ·
          refine ⟨14817314988712262812792097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9878209992474841875194731 14817314988712262812792097)
          ·
            refine ⟨11112986241534197109594073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14817314988712262812792097 11112986241534197109594073)
            ·
              refine ⟨8334739681150647832195555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11112986241534197109594073 8334739681150647832195555)
              ·
                refine ⟨12502109521725971748293333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8334739681150647832195555 12502109521725971748293333)
                ·
                  refine ⟨293018191915452462850625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12502109521725971748293333 293018191915452462850625)
                  ·
                    rfl

theorem cell23_5135858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_5135858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135858 prefixEnd_5135858 := by exact prefixLift 5135858
  have htrace : WordTrace (prefixWord ++ tailWord_5135858) baseStart_5135858 baseEnd_5135858 := by
    simpa [prefixWord, tailWord_5135858, baseEnd_5135858] using wordTrace_append hprefix tailTrace_5135858
  have hstable : (prefixWord ++ tailWord_5135858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135858).length < 2 ^ (prefixWord ++ tailWord_5135858).sum := by decide
  have hdescent : baseEnd_5135858 < baseStart_5135858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135891 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 4]
def baseStart_5135891 : Nat := 118140960795 + 5135891 * 2 ^ 59
def prefixEnd_5135891 : Nat := 4983230072969 + 3 ^ 40 * 5135891 * 2
def baseEnd_5135891 : Nat := 2637180672100670536542973

theorem tailTrace_5135891 : CollatzResearch.WordTrace tailWord_5135891 prefixEnd_5135891 2637180672100670536542973 := by
  unfold tailWord_5135891
  simp only [CollatzResearch.WordTrace]
  refine ⟨187321333836551522195199527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124880889224367681463466351 187321333836551522195199527)
  ·
    refine ⟨280982000754827283292799291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187321333836551522195199527 280982000754827283292799291)
    ·
      refine ⟨421473001132240924939198937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280982000754827283292799291 421473001132240924939198937)
      ·
        refine ⟨316104750849180693704399203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421473001132240924939198937 316104750849180693704399203)
        ·
          refine ⟨474157126273771040556598805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316104750849180693704399203 474157126273771040556598805)
          ·
            refine ⟨22226115294083017526090569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 474157126273771040556598805 22226115294083017526090569)
            ·
              refine ⟨16669586470562263144567927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22226115294083017526090569 16669586470562263144567927)
              ·
                refine ⟨25004379705843394716851891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16669586470562263144567927 25004379705843394716851891)
                ·
                  refine ⟨37506569558765092075277837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25004379705843394716851891 37506569558765092075277837)
                  ·
                    refine ⟨14064963584536909528229189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37506569558765092075277837 14064963584536909528229189)
                    ·
                      refine ⟨2637180672100670536542973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14064963584536909528229189 2637180672100670536542973)
                      ·
                        rfl

theorem cell23_5135891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_5135891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135891 prefixEnd_5135891 := by exact prefixLift 5135891
  have htrace : WordTrace (prefixWord ++ tailWord_5135891) baseStart_5135891 baseEnd_5135891 := by
    simpa [prefixWord, tailWord_5135891, baseEnd_5135891] using wordTrace_append hprefix tailTrace_5135891
  have hstable : (prefixWord ++ tailWord_5135891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135891).length < 2 ^ (prefixWord ++ tailWord_5135891).sum := by decide
  have hdescent : baseEnd_5135891 < baseStart_5135891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135968 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 3, 5, 2]
def baseStart_5135968 : Nat := 118140960795 + 5135968 * 2 ^ 59
def prefixEnd_5135968 : Nat := 4983230072969 + 3 ^ 40 * 5135968 * 2
def baseEnd_5135968 : Nat := 2637220210111066735280119

theorem tailTrace_5135968 : CollatzResearch.WordTrace tailWord_5135968 prefixEnd_5135968 2637220210111066735280119 := by
  unfold tailWord_5135968
  simp only [CollatzResearch.WordTrace]
  refine ⟨93662071128636282172876279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124882761504848376230501705 93662071128636282172876279)
  ·
    refine ⟨140493106692954423259314419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93662071128636282172876279 140493106692954423259314419)
    ·
      refine ⟨210739660039431634888971629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140493106692954423259314419 210739660039431634888971629)
      ·
        refine ⟨79027372514786863083364361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210739660039431634888971629 79027372514786863083364361)
        ·
          refine ⟨59270529386090147312523271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79027372514786863083364361 59270529386090147312523271)
          ·
            refine ⟨88905794079135220968784907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59270529386090147312523271 88905794079135220968784907)
            ·
              refine ⟨133358691118702831453177361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88905794079135220968784907 133358691118702831453177361)
              ·
                refine ⟨100019018339027123589883021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133358691118702831453177361 100019018339027123589883021)
                ·
                  refine ⟨37507131877135171346206133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100019018339027123589883021 37507131877135171346206133)
                  ·
                    refine ⟨3516293613481422313706825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37507131877135171346206133 3516293613481422313706825)
                    ·
                      refine ⟨2637220210111066735280119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516293613481422313706825 2637220210111066735280119)
                      ·
                        rfl

theorem cell23_5135968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_5135968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135968 prefixEnd_5135968 := by exact prefixLift 5135968
  have htrace : WordTrace (prefixWord ++ tailWord_5135968) baseStart_5135968 baseEnd_5135968 := by
    simpa [prefixWord, tailWord_5135968, baseEnd_5135968] using wordTrace_append hprefix tailTrace_5135968
  have hstable : (prefixWord ++ tailWord_5135968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135968).length < 2 ^ (prefixWord ++ tailWord_5135968).sum := by decide
  have hdescent : baseEnd_5135968 < baseStart_5135968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5135978 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_5135978 : Nat := 118140960795 + 5135978 * 2 ^ 59
def prefixEnd_5135978 : Nat := 4983230072969 + 3 ^ 40 * 5135978 * 2
def baseEnd_5135978 : Nat := 879075114972537232051691

theorem tailTrace_5135978 : CollatzResearch.WordTrace tailWord_5135978 prefixEnd_5135978 879075114972537232051691 := by
  unfold tailWord_5135978
  simp only [CollatzResearch.WordTrace]
  refine ⟨46831126746809084013404147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124883004658157557369077725 46831126746809084013404147)
  ·
    refine ⟨70246690120213626020106221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46831126746809084013404147 70246690120213626020106221)
    ·
      refine ⟨26342508795080109757539833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70246690120213626020106221 26342508795080109757539833)
      ·
        refine ⟨19756881596310082318154875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26342508795080109757539833 19756881596310082318154875)
        ·
          refine ⟨29635322394465123477232313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19756881596310082318154875 29635322394465123477232313)
          ·
            refine ⟨22226491795848842607924235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29635322394465123477232313 22226491795848842607924235)
            ·
              refine ⟨33339737693773263911886353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22226491795848842607924235 33339737693773263911886353)
              ·
                refine ⟨25004803270329947933914765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33339737693773263911886353 25004803270329947933914765)
                ·
                  refine ⟨9376801226373730475218037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25004803270329947933914765 9376801226373730475218037)
                  ·
                    refine ⟨879075114972537232051691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9376801226373730475218037 879075114972537232051691)
                    ·
                      rfl

theorem cell23_5135978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_5135978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5135978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5135978 prefixEnd_5135978 := by exact prefixLift 5135978
  have htrace : WordTrace (prefixWord ++ tailWord_5135978) baseStart_5135978 baseEnd_5135978 := by
    simpa [prefixWord, tailWord_5135978, baseEnd_5135978] using wordTrace_append hprefix tailTrace_5135978
  have hstable : (prefixWord ++ tailWord_5135978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5135978).length < 2 ^ (prefixWord ++ tailWord_5135978).sum := by decide
  have hdescent : baseEnd_5135978 < baseStart_5135978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5135978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136032 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 3, 2, 2]
def baseStart_5136032 : Nat := 118140960795 + 5136032 * 2 ^ 59
def prefixEnd_5136032 : Nat := 4983230072969 + 3 ^ 40 * 5136032 * 2
def baseEnd_5136032 : Nat := 2637253072872954484879825

theorem tailTrace_5136032 : CollatzResearch.WordTrace tailWord_5136032 prefixEnd_5136032 2637253072872954484879825 := by
  unfold tailWord_5136032
  simp only [CollatzResearch.WordTrace]
  refine ⟨93663238264520351638041175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124884317686027135517388233 93663238264520351638041175)
  ·
    refine ⟨140494857396780527457061763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93663238264520351638041175 140494857396780527457061763)
    ·
      refine ⟨210742286095170791185592645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140494857396780527457061763 210742286095170791185592645)
      ·
        refine ⟨39514178642844523347298621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210742286095170791185592645 39514178642844523347298621)
        ·
          refine ⟨14817816991066696255236983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39514178642844523347298621 14817816991066696255236983)
          ·
            refine ⟨22226725486600044382855475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14817816991066696255236983 22226725486600044382855475)
            ·
              refine ⟨33340088229900066574283213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22226725486600044382855475 33340088229900066574283213)
              ·
                refine ⟨12502533086212524965356205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33340088229900066574283213 12502533086212524965356205)
                ·
                  refine ⟨4688449907329696862008577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12502533086212524965356205 4688449907329696862008577)
                  ·
                    refine ⟨3516337430497272646506433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4688449907329696862008577 3516337430497272646506433)
                    ·
                      refine ⟨2637253072872954484879825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516337430497272646506433 2637253072872954484879825)
                      ·
                        rfl

theorem cell23_5136032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_5136032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136032 prefixEnd_5136032 := by exact prefixLift 5136032
  have htrace : WordTrace (prefixWord ++ tailWord_5136032) baseStart_5136032 baseEnd_5136032 := by
    simpa [prefixWord, tailWord_5136032, baseEnd_5136032] using wordTrace_append hprefix tailTrace_5136032
  have hstable : (prefixWord ++ tailWord_5136032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136032).length < 2 ^ (prefixWord ++ tailWord_5136032).sum := by decide
  have hdescent : baseEnd_5136032 < baseStart_5136032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136055 : List Nat := [1, 1, 3, 1, 5, 3, 2, 7]
def baseStart_5136055 : Nat := 118140960795 + 5136055 * 2 ^ 59
def prefixEnd_5136055 : Nat := 4983230072969 + 3 ^ 40 * 5136055 * 2
def baseEnd_5136055 : Nat := 97676477145481773884897

theorem tailTrace_5136055 : CollatzResearch.WordTrace tailWord_5136055 prefixEnd_5136055 97676477145481773884897 := by
  unfold tailWord_5136055
  simp only [CollatzResearch.WordTrace]
  refine ⟨187327315407957378204169619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124884876938638252136113079 187327315407957378204169619)
  ·
    refine ⟨280990973111936067306254429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187327315407957378204169619 280990973111936067306254429)
    ·
      refine ⟨105371614916976025239845411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280990973111936067306254429 105371614916976025239845411)
      ·
        refine ⟨158057422375464037859768117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105371614916976025239845411 158057422375464037859768117)
        ·
          refine ⟨14817883347699753549353261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158057422375464037859768117 14817883347699753549353261)
          ·
            refine ⟨5556706255387407581007473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14817883347699753549353261 5556706255387407581007473)
            ·
              refine ⟨4167529691540555685755605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5556706255387407581007473 4167529691540555685755605)
              ·
                refine ⟨97676477145481773884897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4167529691540555685755605 97676477145481773884897)
                ·
                  rfl

theorem cell23_5136055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 7].length) (baseStart_5136055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136055 prefixEnd_5136055 := by exact prefixLift 5136055
  have htrace : WordTrace (prefixWord ++ tailWord_5136055) baseStart_5136055 baseEnd_5136055 := by
    simpa [prefixWord, tailWord_5136055, baseEnd_5136055] using wordTrace_append hprefix tailTrace_5136055
  have hstable : (prefixWord ++ tailWord_5136055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136055).length < 2 ^ (prefixWord ++ tailWord_5136055).sum := by decide
  have hdescent : baseEnd_5136055 < baseStart_5136055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136078 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_5136078 : Nat := 118140960795 + 5136078 * 2 ^ 59
def prefixEnd_5136078 : Nat := 4983230072969 + 3 ^ 40 * 5136078 * 2
def baseEnd_5136078 : Nat := 2637276692983061304904613

theorem tailTrace_5136078 : CollatzResearch.WordTrace tailWord_5136078 prefixEnd_5136078 2637276692983061304904613 := by
  unfold tailWord_5136078
  simp only [CollatzResearch.WordTrace]
  refine ⟨23416019285859256641532111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124885436191249368754837925 23416019285859256641532111)
  ·
    refine ⟨35124028928788884962298167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23416019285859256641532111 35124028928788884962298167)
    ·
      refine ⟨52686043393183327443447251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35124028928788884962298167 52686043393183327443447251)
      ·
        refine ⟨79029065089774991165170877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52686043393183327443447251 79029065089774991165170877)
        ·
          refine ⟨29635899408665621686939079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79029065089774991165170877 29635899408665621686939079)
          ·
            refine ⟨44453849112998432530408619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29635899408665621686939079 44453849112998432530408619)
            ·
              refine ⟨66680773669497648795612929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44453849112998432530408619 66680773669497648795612929)
              ·
                refine ⟨50010580252123236596709697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66680773669497648795612929 50010580252123236596709697)
                ·
                  refine ⟨37507935189092427447532273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50010580252123236596709697 37507935189092427447532273)
                  ·
                    refine ⟨28130951391819320585649205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37507935189092427447532273 28130951391819320585649205)
                    ·
                      refine ⟨2637276692983061304904613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28130951391819320585649205 2637276692983061304904613)
                      ·
                        rfl

theorem cell23_5136078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_5136078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136078 prefixEnd_5136078 := by exact prefixLift 5136078
  have htrace : WordTrace (prefixWord ++ tailWord_5136078) baseStart_5136078 baseEnd_5136078 := by
    simpa [prefixWord, tailWord_5136078, baseEnd_5136078] using wordTrace_append hprefix tailTrace_5136078
  have hstable : (prefixWord ++ tailWord_5136078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136078).length < 2 ^ (prefixWord ++ tailWord_5136078).sum := by decide
  have hdescent : baseEnd_5136078 < baseStart_5136078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136082 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_5136082 : Nat := 118140960795 + 5136082 * 2 ^ 59
def prefixEnd_5136082 : Nat := 4983230072969 + 3 ^ 40 * 5136082 * 2
def baseEnd_5136082 : Nat := 2637278746905679289254595

theorem tailTrace_5136082 : CollatzResearch.WordTrace tailWord_5136082 prefixEnd_5136082 2637278746905679289254595 := by
  unfold tailWord_5136082
  simp only [CollatzResearch.WordTrace]
  refine ⟨46832075044714890453850625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124885533452573041210268333 46832075044714890453850625)
  ·
    refine ⟨35124056283536167840387969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46832075044714890453850625 35124056283536167840387969)
    ·
      refine ⟨26343042212652125880290977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35124056283536167840387969 26343042212652125880290977)
      ·
        refine ⟨19757281659489094410218233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26343042212652125880290977 19757281659489094410218233)
        ·
          refine ⟨14817961244616820807663675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19757281659489094410218233 14817961244616820807663675)
          ·
            refine ⟨22226941866925231211495513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14817961244616820807663675 22226941866925231211495513)
            ·
              refine ⟨16670206400193923408621635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22226941866925231211495513 16670206400193923408621635)
              ·
                refine ⟨25005309600290885112932453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16670206400193923408621635 25005309600290885112932453)
                ·
                  refine ⟨4688495550054540958674835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25005309600290885112932453 4688495550054540958674835)
                  ·
                    refine ⟨7032743325081811438012253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4688495550054540958674835 7032743325081811438012253)
                    ·
                      refine ⟨2637278746905679289254595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7032743325081811438012253 2637278746905679289254595)
                      ·
                        rfl

theorem cell23_5136082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_5136082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136082 prefixEnd_5136082 := by exact prefixLift 5136082
  have htrace : WordTrace (prefixWord ++ tailWord_5136082) baseStart_5136082 baseEnd_5136082 := by
    simpa [prefixWord, tailWord_5136082, baseEnd_5136082] using wordTrace_append hprefix tailTrace_5136082
  have hstable : (prefixWord ++ tailWord_5136082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136082).length < 2 ^ (prefixWord ++ tailWord_5136082).sum := by decide
  have hdescent : baseEnd_5136082 < baseStart_5136082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136088 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_5136088 : Nat := 118140960795 + 5136088 * 2 ^ 59
def prefixEnd_5136088 : Nat := 4983230072969 + 3 ^ 40 * 5136088 * 2
def baseEnd_5136088 : Nat := 2637281827789606265779567

theorem tailTrace_5136088 : CollatzResearch.WordTrace tailWord_5136088 prefixEnd_5136088 2637281827789606265779567 := by
  unfold tailWord_5136088
  simp only [CollatzResearch.WordTrace]
  refine ⟨93664259508418912420060459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124885679344558549893413945 93664259508418912420060459)
  ·
    refine ⟨140496389262628368630090689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93664259508418912420060459 140496389262628368630090689)
    ·
      refine ⟨105372291946971276472568017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140496389262628368630090689 105372291946971276472568017)
      ·
        refine ⟨79029218960228457354426013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105372291946971276472568017 79029218960228457354426013)
        ·
          refine ⟨29635957110085671507909755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79029218960228457354426013 29635957110085671507909755)
          ·
            refine ⟨44453935665128507261864633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29635957110085671507909755 44453935665128507261864633)
            ·
              refine ⟨33340451748846380446398475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44453935665128507261864633 33340451748846380446398475)
              ·
                refine ⟨50010677623269570669597713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33340451748846380446398475 50010677623269570669597713)
                ·
                  refine ⟨37508008217452178002198285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50010677623269570669597713 37508008217452178002198285)
                  ·
                    refine ⟨14065503081544566750824357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37508008217452178002198285 14065503081544566750824357)
                    ·
                      refine ⟨2637281827789606265779567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14065503081544566750824357 2637281827789606265779567)
                      ·
                        rfl

theorem cell23_5136088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_5136088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136088 prefixEnd_5136088 := by exact prefixLift 5136088
  have htrace : WordTrace (prefixWord ++ tailWord_5136088) baseStart_5136088 baseEnd_5136088 := by
    simpa [prefixWord, tailWord_5136088, baseEnd_5136088] using wordTrace_append hprefix tailTrace_5136088
  have hstable : (prefixWord ++ tailWord_5136088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136088).length < 2 ^ (prefixWord ++ tailWord_5136088).sum := by decide
  have hdescent : baseEnd_5136088 < baseStart_5136088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136093 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_5136093 : Nat := 118140960795 + 5136093 * 2 ^ 59
def prefixEnd_5136093 : Nat := 4983230072969 + 3 ^ 40 * 5136093 * 2
def baseEnd_5136093 : Nat := 879094798397626248739015

theorem tailTrace_5136093 : CollatzResearch.WordTrace tailWord_5136093 prefixEnd_5136093 879094798397626248739015 := by
  unfold tailWord_5136093
  simp only [CollatzResearch.WordTrace]
  refine ⟨187328701381819710694052933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124885800921213140462701955 187328701381819710694052933)
  ·
    refine ⟨35124131509091195755134925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187328701381819710694052933 35124131509091195755134925)
    ·
      refine ⟨13171549315909198408175597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35124131509091195755134925 13171549315909198408175597)
      ·
        refine ⟨4939330993465949403065849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13171549315909198408175597 4939330993465949403065849)
        ·
          refine ⟨3704498245099462052299387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4939330993465949403065849 3704498245099462052299387)
          ·
            refine ⟨5556747367649193078449081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704498245099462052299387 5556747367649193078449081)
            ·
              refine ⟨4167560525736894808836811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5556747367649193078449081 4167560525736894808836811)
              ·
                refine ⟨6251340788605342213255217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167560525736894808836811 6251340788605342213255217)
                ·
                  refine ⟨4688505591454006659941413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6251340788605342213255217 4688505591454006659941413)
                  ·
                    refine ⟨879094798397626248739015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4688505591454006659941413 879094798397626248739015)
                    ·
                      rfl

theorem cell23_5136093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_5136093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136093 prefixEnd_5136093 := by exact prefixLift 5136093
  have htrace : WordTrace (prefixWord ++ tailWord_5136093) baseStart_5136093 baseEnd_5136093 := by
    simpa [prefixWord, tailWord_5136093, baseEnd_5136093] using wordTrace_append hprefix tailTrace_5136093
  have hstable : (prefixWord ++ tailWord_5136093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136093).length < 2 ^ (prefixWord ++ tailWord_5136093).sum := by decide
  have hdescent : baseEnd_5136093 < baseStart_5136093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136099 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5136099 : Nat := 118140960795 + 5136099 * 2 ^ 59
def prefixEnd_5136099 : Nat := 4983230072969 + 3 ^ 40 * 5136099 * 2
def baseEnd_5136099 : Nat := 2637287476076805722742017

theorem tailTrace_5136099 : CollatzResearch.WordTrace tailWord_5136099 prefixEnd_5136099 2637287476076805722742017 := by
  unfold tailWord_5136099
  simp only [CollatzResearch.WordTrace]
  refine ⟨187328920219797973718771351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124885946813198649145847567 187328920219797973718771351)
  ·
    refine ⟨280993380329696960578157027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187328920219797973718771351 280993380329696960578157027)
    ·
      refine ⟨421490070494545440867235541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280993380329696960578157027 421490070494545440867235541)
      ·
        refine ⟨9878673527215908770325833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 421490070494545440867235541 9878673527215908770325833)
        ·
          refine ⟨7409005145411931577744375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9878673527215908770325833 7409005145411931577744375)
          ·
            refine ⟨11113507718117897366616563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7409005145411931577744375 11113507718117897366616563)
            ·
              refine ⟨16670261577176846049924845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11113507718117897366616563 16670261577176846049924845)
              ·
                refine ⟨6251348091441317268721817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16670261577176846049924845 6251348091441317268721817)
                ·
                  refine ⟨4688511068580987951541363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6251348091441317268721817 4688511068580987951541363)
                  ·
                    refine ⟨7032766602871481927312045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4688511068580987951541363 7032766602871481927312045)
                    ·
                      refine ⟨2637287476076805722742017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7032766602871481927312045 2637287476076805722742017)
                      ·
                        rfl

theorem cell23_5136099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5136099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136099 prefixEnd_5136099 := by exact prefixLift 5136099
  have htrace : WordTrace (prefixWord ++ tailWord_5136099) baseStart_5136099 baseEnd_5136099 := by
    simpa [prefixWord, tailWord_5136099, baseEnd_5136099] using wordTrace_append hprefix tailTrace_5136099
  have hstable : (prefixWord ++ tailWord_5136099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136099).length < 2 ^ (prefixWord ++ tailWord_5136099).sum := by decide
  have hdescent : baseEnd_5136099 < baseStart_5136099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136105 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 1, 4, 2]
def baseStart_5136105 : Nat := 118140960795 + 5136105 * 2 ^ 59
def prefixEnd_5136105 : Nat := 4983230072969 + 3 ^ 40 * 5136105 * 2
def baseEnd_5136105 : Nat := 2637290556960732699266989

theorem tailTrace_5136105 : CollatzResearch.WordTrace tailWord_5136105 prefixEnd_5136105 2637290556960732699266989 := by
  unfold tailWord_5136105
  simp only [CollatzResearch.WordTrace]
  refine ⟨187329139057776236743489769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124886092705184157828993179 187329139057776236743489769)
  ·
    refine ⟨140496854293332177557617327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187329139057776236743489769 140496854293332177557617327)
    ·
      refine ⟨210745281439998266336425991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140496854293332177557617327 210745281439998266336425991)
      ·
        refine ⟨316117922159997399504638987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210745281439998266336425991 316117922159997399504638987)
        ·
          refine ⟨474176883239996099256958481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316117922159997399504638987 474176883239996099256958481)
          ·
            refine ⟨355632662429997074442718861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474176883239996099256958481 355632662429997074442718861)
            ·
              refine ⟨133362248411248902916019573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 355632662429997074442718861 133362248411248902916019573)
              ·
                refine ⟨12502710788554584648376835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133362248411248902916019573 12502710788554584648376835)
                ·
                  refine ⟨18754066182831876972565253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12502710788554584648376835 18754066182831876972565253)
                  ·
                    refine ⟨3516387409280976932355985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18754066182831876972565253 3516387409280976932355985)
                    ·
                      refine ⟨2637290556960732699266989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516387409280976932355985 2637290556960732699266989)
                      ·
                        rfl

theorem cell23_5136105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 4, 2].length) (baseStart_5136105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136105 prefixEnd_5136105 := by exact prefixLift 5136105
  have htrace : WordTrace (prefixWord ++ tailWord_5136105) baseStart_5136105 baseEnd_5136105 := by
    simpa [prefixWord, tailWord_5136105, baseEnd_5136105] using wordTrace_append hprefix tailTrace_5136105
  have hstable : (prefixWord ++ tailWord_5136105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136105).length < 2 ^ (prefixWord ++ tailWord_5136105).sum := by decide
  have hdescent : baseEnd_5136105 < baseStart_5136105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136108 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_5136108 : Nat := 118140960795 + 5136108 * 2 ^ 59
def prefixEnd_5136108 : Nat := 4983230072969 + 3 ^ 40 * 5136108 * 2
def baseEnd_5136108 : Nat := 2637292097402696187529475

theorem tailTrace_5136108 : CollatzResearch.WordTrace tailWord_5136108 prefixEnd_5136108 2637292097402696187529475 := by
  unfold tailWord_5136108
  simp only [CollatzResearch.WordTrace]
  refine ⟨93664624238382684127924489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124886165651176912170565985 93664624238382684127924489)
  ·
    refine ⟨70248468178787013095943367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93664624238382684127924489 70248468178787013095943367)
    ·
      refine ⟨105372702268180519643915051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70248468178787013095943367 105372702268180519643915051)
      ·
        refine ⟨158059053402270779465872577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105372702268180519643915051 158059053402270779465872577)
        ·
          refine ⟨118544290051703084599404433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158059053402270779465872577 118544290051703084599404433)
          ·
            refine ⟨88908217538777313449553325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118544290051703084599404433 88908217538777313449553325)
            ·
              refine ⟨33340581577041492543582497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88908217538777313449553325 33340581577041492543582497)
              ·
                refine ⟨25005436182781119407686873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33340581577041492543582497 25005436182781119407686873)
                ·
                  refine ⟨18754077137085839555765155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25005436182781119407686873 18754077137085839555765155)
                  ·
                    refine ⟨28131115705628759333647733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18754077137085839555765155 28131115705628759333647733)
                    ·
                      refine ⟨2637292097402696187529475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28131115705628759333647733 2637292097402696187529475)
                      ·
                        rfl

theorem cell23_5136108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_5136108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136108 prefixEnd_5136108 := by exact prefixLift 5136108
  have htrace : WordTrace (prefixWord ++ tailWord_5136108) baseStart_5136108 baseEnd_5136108 := by
    simpa [prefixWord, tailWord_5136108, baseEnd_5136108] using wordTrace_append hprefix tailTrace_5136108
  have hstable : (prefixWord ++ tailWord_5136108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136108).length < 2 ^ (prefixWord ++ tailWord_5136108).sum := by decide
  have hdescent : baseEnd_5136108 < baseStart_5136108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136109 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_5136109 : Nat := 118140960795 + 5136109 * 2 ^ 59
def prefixEnd_5136109 : Nat := 4983230072969 + 3 ^ 40 * 5136109 * 2
def baseEnd_5136109 : Nat := 2637292610883350683616971

theorem tailTrace_5136109 : CollatzResearch.WordTrace tailWord_5136109 prefixEnd_5136109 2637292610883350683616971 := by
  unfold tailWord_5136109
  simp only [CollatzResearch.WordTrace]
  refine ⟨187329284949761745426635381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124886189966507830284423587 187329284949761745426635381)
  ·
    refine ⟨17562120464040163633747067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187329284949761745426635381 17562120464040163633747067)
    ·
      refine ⟨26343180696060245450620601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17562120464040163633747067 26343180696060245450620601)
      ·
        refine ⟨19757385522045184087965451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26343180696060245450620601 19757385522045184087965451)
        ·
          refine ⟨29636078283067776131948177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19757385522045184087965451 29636078283067776131948177)
          ·
            refine ⟨22227058712300832098961133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29636078283067776131948177 22227058712300832098961133)
            ·
              refine ⟨8335147017112812037110425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22227058712300832098961133 8335147017112812037110425)
              ·
                refine ⟨6251360262834609027832819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8335147017112812037110425 6251360262834609027832819)
                ·
                  refine ⟨9377040394251913541749229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6251360262834609027832819 9377040394251913541749229)
                  ·
                    refine ⟨3516390147844467578155961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9377040394251913541749229 3516390147844467578155961)
                    ·
                      refine ⟨2637292610883350683616971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516390147844467578155961 2637292610883350683616971)
                      ·
                        rfl

theorem cell23_5136109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_5136109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136109 prefixEnd_5136109 := by exact prefixLift 5136109
  have htrace : WordTrace (prefixWord ++ tailWord_5136109) baseStart_5136109 baseEnd_5136109 := by
    simpa [prefixWord, tailWord_5136109, baseEnd_5136109] using wordTrace_append hprefix tailTrace_5136109
  have hstable : (prefixWord ++ tailWord_5136109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136109).length < 2 ^ (prefixWord ++ tailWord_5136109).sum := by decide
  have hdescent : baseEnd_5136109 < baseStart_5136109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136134 : List Nat := [6, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5136134 : Nat := 118140960795 + 5136134 * 2 ^ 59
def prefixEnd_5136134 : Nat := 4983230072969 + 3 ^ 40 * 5136134 * 2
def baseEnd_5136134 : Nat := 2637305447899713085804357

theorem tailTrace_5136134 : CollatzResearch.WordTrace tailWord_5136134 prefixEnd_5136134 2637305447899713085804357 := by
  unfold tailWord_5136134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854068649208474209259233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124886797849780783130863637 5854068649208474209259233)
  ·
    refine ⟨4390551486906355656944425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5854068649208474209259233 4390551486906355656944425)
    ·
      refine ⟨3292913615179766742708319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4390551486906355656944425 3292913615179766742708319)
      ·
        refine ⟨4939370422769650114062479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3292913615179766742708319 4939370422769650114062479)
        ·
          refine ⟨7409055634154475171093719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4939370422769650114062479 7409055634154475171093719)
          ·
            refine ⟨11113583451231712756640579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7409055634154475171093719 11113583451231712756640579)
            ·
              refine ⟨16670375176847569134960869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11113583451231712756640579 16670375176847569134960869)
              ·
                refine ⟨3125695345658919212805163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16670375176847569134960869 3125695345658919212805163)
                ·
                  refine ⟨4688543018488378819207745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125695345658919212805163 4688543018488378819207745)
                  ·
                    refine ⟨3516407263866284114405809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4688543018488378819207745 3516407263866284114405809)
                    ·
                      refine ⟨2637305447899713085804357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516407263866284114405809 2637305447899713085804357)
                      ·
                        rfl

theorem cell23_5136134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5136134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136134 prefixEnd_5136134 := by exact prefixLift 5136134
  have htrace : WordTrace (prefixWord ++ tailWord_5136134) baseStart_5136134 baseEnd_5136134 := by
    simpa [prefixWord, tailWord_5136134, baseEnd_5136134] using wordTrace_append hprefix tailTrace_5136134
  have hstable : (prefixWord ++ tailWord_5136134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136134).length < 2 ^ (prefixWord ++ tailWord_5136134).sum := by decide
  have hdescent : baseEnd_5136134 < baseStart_5136134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136208 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_5136208 : Nat := 118140960795 + 5136208 * 2 ^ 59
def prefixEnd_5136208 : Nat := 4983230072969 + 3 ^ 40 * 5136208 * 2
def baseEnd_5136208 : Nat := 2637343445468145796279015

theorem tailTrace_5136208 : CollatzResearch.WordTrace tailWord_5136208 prefixEnd_5136208 2637343445468145796279015 := by
  unfold tailWord_5136208
  simp only [CollatzResearch.WordTrace]
  refine ⟨93666447888201542667244639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124888597184268723556326185 93666447888201542667244639)
  ·
    refine ⟨140499671832302314000866959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93666447888201542667244639 140499671832302314000866959)
    ·
      refine ⟨210749507748453471001300439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140499671832302314000866959 210749507748453471001300439)
      ·
        refine ⟨316124261622680206501950659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210749507748453471001300439 316124261622680206501950659)
        ·
          refine ⟨474186392434020309752925989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316124261622680206501950659 474186392434020309752925989)
          ·
            refine ⟨88909948581378808078673623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 474186392434020309752925989 88909948581378808078673623)
            ·
              refine ⟨133364922872068212118010435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88909948581378808078673623 133364922872068212118010435)
              ·
                refine ⟨200047384308102318177015653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133364922872068212118010435 200047384308102318177015653)
                ·
                  refine ⟨37508884557769184658190435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200047384308102318177015653 37508884557769184658190435)
                  ·
                    refine ⟨56263326836653776987285653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37508884557769184658190435 56263326836653776987285653)
                    ·
                      refine ⟨2637343445468145796279015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56263326836653776987285653 2637343445468145796279015)
                      ·
                        rfl

theorem cell23_5136208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_5136208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136208 prefixEnd_5136208 := by exact prefixLift 5136208
  have htrace : WordTrace (prefixWord ++ tailWord_5136208) baseStart_5136208 baseEnd_5136208 := by
    simpa [prefixWord, tailWord_5136208, baseEnd_5136208] using wordTrace_append hprefix tailTrace_5136208
  have hstable : (prefixWord ++ tailWord_5136208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136208).length < 2 ^ (prefixWord ++ tailWord_5136208).sum := by decide
  have hdescent : baseEnd_5136208 < baseStart_5136208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136232 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_5136232 : Nat := 118140960795 + 5136232 * 2 ^ 59
def prefixEnd_5136232 : Nat := 4983230072969 + 3 ^ 40 * 5136232 * 2
def baseEnd_5136232 : Nat := 2637355769003853702378905

theorem tailTrace_5136232 : CollatzResearch.WordTrace tailWord_5136232 prefixEnd_5136232 2637355769003853702378905 := by
  unfold tailWord_5136232
  simp only [CollatzResearch.WordTrace]
  refine ⟨93666885564158068716681475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124889180752210758288908633 93666885564158068716681475)
  ·
    refine ⟨140500328346237103075022213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93666885564158068716681475 140500328346237103075022213)
    ·
      refine ⟨26343811564919456826566665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140500328346237103075022213 26343811564919456826566665)
      ·
        refine ⟨19757858673689592619924999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26343811564919456826566665 19757858673689592619924999)
        ·
          refine ⟨29636788010534388929887499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19757858673689592619924999 29636788010534388929887499)
          ·
            refine ⟨44455182015801583394831249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29636788010534388929887499 44455182015801583394831249)
            ·
              refine ⟨33341386511851187546123437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44455182015801583394831249 33341386511851187546123437)
              ·
                refine ⟨12503019941944195329796289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33341386511851187546123437 12503019941944195329796289)
                ·
                  refine ⟨9377264956458146497347217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12503019941944195329796289 9377264956458146497347217)
                  ·
                    refine ⟨7032948717343609873010413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9377264956458146497347217 7032948717343609873010413)
                    ·
                      refine ⟨2637355769003853702378905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7032948717343609873010413 2637355769003853702378905)
                      ·
                        rfl

theorem cell23_5136232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_5136232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136232 prefixEnd_5136232 := by exact prefixLift 5136232
  have htrace : WordTrace (prefixWord ++ tailWord_5136232) baseStart_5136232 baseEnd_5136232 := by
    simpa [prefixWord, tailWord_5136232, baseEnd_5136232] using wordTrace_append hprefix tailTrace_5136232
  have hstable : (prefixWord ++ tailWord_5136232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136232).length < 2 ^ (prefixWord ++ tailWord_5136232).sum := by decide
  have hdescent : baseEnd_5136232 < baseStart_5136232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136248 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 11]
def baseStart_5136248 : Nat := 118140960795 + 5136248 * 2 ^ 59
def prefixEnd_5136248 : Nat := 4983230072969 + 3 ^ 40 * 5136248 * 2
def baseEnd_5136248 : Nat := 879121328231441879926277

theorem tailTrace_5136248 : CollatzResearch.WordTrace tailWord_5136248 prefixEnd_5136248 879121328231441879926277 := by
  unfold tailWord_5136248
  simp only [CollatzResearch.WordTrace]
  refine ⟨93667177348129086082972699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124889569797505448110630265 93667177348129086082972699)
  ·
    refine ⟨140500766022193629124459049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93667177348129086082972699 140500766022193629124459049)
    ·
      refine ⟨105375574516645221843344287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140500766022193629124459049 105375574516645221843344287)
      ·
        refine ⟨158063361774967832765016431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105375574516645221843344287 158063361774967832765016431)
        ·
          refine ⟨237095042662451749147524647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158063361774967832765016431 237095042662451749147524647)
          ·
            refine ⟨355642563993677623721286971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237095042662451749147524647 355642563993677623721286971)
            ·
              refine ⟨533463845990516435581930457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355642563993677623721286971 533463845990516435581930457)
              ·
                refine ⟨400097884492887326686447843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533463845990516435581930457 400097884492887326686447843)
                ·
                  refine ⟨600146826739330990029671765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400097884492887326686447843 600146826739330990029671765)
                  ·
                    refine ⟨879121328231441879926277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 600146826739330990029671765 879121328231441879926277)
                    ·
                      rfl

theorem cell23_5136248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_5136248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136248 prefixEnd_5136248 := by exact prefixLift 5136248
  have htrace : WordTrace (prefixWord ++ tailWord_5136248) baseStart_5136248 baseEnd_5136248 := by
    simpa [prefixWord, tailWord_5136248, baseEnd_5136248] using wordTrace_append hprefix tailTrace_5136248
  have hstable : (prefixWord ++ tailWord_5136248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136248).length < 2 ^ (prefixWord ++ tailWord_5136248).sum := by decide
  have hdescent : baseEnd_5136248 < baseStart_5136248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136265 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 3, 5]
def baseStart_5136265 : Nat := 118140960795 + 5136265 * 2 ^ 59
def prefixEnd_5136265 : Nat := 4983230072969 + 3 ^ 40 * 5136265 * 2
def baseEnd_5136265 : Nat := 879124237955150691088751

theorem tailTrace_5136265 : CollatzResearch.WordTrace tailWord_5136265 prefixEnd_5136265 879124237955150691088751 := by
  unfold tailWord_5136265
  simp only [CollatzResearch.WordTrace]
  refine ⟨187334974737196584069314249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124889983158131056046209499 187334974737196584069314249)
  ·
    refine ⟨140501231052897438051985687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187334974737196584069314249 140501231052897438051985687)
    ·
      refine ⟨210751846579346157077978531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140501231052897438051985687 210751846579346157077978531)
      ·
        refine ⟨316127769869019235616967797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210751846579346157077978531 316127769869019235616967797)
        ·
          refine ⟨29636978425220553339090731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 316127769869019235616967797 29636978425220553339090731)
          ·
            refine ⟨44455467637830830008636097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29636978425220553339090731 44455467637830830008636097)
            ·
              refine ⟨33341600728373122506477073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44455467637830830008636097 33341600728373122506477073)
              ·
                refine ⟨25006200546279841879857805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33341600728373122506477073 25006200546279841879857805)
                ·
                  refine ⟨9377325204854940704946677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25006200546279841879857805 9377325204854940704946677)
                  ·
                    refine ⟨879124237955150691088751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9377325204854940704946677 879124237955150691088751)
                    ·
                      rfl

theorem cell23_5136265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_5136265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136265 prefixEnd_5136265 := by exact prefixLift 5136265
  have htrace : WordTrace (prefixWord ++ tailWord_5136265) baseStart_5136265 baseEnd_5136265 := by
    simpa [prefixWord, tailWord_5136265, baseEnd_5136265] using wordTrace_append hprefix tailTrace_5136265
  have hstable : (prefixWord ++ tailWord_5136265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136265).length < 2 ^ (prefixWord ++ tailWord_5136265).sum := by decide
  have hdescent : baseEnd_5136265 < baseStart_5136265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136282 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_5136282 : Nat := 118140960795 + 5136282 * 2 ^ 59
def prefixEnd_5136282 : Nat := 4983230072969 + 3 ^ 40 * 5136282 * 2
def baseEnd_5136282 : Nat := 879127147678859502251225

theorem tailTrace_5136282 : CollatzResearch.WordTrace tailWord_5136282 prefixEnd_5136282 879127147678859502251225 := by
  unfold tailWord_5136282
  simp only [CollatzResearch.WordTrace]
  refine ⟨46833898694533748993170775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124890396518756663981788733 46833898694533748993170775)
  ·
    refine ⟨70250848041800623489756163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46833898694533748993170775 70250848041800623489756163)
    ·
      refine ⟨105376272062700935234634245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70250848041800623489756163 105376272062700935234634245)
      ·
        refine ⟨19758051011756425356493921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105376272062700935234634245 19758051011756425356493921)
        ·
          refine ⟨14818538258817319017370441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19758051011756425356493921 14818538258817319017370441)
          ·
            refine ⟨11113903694112989263027831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14818538258817319017370441 11113903694112989263027831)
            ·
              refine ⟨16670855541169483894541747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11113903694112989263027831 16670855541169483894541747)
              ·
                refine ⟨25006283311754225841812621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16670855541169483894541747 25006283311754225841812621)
                ·
                  refine ⟨9377356241907834690679733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25006283311754225841812621 9377356241907834690679733)
                  ·
                    refine ⟨879127147678859502251225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9377356241907834690679733 879127147678859502251225)
                    ·
                      rfl

theorem cell23_5136282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_5136282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136282 prefixEnd_5136282 := by exact prefixLift 5136282
  have htrace : WordTrace (prefixWord ++ tailWord_5136282) baseStart_5136282 baseEnd_5136282 := by
    simpa [prefixWord, tailWord_5136282, baseEnd_5136282] using wordTrace_append hprefix tailTrace_5136282
  have hstable : (prefixWord ++ tailWord_5136282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136282).length < 2 ^ (prefixWord ++ tailWord_5136282).sum := by decide
  have hdescent : baseEnd_5136282 < baseStart_5136282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136319 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 3, 2, 2]
def baseStart_5136319 : Nat := 118140960795 + 5136319 * 2 ^ 59
def prefixEnd_5136319 : Nat := 4983230072969 + 3 ^ 40 * 5136319 * 2
def baseEnd_5136319 : Nat := 2637400441820794861991005

theorem tailTrace_5136319 : CollatzResearch.WordTrace tailWord_5136319 prefixEnd_5136319 2637400441820794861991005 := by
  unfold tailWord_5136319
  simp only [CollatzResearch.WordTrace]
  refine ⟨187336944279000951291780011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124891296186000634194520007 187336944279000951291780011)
  ·
    refine ⟨281005416418501426937670017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187336944279000951291780011 281005416418501426937670017)
    ·
      refine ⟨210754062313876070203252513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281005416418501426937670017 210754062313876070203252513)
      ·
        refine ⟨158065546735407052652439385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210754062313876070203252513 158065546735407052652439385)
        ·
          refine ⟨118549160051555289489329539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158065546735407052652439385 118549160051555289489329539)
          ·
            refine ⟨177823740077332934233994309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118549160051555289489329539 177823740077332934233994309)
            ·
              refine ⟨33341951264499925168873933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177823740077332934233994309 33341951264499925168873933)
              ·
                refine ⟨12503231724187471938327725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33341951264499925168873933 12503231724187471938327725)
                ·
                  refine ⟨4688711896570301976872897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12503231724187471938327725 4688711896570301976872897)
                  ·
                    refine ⟨3516533922427726482654673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4688711896570301976872897 3516533922427726482654673)
                    ·
                      refine ⟨2637400441820794861991005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516533922427726482654673 2637400441820794861991005)
                      ·
                        rfl

theorem cell23_5136319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_5136319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136319 prefixEnd_5136319 := by exact prefixLift 5136319
  have htrace : WordTrace (prefixWord ++ tailWord_5136319) baseStart_5136319 baseEnd_5136319 := by
    simpa [prefixWord, tailWord_5136319, baseEnd_5136319] using wordTrace_append hprefix tailTrace_5136319
  have hstable : (prefixWord ++ tailWord_5136319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136319).length < 2 ^ (prefixWord ++ tailWord_5136319).sum := by decide
  have hdescent : baseEnd_5136319 < baseStart_5136319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136332 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5136332 : Nat := 118140960795 + 5136332 * 2 ^ 59
def prefixEnd_5136332 : Nat := 4983230072969 + 3 ^ 40 * 5136332 * 2
def baseEnd_5136332 : Nat := 2637407117069303311128445

theorem tailTrace_5136332 : CollatzResearch.WordTrace tailWord_5136332 prefixEnd_5136332 2637407117069303311128445 := by
  unfold tailWord_5136332
  simp only [CollatzResearch.WordTrace]
  refine ⟨93668709213976927256001625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124891612285302569674668833 93668709213976927256001625)
  ·
    refine ⟨70251531910482695442001219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93668709213976927256001625 70251531910482695442001219)
    ·
      refine ⟨105377297865724043163001829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70251531910482695442001219 105377297865724043163001829)
      ·
        refine ⟨19758243349823258093062843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105377297865724043163001829 19758243349823258093062843)
        ·
          refine ⟨29637365024734887139594265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19758243349823258093062843 29637365024734887139594265)
          ·
            refine ⟨22228023768551165354695699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29637365024734887139594265 22228023768551165354695699)
            ·
              refine ⟨33342035652826748032043549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22228023768551165354695699 33342035652826748032043549)
              ·
                refine ⟨12503263369810030512016331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33342035652826748032043549 12503263369810030512016331)
                ·
                  refine ⟨18754895054715045768024497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12503263369810030512016331 18754895054715045768024497)
                  ·
                    refine ⟨14066171291036284326018373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18754895054715045768024497 14066171291036284326018373)
                    ·
                      refine ⟨2637407117069303311128445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14066171291036284326018373 2637407117069303311128445)
                      ·
                        rfl

theorem cell23_5136332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5136332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136332 prefixEnd_5136332 := by exact prefixLift 5136332
  have htrace : WordTrace (prefixWord ++ tailWord_5136332) baseStart_5136332 baseEnd_5136332 := by
    simpa [prefixWord, tailWord_5136332, baseEnd_5136332] using wordTrace_append hprefix tailTrace_5136332
  have hstable : (prefixWord ++ tailWord_5136332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136332).length < 2 ^ (prefixWord ++ tailWord_5136332).sum := by decide
  have hdescent : baseEnd_5136332 < baseStart_5136332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136396 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 1, 3, 2]
def baseStart_5136396 : Nat := 118140960795 + 5136396 * 2 ^ 59
def prefixEnd_5136396 : Nat := 4983230072969 + 3 ^ 40 * 5136396 * 2
def baseEnd_5136396 : Nat := 2637439979831191060728151

theorem tailTrace_5136396 : CollatzResearch.WordTrace tailWord_5136396 prefixEnd_5136396 2637439979831191060728151 := by
  unfold tailWord_5136396
  simp only [CollatzResearch.WordTrace]
  refine ⟨93669876349860996721166521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124893168466481328961555361 93669876349860996721166521)
  ·
    refine ⟨70252407262395747540874891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93669876349860996721166521 70252407262395747540874891)
    ·
      refine ⟨105378610893593621311312337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70252407262395747540874891 105378610893593621311312337)
      ·
        refine ⟨79033958170195215983484253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105378610893593621311312337 79033958170195215983484253)
        ·
          refine ⟨29637734313823205993806595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79033958170195215983484253 29637734313823205993806595)
          ·
            refine ⟨44456601470734808990709893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29637734313823205993806595 44456601470734808990709893)
            ·
              refine ⟨8335612775762776685758105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44456601470734808990709893 8335612775762776685758105)
              ·
                refine ⟨6251709581822082514318579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8335612775762776685758105 6251709581822082514318579)
                ·
                  refine ⟨9377564372733123771477869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6251709581822082514318579 9377564372733123771477869)
                  ·
                    refine ⟨3516586639774921414304201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9377564372733123771477869 3516586639774921414304201)
                    ·
                      refine ⟨2637439979831191060728151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516586639774921414304201 2637439979831191060728151)
                      ·
                        rfl

theorem cell23_5136396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_5136396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136396 prefixEnd_5136396 := by exact prefixLift 5136396
  have htrace : WordTrace (prefixWord ++ tailWord_5136396) baseStart_5136396 baseEnd_5136396 := by
    simpa [prefixWord, tailWord_5136396, baseEnd_5136396] using wordTrace_append hprefix tailTrace_5136396
  have hstable : (prefixWord ++ tailWord_5136396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136396).length < 2 ^ (prefixWord ++ tailWord_5136396).sum := by decide
  have hdescent : baseEnd_5136396 < baseStart_5136396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136404 : List Nat := [2, 4, 3, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5136404 : Nat := 118140960795 + 5136404 * 2 ^ 59
def prefixEnd_5136404 : Nat := 4983230072969 + 3 ^ 40 * 5136404 * 2
def baseEnd_5136404 : Nat := 2637444087676427029428115

theorem tailTrace_5136404 : CollatzResearch.WordTrace tailWord_5136404 prefixEnd_5136404 2637444087676427029428115 := by
  unfold tailWord_5136404
  simp only [CollatzResearch.WordTrace]
  refine ⟨93670022241846505404312133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124893362989128673872416177 93670022241846505404312133)
  ·
    refine ⟨17563129170346219763308525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93670022241846505404312133 17563129170346219763308525)
    ·
      refine ⟨6586173438879832411240697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17563129170346219763308525 6586173438879832411240697)
      ·
        refine ⟨4939630079159874308430523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6586173438879832411240697 4939630079159874308430523)
        ·
          refine ⟨7409445118739811462645785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4939630079159874308430523 7409445118739811462645785)
          ·
            refine ⟨5557083839054858596984339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7409445118739811462645785 5557083839054858596984339)
            ·
              refine ⟨8335625758582287895476509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557083839054858596984339 8335625758582287895476509)
              ·
                refine ⟨3125859659468357960803691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8335625758582287895476509 3125859659468357960803691)
                ·
                  refine ⟨4688789489202536941205537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125859659468357960803691 4688789489202536941205537)
                  ·
                    refine ⟨3516592116901902705904153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4688789489202536941205537 3516592116901902705904153)
                    ·
                      refine ⟨2637444087676427029428115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516592116901902705904153 2637444087676427029428115)
                      ·
                        rfl

theorem cell23_5136404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5136404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136404 prefixEnd_5136404 := by exact prefixLift 5136404
  have htrace : WordTrace (prefixWord ++ tailWord_5136404) baseStart_5136404 baseEnd_5136404 := by
    simpa [prefixWord, tailWord_5136404, baseEnd_5136404] using wordTrace_append hprefix tailTrace_5136404
  have hstable : (prefixWord ++ tailWord_5136404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136404).length < 2 ^ (prefixWord ++ tailWord_5136404).sum := by decide
  have hdescent : baseEnd_5136404 < baseStart_5136404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136412 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_5136412 : Nat := 118140960795 + 5136412 * 2 ^ 59
def prefixEnd_5136412 : Nat := 4983230072969 + 3 ^ 40 * 5136412 * 2
def baseEnd_5136412 : Nat := 2637448195521662998128077

theorem tailTrace_5136412 : CollatzResearch.WordTrace tailWord_5136412 prefixEnd_5136412 2637448195521662998128077 := by
  unfold tailWord_5136412
  simp only [CollatzResearch.WordTrace]
  refine ⟨93670168133832014087457745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124893557511776018783276993 93670168133832014087457745)
  ·
    refine ⟨70252626100374010565593309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93670168133832014087457745 70252626100374010565593309)
    ·
      refine ⟨26344734787640253962097491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70252626100374010565593309 26344734787640253962097491)
      ·
        refine ⟨39517102181460380943146237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26344734787640253962097491 39517102181460380943146237)
        ·
          refine ⟨14818913318047642853679839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39517102181460380943146237 14818913318047642853679839)
          ·
            refine ⟨22228369977071464280519759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14818913318047642853679839 22228369977071464280519759)
            ·
              refine ⟨33342554965607196420779639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22228369977071464280519759 33342554965607196420779639)
              ·
                refine ⟨50013832448410794631169459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33342554965607196420779639 50013832448410794631169459)
                ·
                  refine ⟨75020748672616191946754189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50013832448410794631169459 75020748672616191946754189)
                  ·
                    refine ⟨28132780752231071980032821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75020748672616191946754189 28132780752231071980032821)
                    ·
                      refine ⟨2637448195521662998128077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28132780752231071980032821 2637448195521662998128077)
                      ·
                        rfl

theorem cell23_5136412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_5136412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136412 prefixEnd_5136412 := by exact prefixLift 5136412
  have htrace : WordTrace (prefixWord ++ tailWord_5136412) baseStart_5136412 baseEnd_5136412 := by
    simpa [prefixWord, tailWord_5136412, baseEnd_5136412] using wordTrace_append hprefix tailTrace_5136412
  have hstable : (prefixWord ++ tailWord_5136412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136412).length < 2 ^ (prefixWord ++ tailWord_5136412).sum := by decide
  have hdescent : baseEnd_5136412 < baseStart_5136412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136432 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 7]
def baseStart_5136432 : Nat := 118140960795 + 5136432 * 2 ^ 59
def prefixEnd_5136432 : Nat := 4983230072969 + 3 ^ 40 * 5136432 * 2
def baseEnd_5136432 : Nat := 293050940570528102208665

theorem tailTrace_5136432 : CollatzResearch.WordTrace tailWord_5136432 prefixEnd_5136432 293050940570528102208665 := by
  unfold tailWord_5136432
  simp only [CollatzResearch.WordTrace]
  refine ⟨93670532863795785795321775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124894043818394381060429033 93670532863795785795321775)
  ·
    refine ⟨140505799295693678692982663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93670532863795785795321775 140505799295693678692982663)
    ·
      refine ⟨210758698943540518039473995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140505799295693678692982663 210758698943540518039473995)
      ·
        refine ⟨316138048415310777059210993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210758698943540518039473995 316138048415310777059210993)
        ·
          refine ⟨237103536311483082794408245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316138048415310777059210993 237103536311483082794408245)
          ·
            refine ⟨22228456529201539011975773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237103536311483082794408245 22228456529201539011975773)
            ·
              refine ⟨8335671198450577129490915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22228456529201539011975773 8335671198450577129490915)
              ·
                refine ⟨12503506797675865694236373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8335671198450577129490915 12503506797675865694236373)
                ·
                  refine ⟨293050940570528102208665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12503506797675865694236373 293050940570528102208665)
                  ·
                    rfl

theorem cell23_5136432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 7].length) (baseStart_5136432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136432 prefixEnd_5136432 := by exact prefixLift 5136432
  have htrace : WordTrace (prefixWord ++ tailWord_5136432) baseStart_5136432 baseEnd_5136432 := by
    simpa [prefixWord, tailWord_5136432, baseEnd_5136432] using wordTrace_append hprefix tailTrace_5136432
  have hstable : (prefixWord ++ tailWord_5136432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136432).length < 2 ^ (prefixWord ++ tailWord_5136432).sum := by decide
  have hdescent : baseEnd_5136432 < baseStart_5136432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136442 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_5136442 : Nat := 118140960795 + 5136442 * 2 ^ 59
def prefixEnd_5136442 : Nat := 4983230072969 + 3 ^ 40 * 5136442 * 2
def baseEnd_5136442 : Nat := 2637463599941297880752939

theorem tailTrace_5136442 : CollatzResearch.WordTrace tailWord_5136442 prefixEnd_5136442 2637463599941297880752939 := by
  unfold tailWord_5136442
  simp only [CollatzResearch.WordTrace]
  refine ⟨46835357614388835824626895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124894286971703562199005053 46835357614388835824626895)
  ·
    refine ⟨70253036421583253736940343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46835357614388835824626895 70253036421583253736940343)
    ·
      refine ⟨105379554632374880605410515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70253036421583253736940343 105379554632374880605410515)
      ·
        refine ⟨158069331948562320908115773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105379554632374880605410515 158069331948562320908115773)
        ·
          refine ⟨59275999480710870340543415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158069331948562320908115773 59275999480710870340543415)
          ·
            refine ⟨88913999221066305510815123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59275999480710870340543415 88913999221066305510815123)
            ·
              refine ⟨133370998831599458266222685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88913999221066305510815123 133370998831599458266222685)
              ·
                refine ⟨50014124561849796849833507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133370998831599458266222685 50014124561849796849833507)
                ·
                  refine ⟨75021186842774695274750261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50014124561849796849833507 75021186842774695274750261)
                  ·
                    refine ⟨7033236266510127682007837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75021186842774695274750261 7033236266510127682007837)
                    ·
                      refine ⟨2637463599941297880752939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7033236266510127682007837 2637463599941297880752939)
                      ·
                        rfl

theorem cell23_5136442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_5136442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136442 prefixEnd_5136442 := by exact prefixLift 5136442
  have htrace : WordTrace (prefixWord ++ tailWord_5136442) baseStart_5136442 baseEnd_5136442 := by
    simpa [prefixWord, tailWord_5136442, baseEnd_5136442] using wordTrace_append hprefix tailTrace_5136442
  have hstable : (prefixWord ++ tailWord_5136442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136442).length < 2 ^ (prefixWord ++ tailWord_5136442).sum := by decide
  have hdescent : baseEnd_5136442 < baseStart_5136442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136472 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_5136472 : Nat := 118140960795 + 5136472 * 2 ^ 59
def prefixEnd_5136472 : Nat := 4983230072969 + 3 ^ 40 * 5136472 * 2
def baseEnd_5136472 : Nat := 2637479004360932763377801

theorem tailTrace_5136472 : CollatzResearch.WordTrace tailWord_5136472 prefixEnd_5136472 2637479004360932763377801 := by
  unfold tailWord_5136472
  simp only [CollatzResearch.WordTrace]
  refine ⟨93671262323723329211049835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124895016431631105614733113 93671262323723329211049835)
  ·
    refine ⟨140506893485584993816574753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93671262323723329211049835 140506893485584993816574753)
    ·
      refine ⟨105380170114188745362431065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140506893485584993816574753 105380170114188745362431065)
      ·
        refine ⟨79035127585641559021823299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105380170114188745362431065 79035127585641559021823299)
        ·
          refine ⟨118552691378462338532734949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79035127585641559021823299 118552691378462338532734949)
          ·
            refine ⟨22228629633461688474887803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118552691378462338532734949 22228629633461688474887803)
            ·
              refine ⟨33342944450192532712331705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22228629633461688474887803 33342944450192532712331705)
              ·
                refine ⟨25007208337644399534248779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33342944450192532712331705 25007208337644399534248779)
                ·
                  refine ⟨37510812506466599301373169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25007208337644399534248779 37510812506466599301373169)
                  ·
                    refine ⟨28133109379849949476029877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37510812506466599301373169 28133109379849949476029877)
                    ·
                      refine ⟨2637479004360932763377801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28133109379849949476029877 2637479004360932763377801)
                      ·
                        rfl

theorem cell23_5136472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_5136472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136472 prefixEnd_5136472 := by exact prefixLift 5136472
  have htrace : WordTrace (prefixWord ++ tailWord_5136472) baseStart_5136472 baseEnd_5136472 := by
    simpa [prefixWord, tailWord_5136472, baseEnd_5136472] using wordTrace_append hprefix tailTrace_5136472
  have hstable : (prefixWord ++ tailWord_5136472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136472).length < 2 ^ (prefixWord ++ tailWord_5136472).sum := by decide
  have hdescent : baseEnd_5136472 < baseStart_5136472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136509 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_5136509 : Nat := 118140960795 + 5136509 * 2 ^ 59
def prefixEnd_5136509 : Nat := 4983230072969 + 3 ^ 40 * 5136509 * 2
def baseEnd_5136509 : Nat := 879166001048383039538377

theorem tailTrace_5136509 : CollatzResearch.WordTrace tailWord_5136509 prefixEnd_5136509 879166001048383039538377 := by
  unfold tailWord_5136509
  simp only [CollatzResearch.WordTrace]
  refine ⟨187343874148312613741196581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124895916098875075827464387 187343874148312613741196581)
  ·
    refine ⟨35126976402808615076474359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187343874148312613741196581 35126976402808615076474359)
    ·
      refine ⟨52690464604212922614711539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35126976402808615076474359 52690464604212922614711539)
      ·
        refine ⟨79035696906319383922067309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52690464604212922614711539 79035696906319383922067309)
        ·
          refine ⟨29638386339869768970775241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79035696906319383922067309 29638386339869768970775241)
          ·
            refine ⟨22228789754902326728081431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29638386339869768970775241 22228789754902326728081431)
            ·
              refine ⟨33343184632353490092122147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22228789754902326728081431 33343184632353490092122147)
              ·
                refine ⟨50014776948530235138183221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33343184632353490092122147 50014776948530235138183221)
                ·
                  refine ⟨4688885338924709544204677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50014776948530235138183221 4688885338924709544204677)
                  ·
                    refine ⟨879166001048383039538377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4688885338924709544204677 879166001048383039538377)
                    ·
                      rfl

theorem cell23_5136509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_5136509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136509 prefixEnd_5136509 := by exact prefixLift 5136509
  have htrace : WordTrace (prefixWord ++ tailWord_5136509) baseStart_5136509 baseEnd_5136509 := by
    simpa [prefixWord, tailWord_5136509, baseEnd_5136509] using wordTrace_append hprefix tailTrace_5136509
  have hstable : (prefixWord ++ tailWord_5136509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136509).length < 2 ^ (prefixWord ++ tailWord_5136509).sum := by decide
  have hdescent : baseEnd_5136509 < baseStart_5136509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136513 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 2, 5]
def baseStart_5136513 : Nat := 118140960795 + 5136513 * 2 ^ 59
def prefixEnd_5136513 : Nat := 4983230072969 + 3 ^ 40 * 5136513 * 2
def baseEnd_5136513 : Nat := 879166685689255700988371

theorem tailTrace_5136513 : CollatzResearch.WordTrace tailWord_5136513 prefixEnd_5136513 879166685689255700988371 := by
  unfold tailWord_5136513
  simp only [CollatzResearch.WordTrace]
  refine ⟨187344020040298122424342193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124896013360198748282894795 187344020040298122424342193)
  ·
    refine ⟨140508015030223591818256645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187344020040298122424342193 140508015030223591818256645)
    ·
      refine ⟨26345252818166923465923121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140508015030223591818256645 26345252818166923465923121)
      ·
        refine ⟨19758939613625192599442341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26345252818166923465923121 19758939613625192599442341)
        ·
          refine ⟨3704801177554723612395439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19758939613625192599442341 3704801177554723612395439)
          ·
            refine ⟨5557201766332085418593159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704801177554723612395439 5557201766332085418593159)
            ·
              refine ⟨8335802649498128127889739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557201766332085418593159 8335802649498128127889739)
              ·
                refine ⟨12503703974247192191834609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8335802649498128127889739 12503703974247192191834609)
                ·
                  refine ⟨9377777980685394143875957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12503703974247192191834609 9377777980685394143875957)
                  ·
                    refine ⟨879166685689255700988371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9377777980685394143875957 879166685689255700988371)
                    ·
                      rfl

theorem cell23_5136513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_5136513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136513 prefixEnd_5136513 := by exact prefixLift 5136513
  have htrace : WordTrace (prefixWord ++ tailWord_5136513) baseStart_5136513 baseEnd_5136513 := by
    simpa [prefixWord, tailWord_5136513, baseEnd_5136513] using wordTrace_append hprefix tailTrace_5136513
  have hstable : (prefixWord ++ tailWord_5136513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136513).length < 2 ^ (prefixWord ++ tailWord_5136513).sum := by decide
  have hdescent : baseEnd_5136513 < baseStart_5136513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136543 : List Nat := [1, 1, 2, 6, 1, 1, 2, 4, 1, 4]
def baseStart_5136543 : Nat := 118140960795 + 5136543 * 2 ^ 59
def prefixEnd_5136543 : Nat := 4983230072969 + 3 ^ 40 * 5136543 * 2
def baseEnd_5136543 : Nat := 879171820495800661863325

theorem tailTrace_5136543 : CollatzResearch.WordTrace tailWord_5136543 prefixEnd_5136543 879171820495800661863325 := by
  unfold tailWord_5136543
  simp only [CollatzResearch.WordTrace]
  refine ⟨187345114230189437547934283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124896742820126291698622855 187345114230189437547934283)
  ·
    refine ⟨281017671345284156321901425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187345114230189437547934283 281017671345284156321901425)
    ·
      refine ⟨210763253508963117241426069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281017671345284156321901425 210763253508963117241426069)
      ·
        refine ⟨9879527508232646120691847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 210763253508963117241426069 9879527508232646120691847)
        ·
          refine ⟨14819291262348969181037771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9879527508232646120691847 14819291262348969181037771)
          ·
            refine ⟨22228936893523453771556657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14819291262348969181037771 22228936893523453771556657)
            ·
              refine ⟨16671702670142590328667493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22228936893523453771556657 16671702670142590328667493)
              ·
                refine ⟨3125944250651735686625155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16671702670142590328667493 3125944250651735686625155)
                ·
                  refine ⟨4688916375977603529937733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125944250651735686625155 4688916375977603529937733)
                  ·
                    refine ⟨879171820495800661863325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4688916375977603529937733 879171820495800661863325)
                    ·
                      rfl

theorem cell23_5136543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 4].length) (baseStart_5136543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136543 prefixEnd_5136543 := by exact prefixLift 5136543
  have htrace : WordTrace (prefixWord ++ tailWord_5136543) baseStart_5136543 baseEnd_5136543 := by
    simpa [prefixWord, tailWord_5136543, baseEnd_5136543] using wordTrace_append hprefix tailTrace_5136543
  have hstable : (prefixWord ++ tailWord_5136543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136543).length < 2 ^ (prefixWord ++ tailWord_5136543).sum := by decide
  have hdescent : baseEnd_5136543 < baseStart_5136543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136576 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 1, 5, 2]
def baseStart_5136576 : Nat := 118140960795 + 5136576 * 2 ^ 59
def prefixEnd_5136576 : Nat := 4983230072969 + 3 ^ 40 * 5136576 * 2
def baseEnd_5136576 : Nat := 2637532406349000356477323

theorem tailTrace_5136576 : CollatzResearch.WordTrace tailWord_5136576 prefixEnd_5136576 2637532406349000356477323 := by
  unfold tailWord_5136576
  simp only [CollatzResearch.WordTrace]
  refine ⟨93673158919534942091942791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124897545226046589455923721 93673158919534942091942791)
  ·
    refine ⟨140509738379302413137914187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93673158919534942091942791 140509738379302413137914187)
    ·
      refine ⟨210764607568953619706871281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140509738379302413137914187 210764607568953619706871281)
      ·
        refine ⟨158073455676715214780153461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210764607568953619706871281 158073455676715214780153461)
        ·
          refine ⟨14819386469692051385639387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158073455676715214780153461 14819386469692051385639387)
          ·
            refine ⟨22229079704538077078459081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14819386469692051385639387 22229079704538077078459081)
            ·
              refine ⟨16671809778403557808844311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22229079704538077078459081 16671809778403557808844311)
              ·
                refine ⟨25007714667605336713266467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16671809778403557808844311 25007714667605336713266467)
                ·
                  refine ⟨37511572001408005069899701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25007714667605336713266467 37511572001408005069899701)
                  ·
                    refine ⟨3516709875132000475303097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37511572001408005069899701 3516709875132000475303097)
                    ·
                      refine ⟨2637532406349000356477323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516709875132000475303097 2637532406349000356477323)
                      ·
                        rfl

theorem cell23_5136576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_5136576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136576 prefixEnd_5136576 := by exact prefixLift 5136576
  have htrace : WordTrace (prefixWord ++ tailWord_5136576) baseStart_5136576 baseEnd_5136576 := by
    simpa [prefixWord, tailWord_5136576, baseEnd_5136576] using wordTrace_append hprefix tailTrace_5136576
  have hstable : (prefixWord ++ tailWord_5136576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136576).length < 2 ^ (prefixWord ++ tailWord_5136576).sum := by decide
  have hdescent : baseEnd_5136576 < baseStart_5136576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136577 : List Nat := [1, 2, 6, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5136577 : Nat := 118140960795 + 5136577 * 2 ^ 59
def prefixEnd_5136577 : Nat := 4983230072969 + 3 ^ 40 * 5136577 * 2
def baseEnd_5136577 : Nat := 879177639943218284188273

theorem tailTrace_5136577 : CollatzResearch.WordTrace tailWord_5136577 prefixEnd_5136577 879177639943218284188273 := by
  unfold tailWord_5136577
  simp only [CollatzResearch.WordTrace]
  refine ⟨187346354312066261354671985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124897569541377507569781323 187346354312066261354671985)
  ·
    refine ⟨140509765734049696016003989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187346354312066261354671985 140509765734049696016003989)
    ·
      refine ⟨6586395268783579500750187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140509765734049696016003989 6586395268783579500750187)
      ·
        refine ⟨9879592903175369251125281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6586395268783579500750187 9879592903175369251125281)
        ·
          refine ⟨7409694677381526938343961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9879592903175369251125281 7409694677381526938343961)
          ·
            refine ⟨5557271008036145203757971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7409694677381526938343961 5557271008036145203757971)
            ·
              refine ⟨8335906512054217805636957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557271008036145203757971 8335906512054217805636957)
              ·
                refine ⟨3125964942020331677113859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8335906512054217805636957 3125964942020331677113859)
                ·
                  refine ⟨4688947413030497515670789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125964942020331677113859 4688947413030497515670789)
                  ·
                    refine ⟨879177639943218284188273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4688947413030497515670789 879177639943218284188273)
                    ·
                      rfl

theorem cell23_5136577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5136577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136577 prefixEnd_5136577 := by exact prefixLift 5136577
  have htrace : WordTrace (prefixWord ++ tailWord_5136577) baseStart_5136577 baseEnd_5136577 := by
    simpa [prefixWord, tailWord_5136577, baseEnd_5136577] using wordTrace_append hprefix tailTrace_5136577
  have hstable : (prefixWord ++ tailWord_5136577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136577).length < 2 ^ (prefixWord ++ tailWord_5136577).sum := by decide
  have hdescent : baseEnd_5136577 < baseStart_5136577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136609 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_5136609 : Nat := 118140960795 + 5136609 * 2 ^ 59
def prefixEnd_5136609 : Nat := 4983230072969 + 3 ^ 40 * 5136609 * 2
def baseEnd_5136609 : Nat := 2637549351210598727364671

theorem tailTrace_5136609 : CollatzResearch.WordTrace tailWord_5136609 prefixEnd_5136609 2637549351210598727364671 := by
  unfold tailWord_5136609
  simp only [CollatzResearch.WordTrace]
  refine ⟨187347521447950330819836881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124898347631966887213224587 187347521447950330819836881)
  ·
    refine ⟨140510641085962748114877661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187347521447950330819836881 140510641085962748114877661)
    ·
      refine ⟨52691490407236030543079123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140510641085962748114877661 52691490407236030543079123)
      ·
        refine ⟨79037235610854045814618685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52691490407236030543079123 79037235610854045814618685)
        ·
          refine ⟨29638963354070267180482007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79037235610854045814618685 29638963354070267180482007)
          ·
            refine ⟨44458445031105400770723011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29638963354070267180482007 44458445031105400770723011)
            ·
              refine ⟨66687667546658101156084517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44458445031105400770723011 66687667546658101156084517)
              ·
                refine ⟨12503937664998393966765847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66687667546658101156084517 12503937664998393966765847)
                ·
                  refine ⟨18755906497497590950148771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12503937664998393966765847 18755906497497590950148771)
                  ·
                    refine ⟨28133859746246386425223157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18755906497497590950148771 28133859746246386425223157)
                    ·
                      refine ⟨2637549351210598727364671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28133859746246386425223157 2637549351210598727364671)
                      ·
                        rfl

theorem cell23_5136609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_5136609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136609 prefixEnd_5136609 := by exact prefixLift 5136609
  have htrace : WordTrace (prefixWord ++ tailWord_5136609) baseStart_5136609 baseEnd_5136609 := by
    simpa [prefixWord, tailWord_5136609, baseEnd_5136609] using wordTrace_append hprefix tailTrace_5136609
  have hstable : (prefixWord ++ tailWord_5136609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136609).length < 2 ^ (prefixWord ++ tailWord_5136609).sum := by decide
  have hdescent : baseEnd_5136609 < baseStart_5136609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136619 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 4]
def baseStart_5136619 : Nat := 118140960795 + 5136619 * 2 ^ 59
def prefixEnd_5136619 : Nat := 4983230072969 + 3 ^ 40 * 5136619 * 2
def baseEnd_5136619 : Nat := 2637554486017143688239625

theorem tailTrace_5136619 : CollatzResearch.WordTrace tailWord_5136619 prefixEnd_5136619 2637554486017143688239625 := by
  unfold tailWord_5136619
  simp only [CollatzResearch.WordTrace]
  refine ⟨187347886177914102527700911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124898590785276068351800607 187347886177914102527700911)
  ·
    refine ⟨281021829266871153791551367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187347886177914102527700911 281021829266871153791551367)
    ·
      refine ⟨421532743900306730687327051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281021829266871153791551367 421532743900306730687327051)
      ·
        refine ⟨632299115850460096030990577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421532743900306730687327051 632299115850460096030990577)
        ·
          refine ⟨474224336887845072023242933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632299115850460096030990577 474224336887845072023242933)
          ·
            refine ⟨44458531583235475502179025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 474224336887845072023242933 44458531583235475502179025)
            ·
              refine ⟨33343898687426606626634269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44458531583235475502179025 33343898687426606626634269)
              ·
                refine ⟨12503962007784977484987851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33343898687426606626634269 12503962007784977484987851)
                ·
                  refine ⟨18755943011677466227481777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12503962007784977484987851 18755943011677466227481777)
                  ·
                    refine ⟨14066957258758099670611333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18755943011677466227481777 14066957258758099670611333)
                    ·
                      refine ⟨2637554486017143688239625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14066957258758099670611333 2637554486017143688239625)
                      ·
                        rfl

theorem cell23_5136619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 4].length) (baseStart_5136619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136619 prefixEnd_5136619 := by exact prefixLift 5136619
  have htrace : WordTrace (prefixWord ++ tailWord_5136619) baseStart_5136619 baseEnd_5136619 := by
    simpa [prefixWord, tailWord_5136619, baseEnd_5136619] using wordTrace_append hprefix tailTrace_5136619
  have hstable : (prefixWord ++ tailWord_5136619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136619).length < 2 ^ (prefixWord ++ tailWord_5136619).sum := by decide
  have hdescent : baseEnd_5136619 < baseStart_5136619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136623 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 4]
def baseStart_5136623 : Nat := 118140960795 + 5136623 * 2 ^ 59
def prefixEnd_5136623 : Nat := 4983230072969 + 3 ^ 40 * 5136623 * 2
def baseEnd_5136623 : Nat := 2637556539939761672589607

theorem tailTrace_5136623 : CollatzResearch.WordTrace tailWord_5136623 prefixEnd_5136623 2637556539939761672589607 := by
  unfold tailWord_5136623
  simp only [CollatzResearch.WordTrace]
  refine ⟨187348032069899611210846523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124898688046599740807231015 187348032069899611210846523)
  ·
    refine ⟨281022048104849416816269785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187348032069899611210846523 281022048104849416816269785)
    ·
      refine ⟨210766536078637062612202339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281022048104849416816269785 210766536078637062612202339)
      ·
        refine ⟨316149804117955593918303509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210766536078637062612202339 316149804117955593918303509)
        ·
          refine ⟨14819522068029168464920477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 316149804117955593918303509 14819522068029168464920477)
          ·
            refine ⟨5557320775510938174345179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14819522068029168464920477 5557320775510938174345179)
            ·
              refine ⟨8335981163266407261517769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557320775510938174345179 8335981163266407261517769)
              ·
                refine ⟨6251985872449805446138327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8335981163266407261517769 6251985872449805446138327)
                ·
                  refine ⟨9377978808674708169207491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6251985872449805446138327 9377978808674708169207491)
                  ·
                    refine ⟨14066968213012062253811237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9377978808674708169207491 14066968213012062253811237)
                    ·
                      refine ⟨2637556539939761672589607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14066968213012062253811237 2637556539939761672589607)
                      ·
                        rfl

theorem cell23_5136623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 4].length) (baseStart_5136623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136623 prefixEnd_5136623 := by exact prefixLift 5136623
  have htrace : WordTrace (prefixWord ++ tailWord_5136623) baseStart_5136623 baseEnd_5136623 := by
    simpa [prefixWord, tailWord_5136623, baseEnd_5136623] using wordTrace_append hprefix tailTrace_5136623
  have hstable : (prefixWord ++ tailWord_5136623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136623).length < 2 ^ (prefixWord ++ tailWord_5136623).sum := by decide
  have hdescent : baseEnd_5136623 < baseStart_5136623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136636 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_5136636 : Nat := 118140960795 + 5136636 * 2 ^ 59
def prefixEnd_5136636 : Nat := 4983230072969 + 3 ^ 40 * 5136636 * 2
def baseEnd_5136636 : Nat := 2637563215188270121727047

theorem tailTrace_5136636 : CollatzResearch.WordTrace tailWord_5136636 prefixEnd_5136636 2637563215188270121727047 := by
  unfold tailWord_5136636
  simp only [CollatzResearch.WordTrace]
  refine ⟨93674253109426257215534881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124899004145901676287379841 93674253109426257215534881)
  ·
    refine ⟨70255689832069692911651161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93674253109426257215534881 70255689832069692911651161)
    ·
      refine ⟨52691767374052269683738371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70255689832069692911651161 52691767374052269683738371)
      ·
        refine ⟨79037651061078404525607557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52691767374052269683738371 79037651061078404525607557)
        ·
          refine ⟨14819559573952200848551417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79037651061078404525607557 14819559573952200848551417)
          ·
            refine ⟨11114669680464150636413563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14819559573952200848551417 11114669680464150636413563)
            ·
              refine ⟨16672004520696225954620345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11114669680464150636413563 16672004520696225954620345)
              ·
                refine ⟨12504003390522169465965259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16672004520696225954620345 12504003390522169465965259)
                ·
                  refine ⟨18756005085783254198947889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12504003390522169465965259 18756005085783254198947889)
                  ·
                    refine ⟨14067003814337440649210917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18756005085783254198947889 14067003814337440649210917)
                    ·
                      refine ⟨2637563215188270121727047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14067003814337440649210917 2637563215188270121727047)
                      ·
                        rfl

theorem cell23_5136636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_5136636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136636 prefixEnd_5136636 := by exact prefixLift 5136636
  have htrace : WordTrace (prefixWord ++ tailWord_5136636) baseStart_5136636 baseEnd_5136636 := by
    simpa [prefixWord, tailWord_5136636, baseEnd_5136636] using wordTrace_append hprefix tailTrace_5136636
  have hstable : (prefixWord ++ tailWord_5136636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136636).length < 2 ^ (prefixWord ++ tailWord_5136636).sum := by decide
  have hdescent : baseEnd_5136636 < baseStart_5136636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136643 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 1, 2, 3]
def baseStart_5136643 : Nat := 118140960795 + 5136643 * 2 ^ 59
def prefixEnd_5136643 : Nat := 4983230072969 + 3 ^ 40 * 5136643 * 2
def baseEnd_5136643 : Nat := 2637566809552851594339515

theorem tailTrace_5136643 : CollatzResearch.WordTrace tailWord_5136643 prefixEnd_5136643 2637566809552851594339515 := by
  unfold tailWord_5136643
  simp only [CollatzResearch.WordTrace]
  refine ⟨187348761529827154626574583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124899174353218103084383055 187348761529827154626574583)
  ·
    refine ⟨281023142294740731939861875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187348761529827154626574583 281023142294740731939861875)
    ·
      refine ⟨421534713442111097909792813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281023142294740731939861875 421534713442111097909792813)
      ·
        refine ⟨158075517540791661716172305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421534713442111097909792813 158075517540791661716172305)
        ·
          refine ⟨118556638155593746287129229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158075517540791661716172305 118556638155593746287129229)
          ·
            refine ⟨44458739308347654857673461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118556638155593746287129229 44458739308347654857673461)
            ·
              refine ⟨4168006810157592642906887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44458739308347654857673461 4168006810157592642906887)
              ·
                refine ⟨6252010215236388964360331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168006810157592642906887 6252010215236388964360331)
                ·
                  refine ⟨9378015322854583446540497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6252010215236388964360331 9378015322854583446540497)
                  ·
                    refine ⟨7033511492140937584905373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9378015322854583446540497 7033511492140937584905373)
                    ·
                      refine ⟨2637566809552851594339515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7033511492140937584905373 2637566809552851594339515)
                      ·
                        rfl

theorem cell23_5136643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_5136643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136643 prefixEnd_5136643 := by exact prefixLift 5136643
  have htrace : WordTrace (prefixWord ++ tailWord_5136643) baseStart_5136643 baseEnd_5136643 := by
    simpa [prefixWord, tailWord_5136643, baseEnd_5136643] using wordTrace_append hprefix tailTrace_5136643
  have hstable : (prefixWord ++ tailWord_5136643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136643).length < 2 ^ (prefixWord ++ tailWord_5136643).sum := by decide
  have hdescent : baseEnd_5136643 < baseStart_5136643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136657 : List Nat := [1, 2, 2, 1, 1, 5, 4, 2, 1, 2, 2]
def baseStart_5136657 : Nat := 118140960795 + 5136657 * 2 ^ 59
def prefixEnd_5136657 : Nat := 4983230072969 + 3 ^ 40 * 5136657 * 2
def baseEnd_5136657 : Nat := 2637573998282014539564451

theorem tailTrace_5136657 : CollatzResearch.WordTrace tailWord_5136657 prefixEnd_5136657 2637573998282014539564451 := by
  unfold tailWord_5136657
  simp only [CollatzResearch.WordTrace]
  refine ⟨187349272151776435017584225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124899514767850956678389483 187349272151776435017584225)
  ·
    refine ⟨140511954113832326263188169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187349272151776435017584225 140511954113832326263188169)
    ·
      refine ⟨105383965585374244697391127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140511954113832326263188169 105383965585374244697391127)
      ·
        refine ⟨158075948378061367046086691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105383965585374244697391127 158075948378061367046086691)
        ·
          refine ⟨237113922567092050569130037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158075948378061367046086691 237113922567092050569130037)
          ·
            refine ⟨22229430240664879740855941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237113922567092050569130037 22229430240664879740855941)
            ·
              refine ⟨4168018170124664951410489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22229430240664879740855941 4168018170124664951410489)
              ·
                refine ⟨3126013627593498713557867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168018170124664951410489 3126013627593498713557867)
                ·
                  refine ⟨4689020441390248070336801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3126013627593498713557867 4689020441390248070336801)
                  ·
                    refine ⟨3516765331042686052752601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4689020441390248070336801 3516765331042686052752601)
                    ·
                      refine ⟨2637573998282014539564451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3516765331042686052752601 2637573998282014539564451)
                      ·
                        rfl

theorem cell23_5136657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 2, 2].length) (baseStart_5136657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136657 prefixEnd_5136657 := by exact prefixLift 5136657
  have htrace : WordTrace (prefixWord ++ tailWord_5136657) baseStart_5136657 baseEnd_5136657 := by
    simpa [prefixWord, tailWord_5136657, baseEnd_5136657] using wordTrace_append hprefix tailTrace_5136657
  have hstable : (prefixWord ++ tailWord_5136657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136657).length < 2 ^ (prefixWord ++ tailWord_5136657).sum := by decide
  have hdescent : baseEnd_5136657 < baseStart_5136657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136670 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5136670 : Nat := 118140960795 + 5136670 * 2 ^ 59
def prefixEnd_5136670 : Nat := 4983230072969 + 3 ^ 40 * 5136670 * 2
def baseEnd_5136670 : Nat := 2637580673530522988701891

theorem tailTrace_5136670 : CollatzResearch.WordTrace tailWord_5136670 prefixEnd_5136670 2637580673530522988701891 := by
  unfold tailWord_5136670
  simp only [CollatzResearch.WordTrace]
  refine ⟨23418718287591167279725933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124899830867152892158538309 23418718287591167279725933)
  ·
    refine ⟨8782019357846687729897225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23418718287591167279725933 8782019357846687729897225)
    ·
      refine ⟨6586514518385015797422919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8782019357846687729897225 6586514518385015797422919)
      ·
        refine ⟨9879771777577523696134379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6586514518385015797422919 9879771777577523696134379)
        ·
          refine ⟨14819657666366285544201569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9879771777577523696134379 14819657666366285544201569)
          ·
            refine ⟨11114743249774714158151177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14819657666366285544201569 11114743249774714158151177)
            ·
              refine ⟨8336057437331035618613383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11114743249774714158151177 8336057437331035618613383)
              ·
                refine ⟨12504086155996553427920075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336057437331035618613383 12504086155996553427920075)
                ·
                  refine ⟨18756129233994830141880113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12504086155996553427920075 18756129233994830141880113)
                  ·
                    refine ⟨14067096925496122606410085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18756129233994830141880113 14067096925496122606410085)
                    ·
                      refine ⟨2637580673530522988701891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14067096925496122606410085 2637580673530522988701891)
                      ·
                        rfl

theorem cell23_5136670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5136670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136670 prefixEnd_5136670 := by exact prefixLift 5136670
  have htrace : WordTrace (prefixWord ++ tailWord_5136670) baseStart_5136670 baseEnd_5136670 := by
    simpa [prefixWord, tailWord_5136670, baseEnd_5136670] using wordTrace_append hprefix tailTrace_5136670
  have hstable : (prefixWord ++ tailWord_5136670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136670).length < 2 ^ (prefixWord ++ tailWord_5136670).sum := by decide
  have hdescent : baseEnd_5136670 < baseStart_5136670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136673 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_5136673 : Nat := 118140960795 + 5136673 * 2 ^ 59
def prefixEnd_5136673 : Nat := 4983230072969 + 3 ^ 40 * 5136673 * 2
def baseEnd_5136673 : Nat := 2637582213972486476964377

theorem tailTrace_5136673 : CollatzResearch.WordTrace tailWord_5136673 prefixEnd_5136673 2637582213972486476964377 := by
  unfold tailWord_5136673
  simp only [CollatzResearch.WordTrace]
  refine ⟨187349855719718469750166673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124899903813145646500111115 187349855719718469750166673)
  ·
    refine ⟨140512391789788852312625005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187349855719718469750166673 140512391789788852312625005)
    ·
      refine ⟨52692146921170819617234377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140512391789788852312625005 52692146921170819617234377)
      ·
        refine ⟨39519110190878114712925783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52692146921170819617234377 39519110190878114712925783)
        ·
          refine ⟨59278665286317172069388675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39519110190878114712925783 59278665286317172069388675)
          ·
            refine ⟨88917997929475758104083013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59278665286317172069388675 88917997929475758104083013)
            ·
              refine ⟨16672124611776704644515565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88917997929475758104083013 16672124611776704644515565)
              ·
                refine ⟨6252046729416264241693337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16672124611776704644515565 6252046729416264241693337)
                ·
                  refine ⟨4689035047062198181270003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6252046729416264241693337 4689035047062198181270003)
                  ·
                    refine ⟨7033552570593297271905005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4689035047062198181270003 7033552570593297271905005)
                    ·
                      refine ⟨2637582213972486476964377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7033552570593297271905005 2637582213972486476964377)
                      ·
                        rfl

theorem cell23_5136673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_5136673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136673 prefixEnd_5136673 := by exact prefixLift 5136673
  have htrace : WordTrace (prefixWord ++ tailWord_5136673) baseStart_5136673 baseEnd_5136673 := by
    simpa [prefixWord, tailWord_5136673, baseEnd_5136673] using wordTrace_append hprefix tailTrace_5136673
  have hstable : (prefixWord ++ tailWord_5136673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136673).length < 2 ^ (prefixWord ++ tailWord_5136673).sum := by decide
  have hdescent : baseEnd_5136673 < baseStart_5136673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136776 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_5136776 : Nat := 118140960795 + 5136776 * 2 ^ 59
def prefixEnd_5136776 : Nat := 4983230072969 + 3 ^ 40 * 5136776 * 2
def baseEnd_5136776 : Nat := 2637635102479899573976403

theorem tailTrace_5136776 : CollatzResearch.WordTrace tailWord_5136776 prefixEnd_5136776 2637635102479899573976403 := by
  unfold tailWord_5136776
  simp only [CollatzResearch.WordTrace]
  refine ⟨93676806219172659170583091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124902408292230212227444121 93676806219172659170583091)
  ·
    refine ⟨140515209328758988755874637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93676806219172659170583091 140515209328758988755874637)
    ·
      refine ⟨52693203498284620783452989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140515209328758988755874637 52693203498284620783452989)
      ·
        refine ⟨19759951311856732793794871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52693203498284620783452989 19759951311856732793794871)
        ·
          refine ⟨29639926967785099190692307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19759951311856732793794871 29639926967785099190692307)
          ·
            refine ⟨44459890451677648786038461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29639926967785099190692307 44459890451677648786038461)
            ·
              refine ⟨16672458919379118294764423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44459890451677648786038461 16672458919379118294764423)
              ·
                refine ⟨25008688379068677442146635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16672458919379118294764423 25008688379068677442146635)
                ·
                  refine ⟨37513032568603016163219953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25008688379068677442146635 37513032568603016163219953)
                  ·
                    refine ⟨28134774426452262122414965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37513032568603016163219953 28134774426452262122414965)
                    ·
                      refine ⟨2637635102479899573976403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28134774426452262122414965 2637635102479899573976403)
                      ·
                        rfl

theorem cell23_5136776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_5136776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136776 prefixEnd_5136776 := by exact prefixLift 5136776
  have htrace : WordTrace (prefixWord ++ tailWord_5136776) baseStart_5136776 baseEnd_5136776 := by
    simpa [prefixWord, tailWord_5136776, baseEnd_5136776] using wordTrace_append hprefix tailTrace_5136776
  have hstable : (prefixWord ++ tailWord_5136776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136776).length < 2 ^ (prefixWord ++ tailWord_5136776).sum := by decide
  have hdescent : baseEnd_5136776 < baseStart_5136776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136803 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 4]
def baseStart_5136803 : Nat := 118140960795 + 5136803 * 2 ^ 59
def prefixEnd_5136803 : Nat := 4983230072969 + 3 ^ 40 * 5136803 * 2
def baseEnd_5136803 : Nat := 2637648966457570968338779

theorem tailTrace_5136803 : CollatzResearch.WordTrace tailWord_5136803 prefixEnd_5136803 2637648966457570968338779 := by
  unfold tailWord_5136803
  simp only [CollatzResearch.WordTrace]
  refine ⟨187354597209247501952399063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124903064806165001301599375 187354597209247501952399063)
  ·
    refine ⟨281031895813871252928598595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187354597209247501952399063 281031895813871252928598595)
    ·
      refine ⟨421547843720806879392897893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281031895813871252928598595 421547843720806879392897893)
      ·
        refine ⟨79040220697651289886168355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 421547843720806879392897893 79040220697651289886168355)
        ·
          refine ⟨118560331046476934829252533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79040220697651289886168355 118560331046476934829252533)
          ·
            refine ⟨11115031035607212640242425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118560331046476934829252533 11115031035607212640242425)
            ·
              refine ⟨8336273276705409480181819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11115031035607212640242425 8336273276705409480181819)
              ·
                refine ⟨12504409915058114220272729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336273276705409480181819 12504409915058114220272729)
                ·
                  refine ⟨9378307436293585665204547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12504409915058114220272729 9378307436293585665204547)
                  ·
                    refine ⟨14067461154440378497806821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9378307436293585665204547 14067461154440378497806821)
                    ·
                      refine ⟨2637648966457570968338779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14067461154440378497806821 2637648966457570968338779)
                      ·
                        rfl

theorem cell23_5136803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_5136803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136803 prefixEnd_5136803 := by exact prefixLift 5136803
  have htrace : WordTrace (prefixWord ++ tailWord_5136803) baseStart_5136803 baseEnd_5136803 := by
    simpa [prefixWord, tailWord_5136803, baseEnd_5136803] using wordTrace_append hprefix tailTrace_5136803
  have hstable : (prefixWord ++ tailWord_5136803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136803).length < 2 ^ (prefixWord ++ tailWord_5136803).sum := by decide
  have hdescent : baseEnd_5136803 < baseStart_5136803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136809 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 10]
def baseStart_5136809 : Nat := 118140960795 + 5136809 * 2 ^ 59
def prefixEnd_5136809 : Nat := 4983230072969 + 3 ^ 40 * 5136809 * 2
def baseEnd_5136809 : Nat := 293072449704610882762639

theorem tailTrace_5136809 : CollatzResearch.WordTrace tailWord_5136809 prefixEnd_5136809 293072449704610882762639 := by
  unfold tailWord_5136809
  simp only [CollatzResearch.WordTrace]
  refine ⟨187354816047225764977117481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124903210698150509984744987 187354816047225764977117481)
  ·
    refine ⟨140516112035419323732838111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187354816047225764977117481 140516112035419323732838111)
    ·
      refine ⟨210774168053128985599257167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140516112035419323732838111 210774168053128985599257167)
      ·
        refine ⟨316161252079693478398885751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210774168053128985599257167 316161252079693478398885751)
        ·
          refine ⟨474241878119540217598328627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316161252079693478398885751 474241878119540217598328627)
          ·
            refine ⟨711362817179310326397492941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474241878119540217598328627 711362817179310326397492941)
            ·
              refine ⟨266761056442241372399059853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711362817179310326397492941 266761056442241372399059853)
              ·
                refine ⟨100035396165840514649647445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266761056442241372399059853 100035396165840514649647445)
                ·
                  refine ⟨293072449704610882762639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 100035396165840514649647445 293072449704610882762639)
                  ·
                    rfl

theorem cell23_5136809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 10].length) (baseStart_5136809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136809 prefixEnd_5136809 := by exact prefixLift 5136809
  have htrace : WordTrace (prefixWord ++ tailWord_5136809) baseStart_5136809 baseEnd_5136809 := by
    simpa [prefixWord, tailWord_5136809, baseEnd_5136809] using wordTrace_append hprefix tailTrace_5136809
  have hstable : (prefixWord ++ tailWord_5136809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136809).length < 2 ^ (prefixWord ++ tailWord_5136809).sum := by decide
  have hdescent : baseEnd_5136809 < baseStart_5136809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136823 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_5136823 : Nat := 118140960795 + 5136823 * 2 ^ 59
def prefixEnd_5136823 : Nat := 4983230072969 + 3 ^ 40 * 5136823 * 2
def baseEnd_5136823 : Nat := 2637659236070660890088687

theorem tailTrace_5136823 : CollatzResearch.WordTrace tailWord_5136823 prefixEnd_5136823 2637659236070660890088687 := by
  unfold tailWord_5136823
  simp only [CollatzResearch.WordTrace]
  refine ⟨187355326669175045368127123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124903551112783363578751415 187355326669175045368127123)
  ·
    refine ⟨281032990003762568052190685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187355326669175045368127123 281032990003762568052190685)
    ·
      refine ⟨105387371251410963019571507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281032990003762568052190685 105387371251410963019571507)
      ·
        refine ⟨158081056877116444529357261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105387371251410963019571507 158081056877116444529357261)
        ·
          refine ⟨59280396328918666698508973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158081056877116444529357261 59280396328918666698508973)
          ·
            refine ⟨22230148623344500011940865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59280396328918666698508973 22230148623344500011940865)
            ·
              refine ⟨16672611467508375008955649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22230148623344500011940865 16672611467508375008955649)
              ·
                refine ⟨12504458600631281256716737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16672611467508375008955649 12504458600631281256716737)
                ·
                  refine ⟨9378343950473460942537553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12504458600631281256716737 9378343950473460942537553)
                  ·
                    refine ⟨7033757962855095706903165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9378343950473460942537553 7033757962855095706903165)
                    ·
                      refine ⟨2637659236070660890088687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7033757962855095706903165 2637659236070660890088687)
                      ·
                        rfl

theorem cell23_5136823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_5136823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136823 prefixEnd_5136823 := by exact prefixLift 5136823
  have htrace : WordTrace (prefixWord ++ tailWord_5136823) baseStart_5136823 baseEnd_5136823 := by
    simpa [prefixWord, tailWord_5136823, baseEnd_5136823] using wordTrace_append hprefix tailTrace_5136823
  have hstable : (prefixWord ++ tailWord_5136823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136823).length < 2 ^ (prefixWord ++ tailWord_5136823).sum := by decide
  have hdescent : baseEnd_5136823 < baseStart_5136823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136910 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_5136910 : Nat := 118140960795 + 5136910 * 2 ^ 59
def prefixEnd_5136910 : Nat := 4983230072969 + 3 ^ 40 * 5136910 * 2
def baseEnd_5136910 : Nat := 2637703908887602049700787

theorem tailTrace_5136910 : CollatzResearch.WordTrace tailWord_5136910 prefixEnd_5136910 2637703908887602049700787 := by
  unfold tailWord_5136910
  simp only [CollatzResearch.WordTrace]
  refine ⟨23419812477482482403318023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124905666546573239484362789 23419812477482482403318023)
  ·
    refine ⟨35129718716223723604977035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23419812477482482403318023 35129718716223723604977035)
    ·
      refine ⟨52694578074335585407465553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35129718716223723604977035 52694578074335585407465553)
      ·
        refine ⟨39520933555751689055599165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52694578074335585407465553 39520933555751689055599165)
        ·
          refine ⟨14820350083406883395849687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39520933555751689055599165 14820350083406883395849687)
          ·
            refine ⟨22230525125110325093774531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14820350083406883395849687 22230525125110325093774531)
            ·
              refine ⟨33345787687665487640661797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22230525125110325093774531 33345787687665487640661797)
              ·
                refine ⟨6252335191437278932624087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33345787687665487640661797 6252335191437278932624087)
                ·
                  refine ⟨9378502787155918398936131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6252335191437278932624087 9378502787155918398936131)
                  ·
                    refine ⟨14067754180733877598404197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9378502787155918398936131 14067754180733877598404197)
                    ·
                      refine ⟨2637703908887602049700787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14067754180733877598404197 2637703908887602049700787)
                      ·
                        rfl

theorem cell23_5136910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_5136910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136910 prefixEnd_5136910 := by exact prefixLift 5136910
  have htrace : WordTrace (prefixWord ++ tailWord_5136910) baseStart_5136910 baseEnd_5136910 := by
    simpa [prefixWord, tailWord_5136910, baseEnd_5136910] using wordTrace_append hprefix tailTrace_5136910
  have hstable : (prefixWord ++ tailWord_5136910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136910).length < 2 ^ (prefixWord ++ tailWord_5136910).sum := by decide
  have hdescent : baseEnd_5136910 < baseStart_5136910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136950 : List Nat := [5, 1, 2, 1, 2, 2, 2, 8]
def baseStart_5136950 : Nat := 118140960795 + 5136950 * 2 ^ 59
def prefixEnd_5136950 : Nat := 4983230072969 + 3 ^ 40 * 5136950 * 2
def baseEnd_5136950 : Nat := 97693498078288218266689

theorem tailTrace_5136950 : CollatzResearch.WordTrace tailWord_5136950 prefixEnd_5136950 97693498078288218266689 := by
  unfold tailWord_5136950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11709997421232184128625019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124906639159809964038666869 11709997421232184128625019)
  ·
    refine ⟨17564996131848276192937529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11709997421232184128625019 17564996131848276192937529)
    ·
      refine ⟨13173747098886207144703147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17564996131848276192937529 13173747098886207144703147)
      ·
        refine ⟨19760620648329310717054721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13173747098886207144703147 19760620648329310717054721)
        ·
          refine ⟨14820465486246983037791041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19760620648329310717054721 14820465486246983037791041)
          ·
            refine ⟨11115349114685237278343281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14820465486246983037791041 11115349114685237278343281)
            ·
              refine ⟨8336511836013927958757461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11115349114685237278343281 8336511836013927958757461)
              ·
                refine ⟨97693498078288218266689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8336511836013927958757461 97693498078288218266689)
                ·
                  rfl

theorem cell23_5136950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_5136950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136950 prefixEnd_5136950 := by exact prefixLift 5136950
  have htrace : WordTrace (prefixWord ++ tailWord_5136950) baseStart_5136950 baseEnd_5136950 := by
    simpa [prefixWord, tailWord_5136950, baseEnd_5136950] using wordTrace_append hprefix tailTrace_5136950
  have hstable : (prefixWord ++ tailWord_5136950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136950).length < 2 ^ (prefixWord ++ tailWord_5136950).sum := by decide
  have hdescent : baseEnd_5136950 < baseStart_5136950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5136976 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 3, 8]
def baseStart_5136976 : Nat := 118140960795 + 5136976 * 2 ^ 59
def prefixEnd_5136976 : Nat := 4983230072969 + 3 ^ 40 * 5136976 * 2
def baseEnd_5136976 : Nat := 879245932870266263825161

theorem tailTrace_5136976 : CollatzResearch.WordTrace tailWord_5136976 prefixEnd_5136976 879245932870266263825161 := by
  unfold tailWord_5136976
  simp only [CollatzResearch.WordTrace]
  refine ⟨93680453518810376249223391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124907271358413834998964521 93680453518810376249223391)
  ·
    refine ⟨140520680278215564373835087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93680453518810376249223391 140520680278215564373835087)
    ·
      refine ⟨210781020417323346560752631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140520680278215564373835087 210781020417323346560752631)
      ·
        refine ⟨316171530625985019841128947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210781020417323346560752631 316171530625985019841128947)
        ·
          refine ⟨474257295938977529761693421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316171530625985019841128947 474257295938977529761693421)
          ·
            refine ⟨177846485977116573660635033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474257295938977529761693421 177846485977116573660635033)
            ·
              refine ⟨133384864482837430245476275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177846485977116573660635033 133384864482837430245476275)
              ·
                refine ⟨200077296724256145368214413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133384864482837430245476275 200077296724256145368214413)
                ·
                  refine ⟨75028986271596054513080405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200077296724256145368214413 75028986271596054513080405)
                  ·
                    refine ⟨879245932870266263825161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75028986271596054513080405 879245932870266263825161)
                    ·
                      rfl

theorem cell23_5136976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_5136976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5136976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5136976 prefixEnd_5136976 := by exact prefixLift 5136976
  have htrace : WordTrace (prefixWord ++ tailWord_5136976) baseStart_5136976 baseEnd_5136976 := by
    simpa [prefixWord, tailWord_5136976, baseEnd_5136976] using wordTrace_append hprefix tailTrace_5136976
  have hstable : (prefixWord ++ tailWord_5136976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5136976).length < 2 ^ (prefixWord ++ tailWord_5136976).sum := by decide
  have hdescent : baseEnd_5136976 < baseStart_5136976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5136976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137010 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_5137010 : Nat := 118140960795 + 5137010 * 2 ^ 59
def prefixEnd_5137010 : Nat := 4983230072969 + 3 ^ 40 * 5137010 * 2
def baseEnd_5137010 : Nat := 879251752317683886150109

theorem tailTrace_5137010 : CollatzResearch.WordTrace tailWord_5137010 prefixEnd_5137010 879251752317683886150109 := by
  unfold tailWord_5137010
  simp only [CollatzResearch.WordTrace]
  refine ⟨46840536779874394076296121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124908098079665050870122989 46840536779874394076296121)
  ·
    refine ⟨35130402584905795557222091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46840536779874394076296121 35130402584905795557222091)
    ·
      refine ⟨52695603877358693335833137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35130402584905795557222091 52695603877358693335833137)
      ·
        refine ⟨39521702908019020001874853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52695603877358693335833137 39521702908019020001874853)
        ·
          refine ⟨7410319295253566250351535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39521702908019020001874853 7410319295253566250351535)
          ·
            refine ⟨11115478942880349375527303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7410319295253566250351535 11115478942880349375527303)
            ·
              refine ⟨16673218414320524063290955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11115478942880349375527303 16673218414320524063290955)
              ·
                refine ⟨25009827621480786094936433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16673218414320524063290955 25009827621480786094936433)
                ·
                  refine ⟨18757370716110589571202325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25009827621480786094936433 18757370716110589571202325)
                  ·
                    refine ⟨879251752317683886150109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18757370716110589571202325 879251752317683886150109)
                    ·
                      rfl

theorem cell23_5137010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_5137010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137010 prefixEnd_5137010 := by exact prefixLift 5137010
  have htrace : WordTrace (prefixWord ++ tailWord_5137010) baseStart_5137010 baseEnd_5137010 := by
    simpa [prefixWord, tailWord_5137010, baseEnd_5137010] using wordTrace_append hprefix tailTrace_5137010
  have hstable : (prefixWord ++ tailWord_5137010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137010).length < 2 ^ (prefixWord ++ tailWord_5137010).sum := by decide
  have hdescent : baseEnd_5137010 < baseStart_5137010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137017 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 1, 4, 2]
def baseStart_5137017 : Nat := 118140960795 + 5137017 * 2 ^ 59
def prefixEnd_5137017 : Nat := 4983230072969 + 3 ^ 40 * 5137017 * 2
def baseEnd_5137017 : Nat := 2637758851317633131062795

theorem tailTrace_5137017 : CollatzResearch.WordTrace tailWord_5137017 prefixEnd_5137017 2637758851317633131062795 := by
  unfold tailWord_5137017
  simp only [CollatzResearch.WordTrace]
  refine ⟨187362402430472216500689305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124908268286981477667126203 187362402430472216500689305)
  ·
    refine ⟨140521801822854162375516979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187362402430472216500689305 140521801822854162375516979)
    ·
      refine ⟨210782702734281243563275469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140521801822854162375516979 210782702734281243563275469)
      ·
        refine ⟨79043513525355466336228301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210782702734281243563275469 79043513525355466336228301)
        ·
          refine ⟨29641317572008299876085613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79043513525355466336228301 29641317572008299876085613)
          ·
            refine ⟨11115494089503112453532105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29641317572008299876085613 11115494089503112453532105)
            ·
              refine ⟨8336620567127334340149079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11115494089503112453532105 8336620567127334340149079)
              ·
                refine ⟨12504930850691001510223619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336620567127334340149079 12504930850691001510223619)
                ·
                  refine ⟨18757396276036502265335429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12504930850691001510223619 18757396276036502265335429)
                  ·
                    refine ⟨3517011801756844174750393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18757396276036502265335429 3517011801756844174750393)
                    ·
                      refine ⟨2637758851317633131062795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517011801756844174750393 2637758851317633131062795)
                      ·
                        rfl

theorem cell23_5137017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_5137017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137017 prefixEnd_5137017 := by exact prefixLift 5137017
  have htrace : WordTrace (prefixWord ++ tailWord_5137017) baseStart_5137017 baseEnd_5137017 := by
    simpa [prefixWord, tailWord_5137017, baseEnd_5137017] using wordTrace_append hprefix tailTrace_5137017
  have hstable : (prefixWord ++ tailWord_5137017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137017).length < 2 ^ (prefixWord ++ tailWord_5137017).sum := by decide
  have hdescent : baseEnd_5137017 < baseStart_5137017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
