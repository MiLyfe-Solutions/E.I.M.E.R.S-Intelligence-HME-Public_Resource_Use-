import V185TrunkScan22Chunk115

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1039226 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_1039226 : Nat := 118140960795 + 1039226 * 2 ^ 59
def prefixEnd_1039226 : Nat := 4983230072969 + 3 ^ 40 * 1039226 * 2
def baseEnd_1039226 : Nat := 355748297766304171463795

theorem tailTrace_1039226 : CollatzResearch.WordTrace tailWord_1039226 prefixEnd_1039226 355748297766304171463795 := by
  unfold tailWord_1039226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475921533267290628888383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25269124088712775010369021 9475921533267290628888383)
  ·
    refine ⟨14213882299900935943332575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9475921533267290628888383 14213882299900935943332575)
    ·
      refine ⟨21320823449851403914998863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14213882299900935943332575 21320823449851403914998863)
      ·
        refine ⟨31981235174777105872498295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21320823449851403914998863 31981235174777105872498295)
        ·
          refine ⟨47971852762165658808747443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31981235174777105872498295 47971852762165658808747443)
          ·
            refine ⟨71957779143248488213121165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47971852762165658808747443 71957779143248488213121165)
            ·
              refine ⟨26984167178718183079920437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71957779143248488213121165 26984167178718183079920437)
              ·
                refine ⟨2529765673004829663742541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26984167178718183079920437 2529765673004829663742541)
                ·
                  refine ⟨948662127376811123903453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2529765673004829663742541 948662127376811123903453)
                  ·
                    refine ⟨355748297766304171463795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 948662127376811123903453 355748297766304171463795)
                    ·
                      rfl

theorem cell22_1039226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_1039226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039226 prefixEnd_1039226 := by exact prefixLift 1039226
  have htrace : WordTrace (prefixWord ++ tailWord_1039226) baseStart_1039226 baseEnd_1039226 := by
    simpa [prefixWord, tailWord_1039226, baseEnd_1039226] using wordTrace_append hprefix tailTrace_1039226
  have hstable : (prefixWord ++ tailWord_1039226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039226).length < 2 ^ (prefixWord ++ tailWord_1039226).sum := by decide
  have hdescent : baseEnd_1039226 < baseStart_1039226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039277 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1039277 : Nat := 118140960795 + 1039277 * 2 ^ 59
def prefixEnd_1039277 : Nat := 4983230072969 + 3 ^ 40 * 1039277 * 2
def baseEnd_1039277 : Nat := 355765756108557038438639

theorem tailTrace_1039277 : CollatzResearch.WordTrace tailWord_1039277 prefixEnd_1039277 355765756108557038438639 := by
  unfold tailWord_1039277
  simp only [CollatzResearch.WordTrace]
  refine ⟨37905546255884398225660085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25270364170589598817106723 37905546255884398225660085)
  ·
    refine ⟨3553644961489162333655633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37905546255884398225660085 3553644961489162333655633)
    ·
      refine ⟨2665233721116871750241725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3553644961489162333655633 2665233721116871750241725)
      ·
        refine ⟨999462645418826906340647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2665233721116871750241725 999462645418826906340647)
        ·
          refine ⟨1499193968128240359510971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999462645418826906340647 1499193968128240359510971)
          ·
            refine ⟨2248790952192360539266457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499193968128240359510971 2248790952192360539266457)
            ·
              refine ⟨1686593214144270404449843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248790952192360539266457 1686593214144270404449843)
              ·
                refine ⟨2529889821216405606674765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1686593214144270404449843 2529889821216405606674765)
                ·
                  refine ⟨948708682956152102503037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2529889821216405606674765 948708682956152102503037)
                  ·
                    refine ⟨355765756108557038438639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 948708682956152102503037 355765756108557038438639)
                    ·
                      rfl

theorem cell22_1039277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1039277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039277 prefixEnd_1039277 := by exact prefixLift 1039277
  have htrace : WordTrace (prefixWord ++ tailWord_1039277) baseStart_1039277 baseEnd_1039277 := by
    simpa [prefixWord, tailWord_1039277, baseEnd_1039277] using wordTrace_append hprefix tailTrace_1039277
  have hstable : (prefixWord ++ tailWord_1039277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039277).length < 2 ^ (prefixWord ++ tailWord_1039277).sum := by decide
  have hdescent : baseEnd_1039277 < baseStart_1039277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039412 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1039412 : Nat := 118140960795 + 1039412 * 2 ^ 59
def prefixEnd_1039412 : Nat := 4983230072969 + 3 ^ 40 * 1039412 * 2
def baseEnd_1039412 : Nat := 355811969367461686313225

theorem tailTrace_1039412 : CollatzResearch.WordTrace tailWord_1039412 prefixEnd_1039412 355811969367461686313225 := by
  unfold tailWord_1039412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18955235055197658140912245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25273646740263544187882993 18955235055197658140912245)
  ·
    refine ⟨1777053286424780450710523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18955235055197658140912245 1777053286424780450710523)
    ·
      refine ⟨2665579929637170676065785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1777053286424780450710523 2665579929637170676065785)
      ·
        refine ⟨1999184947227878007049339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2665579929637170676065785 1999184947227878007049339)
        ·
          refine ⟨2998777420841817010574009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999184947227878007049339 2998777420841817010574009)
          ·
            refine ⟨2249083065631362757930507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2998777420841817010574009 2249083065631362757930507)
            ·
              refine ⟨3373624598447044136895761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249083065631362757930507 3373624598447044136895761)
              ·
                refine ⟨2530218448835283102671821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3373624598447044136895761 2530218448835283102671821)
                ·
                  refine ⟨948831918313231163501933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2530218448835283102671821 948831918313231163501933)
                  ·
                    refine ⟨355811969367461686313225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 948831918313231163501933 355811969367461686313225)
                    ·
                      rfl

theorem cell22_1039412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1039412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039412 prefixEnd_1039412 := by exact prefixLift 1039412
  have htrace : WordTrace (prefixWord ++ tailWord_1039412) baseStart_1039412 baseEnd_1039412 := by
    simpa [prefixWord, tailWord_1039412, baseEnd_1039412] using wordTrace_append hprefix tailTrace_1039412
  have hstable : (prefixWord ++ tailWord_1039412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039412).length < 2 ^ (prefixWord ++ tailWord_1039412).sum := by decide
  have hdescent : baseEnd_1039412 < baseStart_1039412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039436 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 10]
def baseStart_1039436 : Nat := 118140960795 + 1039436 * 2 ^ 59
def prefixEnd_1039436 : Nat := 4983230072969 + 3 ^ 40 * 1039436 * 2
def baseEnd_1039436 : Nat := 118606728352644541237717

theorem tailTrace_1039436 : CollatzResearch.WordTrace tailWord_1039436 prefixEnd_1039436 118606728352644541237717 := by
  unfold tailWord_1039436
  simp only [CollatzResearch.WordTrace]
  refine ⟨18955672731154184190349081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25274230308205578920465441 18955672731154184190349081)
  ·
    refine ⟨14216754548365638142761811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18955672731154184190349081 14216754548365638142761811)
    ·
      refine ⟨21325131822548457214142717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14216754548365638142761811 21325131822548457214142717)
      ·
        refine ⟨7996924433455671455303519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21325131822548457214142717 7996924433455671455303519)
        ·
          refine ⟨11995386650183507182955279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996924433455671455303519 11995386650183507182955279)
          ·
            refine ⟨17993079975275260774432919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11995386650183507182955279 17993079975275260774432919)
            ·
              refine ⟨26989619962912891161649379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17993079975275260774432919 26989619962912891161649379)
              ·
                refine ⟨40484429944369336742474069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26989619962912891161649379 40484429944369336742474069)
                ·
                  refine ⟨118606728352644541237717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 40484429944369336742474069 118606728352644541237717)
                  ·
                    rfl

theorem cell22_1039436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_1039436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039436 prefixEnd_1039436 := by exact prefixLift 1039436
  have htrace : WordTrace (prefixWord ++ tailWord_1039436) baseStart_1039436 baseEnd_1039436 := by
    simpa [prefixWord, tailWord_1039436, baseEnd_1039436] using wordTrace_append hprefix tailTrace_1039436
  have hstable : (prefixWord ++ tailWord_1039436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039436).length < 2 ^ (prefixWord ++ tailWord_1039436).sum := by decide
  have hdescent : baseEnd_1039436 < baseStart_1039436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039588 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1039588 : Nat := 118140960795 + 1039588 * 2 ^ 59
def prefixEnd_1039588 : Nat := 4983230072969 + 3 ^ 40 * 1039588 * 2
def baseEnd_1039588 : Nat := 118624072588085297970895

theorem tailTrace_1039588 : CollatzResearch.WordTrace tailWord_1039588 prefixEnd_1039588 118624072588085297970895 := by
  unfold tailWord_1039588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18958444678878849170115709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25277926238505132226820945 18958444678878849170115709)
  ·
    refine ⟨7109416754579568438793391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18958444678878849170115709 7109416754579568438793391)
    ·
      refine ⟨10664125131869352658190087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7109416754579568438793391 10664125131869352658190087)
      ·
        refine ⟨15996187697804028987285131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10664125131869352658190087 15996187697804028987285131)
        ·
          refine ⟨23994281546706043480927697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15996187697804028987285131 23994281546706043480927697)
          ·
            refine ⟨17995711160029532610695773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23994281546706043480927697 17995711160029532610695773)
            ·
              refine ⟨6748391685011074729010915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17995711160029532610695773 6748391685011074729010915)
              ·
                refine ⟨10122587527516612093516373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6748391685011074729010915 10122587527516612093516373)
                ·
                  refine ⟨118624072588085297970895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10122587527516612093516373 118624072588085297970895)
                  ·
                    rfl

theorem cell22_1039588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1039588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039588 prefixEnd_1039588 := by exact prefixLift 1039588
  have htrace : WordTrace (prefixWord ++ tailWord_1039588) baseStart_1039588 baseEnd_1039588 := by
    simpa [prefixWord, tailWord_1039588, baseEnd_1039588] using wordTrace_append hprefix tailTrace_1039588
  have hstable : (prefixWord ++ tailWord_1039588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039588).length < 2 ^ (prefixWord ++ tailWord_1039588).sum := by decide
  have hdescent : baseEnd_1039588 < baseStart_1039588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039633 : List Nat := [1, 2, 2, 1, 1, 4, 2, 9]
def baseStart_1039633 : Nat := 118140960795 + 1039633 * 2 ^ 59
def prefixEnd_1039633 : Nat := 4983230072969 + 3 ^ 40 * 1039633 * 2
def baseEnd_1039633 : Nat := 39543069131543419615283

theorem tailTrace_1039633 : CollatzResearch.WordTrace tailWord_1039633 prefixEnd_1039633 39543069131543419615283 := by
  unfold tailWord_1039633
  simp only [CollatzResearch.WordTrace]
  refine ⟨37918530642594671025619553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25279020428396447350413035 37918530642594671025619553)
  ·
    refine ⟨28438897981946003269214665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37918530642594671025619553 28438897981946003269214665)
    ·
      refine ⟨21329173486459502451910999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28438897981946003269214665 21329173486459502451910999)
      ·
        refine ⟨31993760229689253677866499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21329173486459502451910999 31993760229689253677866499)
        ·
          refine ⟨47990640344533880516799749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31993760229689253677866499 47990640344533880516799749)
          ·
            refine ⟨8998245064600102596899953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47990640344533880516799749 8998245064600102596899953)
            ·
              refine ⟨6748683798450076947674965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8998245064600102596899953 6748683798450076947674965)
              ·
                refine ⟨39543069131543419615283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6748683798450076947674965 39543069131543419615283)
                ·
                  rfl

theorem cell22_1039633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 9].length) (baseStart_1039633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039633 prefixEnd_1039633 := by exact prefixLift 1039633
  have htrace : WordTrace (prefixWord ++ tailWord_1039633) baseStart_1039633 baseEnd_1039633 := by
    simpa [prefixWord, tailWord_1039633, baseEnd_1039633] using wordTrace_append hprefix tailTrace_1039633
  have hstable : (prefixWord ++ tailWord_1039633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039633).length < 2 ^ (prefixWord ++ tailWord_1039633).sum := by decide
  have hdescent : baseEnd_1039633 < baseStart_1039633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039663 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 1, 8]
def baseStart_1039663 : Nat := 118140960795 + 1039663 * 2 ^ 59
def prefixEnd_1039663 : Nat := 4983230072969 + 3 ^ 40 * 1039663 * 2
def baseEnd_1039663 : Nat := 355897891796980698287455

theorem tailTrace_1039663 : CollatzResearch.WordTrace tailWord_1039663 prefixEnd_1039663 355897891796980698287455 := by
  unfold tailWord_1039663
  simp only [CollatzResearch.WordTrace]
  refine ⟨37919624832485986149211643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25279749888323990766141095 37919624832485986149211643)
  ·
    refine ⟨56879437248728979223817465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37919624832485986149211643 56879437248728979223817465)
    ·
      refine ⟨42659577936546734417863099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56879437248728979223817465 42659577936546734417863099)
      ·
        refine ⟨63989366904820101626794649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42659577936546734417863099 63989366904820101626794649)
        ·
          refine ⟨47992025178615076220095987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63989366904820101626794649 47992025178615076220095987)
          ·
            refine ⟨71988037767922614330143981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47992025178615076220095987 71988037767922614330143981)
            ·
              refine ⟨26995514162970980373803993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71988037767922614330143981 26995514162970980373803993)
              ·
                refine ⟨20246635622228235280352995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26995514162970980373803993 20246635622228235280352995)
                ·
                  refine ⟨30369953433342352920529493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20246635622228235280352995 30369953433342352920529493)
                  ·
                    refine ⟨355897891796980698287455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30369953433342352920529493 355897891796980698287455)
                    ·
                      rfl

theorem cell22_1039663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_1039663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039663 prefixEnd_1039663 := by exact prefixLift 1039663
  have htrace : WordTrace (prefixWord ++ tailWord_1039663) baseStart_1039663 baseEnd_1039663 := by
    simpa [prefixWord, tailWord_1039663, baseEnd_1039663] using wordTrace_append hprefix tailTrace_1039663
  have hstable : (prefixWord ++ tailWord_1039663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039663).length < 2 ^ (prefixWord ++ tailWord_1039663).sum := by decide
  have hdescent : baseEnd_1039663 < baseStart_1039663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039740 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 6]
def baseStart_1039740 : Nat := 118140960795 + 1039740 * 2 ^ 59
def prefixEnd_1039740 : Nat := 4983230072969 + 3 ^ 40 * 1039740 * 2
def baseEnd_1039740 : Nat := 118641416823526054704073

theorem tailTrace_1039740 : CollatzResearch.WordTrace tailWord_1039740 prefixEnd_1039740 118641416823526054704073 := by
  unfold tailWord_1039740
  simp only [CollatzResearch.WordTrace]
  refine ⟨18961216626603514149882337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25281622168804685533176449 18961216626603514149882337)
  ·
    refine ⟨14220912469952635612411753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18961216626603514149882337 14220912469952635612411753)
    ·
      refine ⟨10665684352464476709308815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14220912469952635612411753 10665684352464476709308815)
      ·
        refine ⟨15998526528696715063963223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10665684352464476709308815 15998526528696715063963223)
        ·
          refine ⟨23997789793045072595944835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15998526528696715063963223 23997789793045072595944835)
          ·
            refine ⟨35996684689567608893917253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23997789793045072595944835 35996684689567608893917253)
            ·
              refine ⟨6749378379293926667609485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35996684689567608893917253 6749378379293926667609485)
              ·
                refine ⟨2531016892235222500353557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6749378379293926667609485 2531016892235222500353557)
                ·
                  refine ⟨118641416823526054704073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2531016892235222500353557 118641416823526054704073)
                  ·
                    rfl

theorem cell22_1039740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_1039740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039740 prefixEnd_1039740 := by exact prefixLift 1039740
  have htrace : WordTrace (prefixWord ++ tailWord_1039740) baseStart_1039740 baseEnd_1039740 := by
    simpa [prefixWord, tailWord_1039740, baseEnd_1039740] using wordTrace_append hprefix tailTrace_1039740
  have hstable : (prefixWord ++ tailWord_1039740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039740).length < 2 ^ (prefixWord ++ tailWord_1039740).sum := by decide
  have hdescent : baseEnd_1039740 < baseStart_1039740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039847 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 7]
def baseStart_1039847 : Nat := 118140960795 + 1039847 * 2 ^ 59
def prefixEnd_1039847 : Nat := 4983230072969 + 3 ^ 40 * 1039847 * 2
def baseEnd_1039847 : Nat := 118653626252421850562297

theorem tailTrace_1039847 : CollatzResearch.WordTrace tailWord_1039847 prefixEnd_1039847 118653626252421850562297 := by
  unfold tailWord_1039847
  simp only [CollatzResearch.WordTrace]
  refine ⟨37926335863819385573909795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25284223909212923715939863 37926335863819385573909795)
  ·
    refine ⟨56889503795729078360864693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37926335863819385573909795 56889503795729078360864693)
    ·
      refine ⟨5333390980849601096331065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56889503795729078360864693 5333390980849601096331065)
      ·
        refine ⟨4000043235637200822248299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5333390980849601096331065 4000043235637200822248299)
        ·
          refine ⟨6000064853455801233372449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4000043235637200822248299 6000064853455801233372449)
          ·
            refine ⟨4500048640091850925029337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6000064853455801233372449 4500048640091850925029337)
            ·
              refine ⟨3375036480068888193772003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4500048640091850925029337 3375036480068888193772003)
              ·
                refine ⟨5062554720103332290658005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375036480068888193772003 5062554720103332290658005)
                ·
                  refine ⟨118653626252421850562297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5062554720103332290658005 118653626252421850562297)
                  ·
                    rfl

theorem cell22_1039847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 7].length) (baseStart_1039847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039847 prefixEnd_1039847 := by exact prefixLift 1039847
  have htrace : WordTrace (prefixWord ++ tailWord_1039847) baseStart_1039847 baseEnd_1039847 := by
    simpa [prefixWord, tailWord_1039847, baseEnd_1039847] using wordTrace_append hprefix tailTrace_1039847
  have hstable : (prefixWord ++ tailWord_1039847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039847).length < 2 ^ (prefixWord ++ tailWord_1039847).sum := by decide
  have hdescent : baseEnd_1039847 < baseStart_1039847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039864 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 5]
def baseStart_1039864 : Nat := 118140960795 + 1039864 * 2 ^ 59
def prefixEnd_1039864 : Nat := 4983230072969 + 3 ^ 40 * 1039864 * 2
def baseEnd_1039864 : Nat := 118655566068227724670613

theorem tailTrace_1039864 : CollatzResearch.WordTrace tailWord_1039864 prefixEnd_1039864 118655566068227724670613 := by
  unfold tailWord_1039864
  simp only [CollatzResearch.WordTrace]
  refine ⟨18963477952378898738639323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25284637269838531651519097 18963477952378898738639323)
  ·
    refine ⟨28445216928568348107958985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18963477952378898738639323 28445216928568348107958985)
    ·
      refine ⟨21333912696426261080969239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28445216928568348107958985 21333912696426261080969239)
      ·
        refine ⟨32000869044639391621453859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21333912696426261080969239 32000869044639391621453859)
        ·
          refine ⟨48001303566959087432180789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32000869044639391621453859 48001303566959087432180789)
          ·
            refine ⟨4500122209402414446766949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48001303566959087432180789 4500122209402414446766949)
            ·
              refine ⟨843772914262952708768803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4500122209402414446766949 843772914262952708768803)
              ·
                refine ⟨1265659371394429063153205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843772914262952708768803 1265659371394429063153205)
                ·
                  refine ⟨118655566068227724670613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1265659371394429063153205 118655566068227724670613)
                  ·
                    rfl

theorem cell22_1039864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 5].length) (baseStart_1039864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039864 prefixEnd_1039864 := by exact prefixLift 1039864
  have htrace : WordTrace (prefixWord ++ tailWord_1039864) baseStart_1039864 baseEnd_1039864 := by
    simpa [prefixWord, tailWord_1039864, baseEnd_1039864] using wordTrace_append hprefix tailTrace_1039864
  have hstable : (prefixWord ++ tailWord_1039864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039864).length < 2 ^ (prefixWord ++ tailWord_1039864).sum := by decide
  have hdescent : baseEnd_1039864 < baseStart_1039864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039922 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1039922 : Nat := 118140960795 + 1039922 * 2 ^ 59
def prefixEnd_1039922 : Nat := 4983230072969 + 3 ^ 40 * 1039922 * 2
def baseEnd_1039922 : Nat := 355986552789990356061661

theorem tailTrace_1039922 : CollatzResearch.WordTrace tailWord_1039922 prefixEnd_1039922 355986552789990356061661 := by
  unfold tailWord_1039922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9482267834636918345722505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25286047559031782255260013 9482267834636918345722505)
  ·
    refine ⟨7111700875977688759291879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9482267834636918345722505 7111700875977688759291879)
    ·
      refine ⟨10667551313966533138937819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7111700875977688759291879 10667551313966533138937819)
      ·
        refine ⟨16001326970949799708406729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10667551313966533138937819 16001326970949799708406729)
        ·
          refine ⟨12000995228212349781305047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16001326970949799708406729 12000995228212349781305047)
          ·
            refine ⟨18001492842318524671957571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12000995228212349781305047 18001492842318524671957571)
            ·
              refine ⟨27002239263477787007936357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18001492842318524671957571 27002239263477787007936357)
              ·
                refine ⟨5062919861902085063988067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27002239263477787007936357 5062919861902085063988067)
                ·
                  refine ⟨7594379792853127595982101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062919861902085063988067 7594379792853127595982101)
                  ·
                    refine ⟨355986552789990356061661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7594379792853127595982101 355986552789990356061661)
                    ·
                      rfl

theorem cell22_1039922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1039922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039922 prefixEnd_1039922 := by exact prefixLift 1039922
  have htrace : WordTrace (prefixWord ++ tailWord_1039922) baseStart_1039922 baseEnd_1039922 := by
    simpa [prefixWord, tailWord_1039922, baseEnd_1039922] using wordTrace_append hprefix tailTrace_1039922
  have hstable : (prefixWord ++ tailWord_1039922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039922).length < 2 ^ (prefixWord ++ tailWord_1039922).sum := by decide
  have hdescent : baseEnd_1039922 < baseStart_1039922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039926 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_1039926 : Nat := 118140960795 + 1039926 * 2 ^ 59
def prefixEnd_1039926 : Nat := 4983230072969 + 3 ^ 40 * 1039926 * 2
def baseEnd_1039926 : Nat := 118662640690578559653883

theorem tailTrace_1039926 : CollatzResearch.WordTrace tailWord_1039926 prefixEnd_1039926 118662640690578559653883 := by
  unfold tailWord_1039926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370576076908323879127227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25286144820355454710690421 2370576076908323879127227)
  ·
    refine ⟨3555864115362485818690841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370576076908323879127227 3555864115362485818690841)
    ·
      refine ⟨2666898086521864364018131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3555864115362485818690841 2666898086521864364018131)
      ·
        refine ⟨4000347129782796546027197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2666898086521864364018131 4000347129782796546027197)
        ·
          refine ⟨1500130173668548704760199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4000347129782796546027197 1500130173668548704760199)
          ·
            refine ⟨2250195260502823057140299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500130173668548704760199 2250195260502823057140299)
            ·
              refine ⟨3375292890754234585710449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250195260502823057140299 3375292890754234585710449)
              ·
                refine ⟨2531469668065675939282837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375292890754234585710449 2531469668065675939282837)
                ·
                  refine ⟨118662640690578559653883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2531469668065675939282837 118662640690578559653883)
                  ·
                    rfl

theorem cell22_1039926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_1039926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039926 prefixEnd_1039926 := by exact prefixLift 1039926
  have htrace : WordTrace (prefixWord ++ tailWord_1039926) baseStart_1039926 baseEnd_1039926 := by
    simpa [prefixWord, tailWord_1039926, baseEnd_1039926] using wordTrace_append hprefix tailTrace_1039926
  have hstable : (prefixWord ++ tailWord_1039926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039926).length < 2 ^ (prefixWord ++ tailWord_1039926).sum := by decide
  have hdescent : baseEnd_1039926 < baseStart_1039926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039986 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_1039986 : Nat := 118140960795 + 1039986 * 2 ^ 59
def prefixEnd_1039986 : Nat := 4983230072969 + 3 ^ 40 * 1039986 * 2
def baseEnd_1039986 : Nat := 356008461297915522461465

theorem tailTrace_1039986 : CollatzResearch.WordTrace tailWord_1039986 prefixEnd_1039986 356008461297915522461465 := by
  unfold tailWord_1039986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9482851402578953078304953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25287603740210541542146541 9482851402578953078304953)
  ·
    refine ⟨7112138551934214808728715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9482851402578953078304953 7112138551934214808728715)
    ·
      refine ⟨10668207827901322213093073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7112138551934214808728715 10668207827901322213093073)
      ·
        refine ⟨8001155870925991659819805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10668207827901322213093073 8001155870925991659819805)
        ·
          refine ⟨3000433451597246872432427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8001155870925991659819805 3000433451597246872432427)
          ·
            refine ⟨4500650177395870308648641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000433451597246872432427 4500650177395870308648641)
            ·
              refine ⟨3375487633046902731486481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4500650177395870308648641 3375487633046902731486481)
              ·
                refine ⟨2531615724785177048614861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375487633046902731486481 2531615724785177048614861)
                ·
                  refine ⟨949355896794441393230573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2531615724785177048614861 949355896794441393230573)
                  ·
                    refine ⟨356008461297915522461465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949355896794441393230573 356008461297915522461465)
                    ·
                      rfl

theorem cell22_1039986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_1039986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039986 prefixEnd_1039986 := by exact prefixLift 1039986
  have htrace : WordTrace (prefixWord ++ tailWord_1039986) baseStart_1039986 baseEnd_1039986 := by
    simpa [prefixWord, tailWord_1039986, baseEnd_1039986] using wordTrace_append hprefix tailTrace_1039986
  have hstable : (prefixWord ++ tailWord_1039986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039986).length < 2 ^ (prefixWord ++ tailWord_1039986).sum := by decide
  have hdescent : baseEnd_1039986 < baseStart_1039986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040020 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1040020 : Nat := 118140960795 + 1040020 * 2 ^ 59
def prefixEnd_1040020 : Nat := 4983230072969 + 3 ^ 40 * 1040020 * 2
def baseEnd_1040020 : Nat := 356020100192750767111361

theorem tailTrace_1040020 : CollatzResearch.WordTrace tailWord_1040020 prefixEnd_1040020 356020100192750767111361 := by
  unfold tailWord_1040020
  simp only [CollatzResearch.WordTrace]
  refine ⟨18966322846096318059978757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25288430461461757413305009 18966322846096318059978757)
  ·
    refine ⟨3556185533643059636246017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18966322846096318059978757 3556185533643059636246017)
    ·
      refine ⟨2667139150232294727184513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3556185533643059636246017 2667139150232294727184513)
      ·
        refine ⟨2000354362674221045388385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2667139150232294727184513 2000354362674221045388385)
        ·
          refine ⟨1500265772005665784041289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2000354362674221045388385 1500265772005665784041289)
          ·
            refine ⟨1125199329004249338030967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500265772005665784041289 1125199329004249338030967)
            ·
              refine ⟨1687798993506374007046451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125199329004249338030967 1687798993506374007046451)
              ·
                refine ⟨2531698490259561010569677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687798993506374007046451 2531698490259561010569677)
                ·
                  refine ⟨949386933847335378963629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2531698490259561010569677 949386933847335378963629)
                  ·
                    refine ⟨356020100192750767111361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949386933847335378963629 356020100192750767111361)
                    ·
                      rfl

theorem cell22_1040020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1040020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040020 prefixEnd_1040020 := by exact prefixLift 1040020
  have htrace : WordTrace (prefixWord ++ tailWord_1040020) baseStart_1040020 baseEnd_1040020 := by
    simpa [prefixWord, tailWord_1040020, baseEnd_1040020] using wordTrace_append hprefix tailTrace_1040020
  have hstable : (prefixWord ++ tailWord_1040020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040020).length < 2 ^ (prefixWord ++ tailWord_1040020).sum := by decide
  have hdescent : baseEnd_1040020 < baseStart_1040020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040029 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1040029 : Nat := 118140960795 + 1040029 * 2 ^ 59
def prefixEnd_1040029 : Nat := 4983230072969 + 3 ^ 40 * 1040029 * 2
def baseEnd_1040029 : Nat := 356023181076677743636333

theorem tailTrace_1040029 : CollatzResearch.WordTrace tailWord_1040029 prefixEnd_1040029 356023181076677743636333 := by
  unfold tailWord_1040029
  simp only [CollatzResearch.WordTrace]
  refine ⟨37932973949160030657035141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25288649299440020438023427 37932973949160030657035141)
  ·
    refine ⟨7112432615467505748194089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37932973949160030657035141 7112432615467505748194089)
    ·
      refine ⟨5334324461600629311145567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7112432615467505748194089 5334324461600629311145567)
      ·
        refine ⟨8001486692400943966718351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5334324461600629311145567 8001486692400943966718351)
        ·
          refine ⟨12002230038601415950077527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8001486692400943966718351 12002230038601415950077527)
          ·
            refine ⟨18003345057902123925116291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12002230038601415950077527 18003345057902123925116291)
            ·
              refine ⟨27005017586853185887674437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18003345057902123925116291 27005017586853185887674437)
              ·
                refine ⟨5063440797534972353938957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27005017586853185887674437 5063440797534972353938957)
                ·
                  refine ⟨1898790299075614632727109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5063440797534972353938957 1898790299075614632727109)
                  ·
                    refine ⟨356023181076677743636333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1898790299075614632727109 356023181076677743636333)
                    ·
                      rfl

theorem cell22_1040029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1040029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040029 prefixEnd_1040029 := by exact prefixLift 1040029
  have htrace : WordTrace (prefixWord ++ tailWord_1040029) baseStart_1040029 baseEnd_1040029 := by
    simpa [prefixWord, tailWord_1040029, baseEnd_1040029] using wordTrace_append hprefix tailTrace_1040029
  have hstable : (prefixWord ++ tailWord_1040029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040029).length < 2 ^ (prefixWord ++ tailWord_1040029).sum := by decide
  have hdescent : baseEnd_1040029 < baseStart_1040029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040033 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 5]
def baseStart_1040033 : Nat := 118140960795 + 1040033 * 2 ^ 59
def prefixEnd_1040033 : Nat := 4983230072969 + 3 ^ 40 * 1040033 * 2
def baseEnd_1040033 : Nat := 118674850119474355512107

theorem tailTrace_1040033 : CollatzResearch.WordTrace tailWord_1040033 prefixEnd_1040033 118674850119474355512107 := by
  unfold tailWord_1040033
  simp only [CollatzResearch.WordTrace]
  refine ⟨37933119841145539340180753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25288746560763692893453835 37933119841145539340180753)
  ·
    refine ⟨28449839880859154505135565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37933119841145539340180753 28449839880859154505135565)
    ·
      refine ⟨10668689955322182939425837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28449839880859154505135565 10668689955322182939425837)
      ·
        refine ⟨4000758733245818602284689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10668689955322182939425837 4000758733245818602284689)
        ·
          refine ⟨3000569049934363951713517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4000758733245818602284689 3000569049934363951713517)
          ·
            refine ⟨1125213393725386481892569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3000569049934363951713517 1125213393725386481892569)
            ·
              refine ⟨843910045294039861419427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125213393725386481892569 843910045294039861419427)
              ·
                refine ⟨1265865067941059792129141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843910045294039861419427 1265865067941059792129141)
                ·
                  refine ⟨118674850119474355512107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1265865067941059792129141 118674850119474355512107)
                  ·
                    rfl

theorem cell22_1040033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 5].length) (baseStart_1040033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040033 prefixEnd_1040033 := by exact prefixLift 1040033
  have htrace : WordTrace (prefixWord ++ tailWord_1040033) baseStart_1040033 baseEnd_1040033 := by
    simpa [prefixWord, tailWord_1040033, baseEnd_1040033] using wordTrace_append hprefix tailTrace_1040033
  have hstable : (prefixWord ++ tailWord_1040033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040033).length < 2 ^ (prefixWord ++ tailWord_1040033).sum := by decide
  have hdescent : baseEnd_1040033 < baseStart_1040033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040059 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 6, 3]
def baseStart_1040059 : Nat := 118140960795 + 1040059 * 2 ^ 59
def prefixEnd_1040059 : Nat := 4983230072969 + 3 ^ 40 * 1040059 * 2
def baseEnd_1040059 : Nat := 356033450689767665386241

theorem tailTrace_1040059 : CollatzResearch.WordTrace tailWord_1040059 prefixEnd_1040059 356033450689767665386241 := by
  unfold tailWord_1040059
  simp only [CollatzResearch.WordTrace]
  refine ⟨37934068139051345780627231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25289378759367563853751487 37934068139051345780627231)
  ·
    refine ⟨56901102208577018670940847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37934068139051345780627231 56901102208577018670940847)
    ·
      refine ⟨85351653312865528006411271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56901102208577018670940847 85351653312865528006411271)
      ·
        refine ⟨128027479969298292009616907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85351653312865528006411271 128027479969298292009616907)
        ·
          refine ⟨192041219953947438014425361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128027479969298292009616907 192041219953947438014425361)
          ·
            refine ⟨144030914965460578510819021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192041219953947438014425361 144030914965460578510819021)
            ·
              refine ⟨54011593112047716941557133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144030914965460578510819021 54011593112047716941557133)
              ·
                refine ⟨20254347417017893853083925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54011593112047716941557133 20254347417017893853083925)
                ·
                  refine ⟨949422535172713774363309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20254347417017893853083925 949422535172713774363309)
                  ·
                    refine ⟨356033450689767665386241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949422535172713774363309 356033450689767665386241)
                    ·
                      rfl

theorem cell22_1040059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 3].length) (baseStart_1040059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040059 prefixEnd_1040059 := by exact prefixLift 1040059
  have htrace : WordTrace (prefixWord ++ tailWord_1040059) baseStart_1040059 baseEnd_1040059 := by
    simpa [prefixWord, tailWord_1040059, baseEnd_1040059] using wordTrace_append hprefix tailTrace_1040059
  have hstable : (prefixWord ++ tailWord_1040059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040059).length < 2 ^ (prefixWord ++ tailWord_1040059).sum := by decide
  have hdescent : baseEnd_1040059 < baseStart_1040059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040061 : List Nat := [1, 4, 1, 2, 1, 2, 2, 5, 4]
def baseStart_1040061 : Nat := 118140960795 + 1040061 * 2 ^ 59
def prefixEnd_1040061 : Nat := 4983230072969 + 3 ^ 40 * 1040061 * 2
def baseEnd_1040061 : Nat := 118678045110213442278745

theorem tailTrace_1040061 : CollatzResearch.WordTrace tailWord_1040061 prefixEnd_1040061 118678045110213442278745 := by
  unfold tailWord_1040061
  simp only [CollatzResearch.WordTrace]
  refine ⟨37934141085044100122200037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25289427390029400081466691 37934141085044100122200037)
  ·
    refine ⟨7112651453445768772912507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37934141085044100122200037 7112651453445768772912507)
    ·
      refine ⟨10668977180168653159368761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7112651453445768772912507 10668977180168653159368761)
      ·
        refine ⟨8001732885126489869526571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10668977180168653159368761 8001732885126489869526571)
        ·
          refine ⟨12002599327689734804289857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8001732885126489869526571 12002599327689734804289857)
          ·
            refine ⟨9001949495767301103217393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12002599327689734804289857 9001949495767301103217393)
            ·
              refine ⟨6751462121825475827413045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9001949495767301103217393 6751462121825475827413045)
              ·
                refine ⟨632949573921138358819973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6751462121825475827413045 632949573921138358819973)
                ·
                  refine ⟨118678045110213442278745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632949573921138358819973 118678045110213442278745)
                  ·
                    rfl

theorem cell22_1040061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_1040061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040061 prefixEnd_1040061 := by exact prefixLift 1040061
  have htrace : WordTrace (prefixWord ++ tailWord_1040061) baseStart_1040061 baseEnd_1040061 := by
    simpa [prefixWord, tailWord_1040061, baseEnd_1040061] using wordTrace_append hprefix tailTrace_1040061
  have hstable : (prefixWord ++ tailWord_1040061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040061).length < 2 ^ (prefixWord ++ tailWord_1040061).sum := by decide
  have hdescent : baseEnd_1040061 < baseStart_1040061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040089 : List Nat := [1, 2, 1, 2, 3, 3, 3, 7]
def baseStart_1040089 : Nat := 118140960795 + 1040089 * 2 ^ 59
def prefixEnd_1040089 : Nat := 4983230072969 + 3 ^ 40 * 1040089 * 2
def baseEnd_1040089 : Nat := 39560413366984176348461

theorem tailTrace_1040089 : CollatzResearch.WordTrace tailWord_1040089 prefixEnd_1040089 39560413366984176348461 := by
  unfold tailWord_1040089
  simp only [CollatzResearch.WordTrace]
  refine ⟨37935162328942660904219321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25290108219295107269479547 37935162328942660904219321)
  ·
    refine ⟨28451371746706995678164491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37935162328942660904219321 28451371746706995678164491)
    ·
      refine ⟨42677057620060493517246737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28451371746706995678164491 42677057620060493517246737)
      ·
        refine ⟨32007793215045370137935053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42677057620060493517246737 32007793215045370137935053)
        ·
          refine ⟨12002922455642013801725645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32007793215045370137935053 12002922455642013801725645)
          ·
            refine ⟨4501095920865755175647117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12002922455642013801725645 4501095920865755175647117)
            ·
              refine ⟨1687910970324658190867669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4501095920865755175647117 1687910970324658190867669)
              ·
                refine ⟨39560413366984176348461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1687910970324658190867669 39560413366984176348461)
                ·
                  rfl

theorem cell22_1040089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 7].length) (baseStart_1040089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040089 prefixEnd_1040089 := by exact prefixLift 1040089
  have htrace : WordTrace (prefixWord ++ tailWord_1040089) baseStart_1040089 baseEnd_1040089 := by
    simpa [prefixWord, tailWord_1040089, baseEnd_1040089] using wordTrace_append hprefix tailTrace_1040089
  have hstable : (prefixWord ++ tailWord_1040089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040089).length < 2 ^ (prefixWord ++ tailWord_1040089).sum := by decide
  have hdescent : baseEnd_1040089 < baseStart_1040089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040138 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_1040138 : Nat := 118140960795 + 1040138 * 2 ^ 59
def prefixEnd_1040138 : Nat := 4983230072969 + 3 ^ 40 * 1040138 * 2
def baseEnd_1040138 : Nat := 356060494004237792660999

theorem tailTrace_1040138 : CollatzResearch.WordTrace tailWord_1040138 prefixEnd_1040138 356060494004237792660999 := by
  unfold tailWord_1040138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9484237376441285568188267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25291299670510094848502045 9484237376441285568188267)
  ·
    refine ⟨14226356064661928352282401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9484237376441285568188267 14226356064661928352282401)
    ·
      refine ⟨10669767048496446264211801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14226356064661928352282401 10669767048496446264211801)
      ·
        refine ⟨8002325286372334698158851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10669767048496446264211801 8002325286372334698158851)
        ·
          refine ⟨12003487929558502047238277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8002325286372334698158851 12003487929558502047238277)
          ·
            refine ⟨2250653986792219133857177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12003487929558502047238277 2250653986792219133857177)
            ·
              refine ⟨1687990490094164350392883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250653986792219133857177 1687990490094164350392883)
              ·
                refine ⟨2531985735141246525589325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687990490094164350392883 2531985735141246525589325)
                ·
                  refine ⟨949494650677967447095997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2531985735141246525589325 949494650677967447095997)
                  ·
                    refine ⟨356060494004237792660999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949494650677967447095997 356060494004237792660999)
                    ·
                      rfl

theorem cell22_1040138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_1040138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040138 prefixEnd_1040138 := by exact prefixLift 1040138
  have htrace : WordTrace (prefixWord ++ tailWord_1040138) baseStart_1040138 baseEnd_1040138 := by
    simpa [prefixWord, tailWord_1040138, baseEnd_1040138] using wordTrace_append hprefix tailTrace_1040138
  have hstable : (prefixWord ++ tailWord_1040138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040138).length < 2 ^ (prefixWord ++ tailWord_1040138).sum := by decide
  have hdescent : baseEnd_1040138 < baseStart_1040138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040215 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 1, 4]
def baseStart_1040215 : Nat := 118140960795 + 1040215 * 2 ^ 59
def prefixEnd_1040215 : Nat := 4983230072969 + 3 ^ 40 * 1040215 * 2
def baseEnd_1040215 : Nat := 356086852677835258485763

theorem tailTrace_1040215 : CollatzResearch.WordTrace tailWord_1040215 prefixEnd_1040215 356086852677835258485763 := by
  unfold tailWord_1040215
  simp only [CollatzResearch.WordTrace]
  refine ⟨37939757926486184423306099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25293171950990789615537399 37939757926486184423306099)
  ·
    refine ⟨56909636889729276634959149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37939757926486184423306099 56909636889729276634959149)
    ·
      refine ⟨21341113833648478738109681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56909636889729276634959149 21341113833648478738109681)
      ·
        refine ⟨16005835375236359053582261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21341113833648478738109681 16005835375236359053582261)
        ·
          refine ⟨1500547066428408661273337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16005835375236359053582261 1500547066428408661273337)
          ·
            refine ⟨1125410299821306495955003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500547066428408661273337 1125410299821306495955003)
            ·
              refine ⟨1688115449731959743932505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125410299821306495955003 1688115449731959743932505)
              ·
                refine ⟨1266086587298969807949379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688115449731959743932505 1266086587298969807949379)
                ·
                  refine ⟨1899129880948454711924069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266086587298969807949379 1899129880948454711924069)
                  ·
                    refine ⟨356086852677835258485763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1899129880948454711924069 356086852677835258485763)
                    ·
                      rfl

theorem cell22_1040215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_1040215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040215 prefixEnd_1040215 := by exact prefixLift 1040215
  have htrace : WordTrace (prefixWord ++ tailWord_1040215) baseStart_1040215 baseEnd_1040215 := by
    simpa [prefixWord, tailWord_1040215, baseEnd_1040215] using wordTrace_append hprefix tailTrace_1040215
  have hstable : (prefixWord ++ tailWord_1040215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040215).length < 2 ^ (prefixWord ++ tailWord_1040215).sum := by decide
  have hdescent : baseEnd_1040215 < baseStart_1040215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040228 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_1040228 : Nat := 118140960795 + 1040228 * 2 ^ 59
def prefixEnd_1040228 : Nat := 4983230072969 + 3 ^ 40 * 1040228 * 2
def baseEnd_1040228 : Nat := 356091302843507557910723

theorem tailTrace_1040228 : CollatzResearch.WordTrace tailWord_1040228 prefixEnd_1040228 356091302843507557910723 := by
  unfold tailWord_1040228
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970116037719543821764669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25293488050292725095686225 18970116037719543821764669)
  ·
    refine ⟨7113793514144828933161751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18970116037719543821764669 7113793514144828933161751)
    ·
      refine ⟨10670690271217243399742627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7113793514144828933161751 10670690271217243399742627)
      ·
        refine ⟨16006035406825865099613941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10670690271217243399742627 16006035406825865099613941)
        ·
          refine ⟨1500565819389924853088807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16006035406825865099613941 1500565819389924853088807)
          ·
            refine ⟨2250848729084887279633211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500565819389924853088807 2250848729084887279633211)
            ·
              refine ⟨3376273093627330919449817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250848729084887279633211 3376273093627330919449817)
              ·
                refine ⟨2532204820220498189587363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3376273093627330919449817 2532204820220498189587363)
                ·
                  refine ⟨3798307230330747284381045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532204820220498189587363 3798307230330747284381045)
                  ·
                    refine ⟨356091302843507557910723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3798307230330747284381045 356091302843507557910723)
                    ·
                      rfl

theorem cell22_1040228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_1040228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040228 prefixEnd_1040228 := by exact prefixLift 1040228
  have htrace : WordTrace (prefixWord ++ tailWord_1040228) baseStart_1040228 baseEnd_1040228 := by
    simpa [prefixWord, tailWord_1040228, baseEnd_1040228] using wordTrace_append hprefix tailTrace_1040228
  have hstable : (prefixWord ++ tailWord_1040228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040228).length < 2 ^ (prefixWord ++ tailWord_1040228).sum := by decide
  have hdescent : baseEnd_1040228 < baseStart_1040228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040245 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1040245 : Nat := 118140960795 + 1040245 * 2 ^ 59
def prefixEnd_1040245 : Nat := 4983230072969 + 3 ^ 40 * 1040245 * 2
def baseEnd_1040245 : Nat := 356097122290925180235671

theorem tailTrace_1040245 : CollatzResearch.WordTrace tailWord_1040245 prefixEnd_1040245 356097122290925180235671 := by
  unfold tailWord_1040245
  simp only [CollatzResearch.WordTrace]
  refine ⟨37940852116377499546898189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25293901410918333031265459 37940852116377499546898189)
  ·
    refine ⟨14227819543641562330086821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37940852116377499546898189 14227819543641562330086821)
    ·
      refine ⟨2667716164432792936891279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14227819543641562330086821 2667716164432792936891279)
      ·
        refine ⟨4001574246649189405336919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2667716164432792936891279 4001574246649189405336919)
        ·
          refine ⟨6002361369973784108005379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001574246649189405336919 6002361369973784108005379)
          ·
            refine ⟨9003542054960676162008069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002361369973784108005379 9003542054960676162008069)
            ·
              refine ⟨1688164135305126780376513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9003542054960676162008069 1688164135305126780376513)
              ·
                refine ⟨1266123101478845085282385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688164135305126780376513 1266123101478845085282385)
                ·
                  refine ⟨949592326109133813961789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1266123101478845085282385 949592326109133813961789)
                  ·
                    refine ⟨356097122290925180235671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949592326109133813961789 356097122290925180235671)
                    ·
                      rfl

theorem cell22_1040245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1040245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040245 prefixEnd_1040245 := by exact prefixLift 1040245
  have htrace : WordTrace (prefixWord ++ tailWord_1040245) baseStart_1040245 baseEnd_1040245 := by
    simpa [prefixWord, tailWord_1040245, baseEnd_1040245] using wordTrace_append hprefix tailTrace_1040245
  have hstable : (prefixWord ++ tailWord_1040245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040245).length < 2 ^ (prefixWord ++ tailWord_1040245).sum := by decide
  have hdescent : baseEnd_1040245 < baseStart_1040245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040296 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1040296 : Nat := 118140960795 + 1040296 * 2 ^ 59
def prefixEnd_1040296 : Nat := 4983230072969 + 3 ^ 40 * 1040296 * 2
def baseEnd_1040296 : Nat := 356114580633178047210515

theorem tailTrace_1040296 : CollatzResearch.WordTrace tailWord_1040296 prefixEnd_1040296 356114580633178047210515 := by
  unfold tailWord_1040296
  simp only [CollatzResearch.WordTrace]
  refine ⟨18971356119596367628502371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25295141492795156838003161 18971356119596367628502371)
  ·
    refine ⟨28457034179394551442753557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18971356119596367628502371 28457034179394551442753557)
    ·
      refine ⟨1333923477159119598879073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28457034179394551442753557 1333923477159119598879073)
      ·
        refine ⟨1000442607869339699159305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1333923477159119598879073 1000442607869339699159305)
        ·
          refine ⟨750331955902004774369479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000442607869339699159305 750331955902004774369479)
          ·
            refine ⟨1125497933853007161554219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750331955902004774369479 1125497933853007161554219)
            ·
              refine ⟨1688246900779510742331329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125497933853007161554219 1688246900779510742331329)
              ·
                refine ⟨1266185175584633056748497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688246900779510742331329 1266185175584633056748497)
                ·
                  refine ⟨949638881688474792561373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1266185175584633056748497 949638881688474792561373)
                  ·
                    refine ⟨356114580633178047210515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949638881688474792561373 356114580633178047210515)
                    ·
                      rfl

theorem cell22_1040296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1040296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040296 prefixEnd_1040296 := by exact prefixLift 1040296
  have htrace : WordTrace (prefixWord ++ tailWord_1040296) baseStart_1040296 baseEnd_1040296 := by
    simpa [prefixWord, tailWord_1040296, baseEnd_1040296] using wordTrace_append hprefix tailTrace_1040296
  have hstable : (prefixWord ++ tailWord_1040296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040296).length < 2 ^ (prefixWord ++ tailWord_1040296).sum := by decide
  have hdescent : baseEnd_1040296 < baseStart_1040296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040318 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1040318 : Nat := 118140960795 + 1040318 * 2 ^ 59
def prefixEnd_1040318 : Nat := 4983230072969 + 3 ^ 40 * 1040318 * 2
def baseEnd_1040318 : Nat := 356122111682777323160447

theorem tailTrace_1040318 : CollatzResearch.WordTrace tailWord_1040318 prefixEnd_1040318 356122111682777323160447 := by
  unfold tailWord_1040318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742939330639129126788201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25295676430075355342870405 4742939330639129126788201)
  ·
    refine ⟨3557204497979346845091151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4742939330639129126788201 3557204497979346845091151)
    ·
      refine ⟨5335806746969020267636727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3557204497979346845091151 5335806746969020267636727)
      ·
        refine ⟨8003710120453530401455091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5335806746969020267636727 8003710120453530401455091)
        ·
          refine ⟨12005565180680295602182637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8003710120453530401455091 12005565180680295602182637)
          ·
            refine ⟨4502086942755110850818489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12005565180680295602182637 4502086942755110850818489)
            ·
              refine ⟨3376565207066333138113867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4502086942755110850818489 3376565207066333138113867)
              ·
                refine ⟨5064847810599499707170801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376565207066333138113867 5064847810599499707170801)
                ·
                  refine ⟨3798635857949624780378101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5064847810599499707170801 3798635857949624780378101)
                  ·
                    refine ⟨356122111682777323160447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3798635857949624780378101 356122111682777323160447)
                    ·
                      rfl

theorem cell22_1040318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1040318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040318 prefixEnd_1040318 := by exact prefixLift 1040318
  have htrace : WordTrace (prefixWord ++ tailWord_1040318) baseStart_1040318 baseEnd_1040318 := by
    simpa [prefixWord, tailWord_1040318, baseEnd_1040318] using wordTrace_append hprefix tailTrace_1040318
  have hstable : (prefixWord ++ tailWord_1040318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040318).length < 2 ^ (prefixWord ++ tailWord_1040318).sum := by decide
  have hdescent : baseEnd_1040318 < baseStart_1040318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040331 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 6]
def baseStart_1040331 : Nat := 118140960795 + 1040331 * 2 ^ 59
def prefixEnd_1040331 : Nat := 4983230072969 + 3 ^ 40 * 1040331 * 2
def baseEnd_1040331 : Nat := 118708853949483207528469

theorem tailTrace_1040331 : CollatzResearch.WordTrace tailWord_1040331 prefixEnd_1040331 118708853949483207528469 := by
  unfold tailWord_1040331
  simp only [CollatzResearch.WordTrace]
  refine ⟨37943988794065936234528847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25295992529377290823019231 37943988794065936234528847)
  ·
    refine ⟨56915983191098904351793271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37943988794065936234528847 56915983191098904351793271)
    ·
      refine ⟨85373974786648356527689907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56915983191098904351793271 85373974786648356527689907)
      ·
        refine ⟨128060962179972534791534861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85373974786648356527689907 128060962179972534791534861)
        ·
          refine ⟨48022860817489700546825573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128060962179972534791534861 48022860817489700546825573)
          ·
            refine ⟨9004286403279318852529795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48022860817489700546825573 9004286403279318852529795)
            ·
              refine ⟨13506429604918978278794693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004286403279318852529795 13506429604918978278794693)
              ·
                refine ⟨2532455550922308427274005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13506429604918978278794693 2532455550922308427274005)
                ·
                  refine ⟨118708853949483207528469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2532455550922308427274005 118708853949483207528469)
                  ·
                    rfl

theorem cell22_1040331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 6].length) (baseStart_1040331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040331 prefixEnd_1040331 := by exact prefixLift 1040331
  have htrace : WordTrace (prefixWord ++ tailWord_1040331) baseStart_1040331 baseEnd_1040331 := by
    simpa [prefixWord, tailWord_1040331, baseEnd_1040331] using wordTrace_append hprefix tailTrace_1040331
  have hstable : (prefixWord ++ tailWord_1040331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040331).length < 2 ^ (prefixWord ++ tailWord_1040331).sum := by decide
  have hdescent : baseEnd_1040331 < baseStart_1040331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040376 : List Nat := [2, 1, 2, 1, 1, 3, 3, 9]
def baseStart_1040376 : Nat := 118140960795 + 1040376 * 2 ^ 59
def prefixEnd_1040376 : Nat := 4983230072969 + 3 ^ 40 * 1040376 * 2
def baseEnd_1040376 : Nat := 39571329585342722801141

theorem tailTrace_1040376 : CollatzResearch.WordTrace tailWord_1040376 prefixEnd_1040376 39571329585342722801141 := by
  unfold tailWord_1040376
  simp only [CollatzResearch.WordTrace]
  refine ⟨18972815039451454459958491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25297086719268605946611321 18972815039451454459958491)
  ·
    refine ⟨28459222559177181689937737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18972815039451454459958491 28459222559177181689937737)
    ·
      refine ⟨21344416919382886267453303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28459222559177181689937737 21344416919382886267453303)
      ·
        refine ⟨32016625379074329401179955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21344416919382886267453303 32016625379074329401179955)
        ·
          refine ⟨48024938068611494101769933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32016625379074329401179955 48024938068611494101769933)
          ·
            refine ⟨18009351775729310288163725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48024938068611494101769933 18009351775729310288163725)
            ·
              refine ⟨6753506915898491358061397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18009351775729310288163725 6753506915898491358061397)
              ·
                refine ⟨39571329585342722801141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6753506915898491358061397 39571329585342722801141)
                ·
                  rfl

theorem cell22_1040376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 9].length) (baseStart_1040376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040376 prefixEnd_1040376 := by exact prefixLift 1040376
  have htrace : WordTrace (prefixWord ++ tailWord_1040376) baseStart_1040376 baseEnd_1040376 := by
    simpa [prefixWord, tailWord_1040376, baseEnd_1040376] using wordTrace_append hprefix tailTrace_1040376
  have hstable : (prefixWord ++ tailWord_1040376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040376).length < 2 ^ (prefixWord ++ tailWord_1040376).sum := by decide
  have hdescent : baseEnd_1040376 < baseStart_1040376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040380 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_1040380 : Nat := 118140960795 + 1040380 * 2 ^ 59
def prefixEnd_1040380 : Nat := 4983230072969 + 3 ^ 40 * 1040380 * 2
def baseEnd_1040380 : Nat := 356143335549829828110257

theorem tailTrace_1040380 : CollatzResearch.WordTrace tailWord_1040380 prefixEnd_1040380 356143335549829828110257 := by
  unfold tailWord_1040380
  simp only [CollatzResearch.WordTrace]
  refine ⟨18972887985444208801531297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25297183980592278402041729 18972887985444208801531297)
  ·
    refine ⟨14229665989083156601148473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18972887985444208801531297 14229665989083156601148473)
    ·
      refine ⟨10672249491812367450861355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14229665989083156601148473 10672249491812367450861355)
      ·
        refine ⟨16008374237718551176292033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672249491812367450861355 16008374237718551176292033)
        ·
          refine ⟨12006280678288913382219025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16008374237718551176292033 12006280678288913382219025)
          ·
            refine ⟨9004710508716685036664269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12006280678288913382219025 9004710508716685036664269)
            ·
              refine ⟨3376766440768756888749101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9004710508716685036664269 3376766440768756888749101)
              ·
                refine ⟨1266287415288283833280913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3376766440768756888749101 1266287415288283833280913)
                ·
                  refine ⟨949715561466212874960685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1266287415288283833280913 949715561466212874960685)
                  ·
                    refine ⟨356143335549829828110257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949715561466212874960685 356143335549829828110257)
                    ·
                      rfl

theorem cell22_1040380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_1040380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040380 prefixEnd_1040380 := by exact prefixLift 1040380
  have htrace : WordTrace (prefixWord ++ tailWord_1040380) baseStart_1040380 baseEnd_1040380 := by
    simpa [prefixWord, tailWord_1040380, baseEnd_1040380] using wordTrace_append hprefix tailTrace_1040380
  have hstable : (prefixWord ++ tailWord_1040380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040380).length < 2 ^ (prefixWord ++ tailWord_1040380).sum := by decide
  have hdescent : baseEnd_1040380 < baseStart_1040380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040483 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 6]
def baseStart_1040483 : Nat := 118140960795 + 1040483 * 2 ^ 59
def prefixEnd_1040483 : Nat := 4983230072969 + 3 ^ 40 * 1040483 * 2
def baseEnd_1040483 : Nat := 118726198184923964261647

theorem tailTrace_1040483 : CollatzResearch.WordTrace tailWord_1040483 prefixEnd_1040483 118726198184923964261647 := by
  unfold tailWord_1040483
  simp only [CollatzResearch.WordTrace]
  refine ⟨37949532689515266194062103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25299688459676844129374735 37949532689515266194062103)
  ·
    refine ⟨56924299034272899291093155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37949532689515266194062103 56924299034272899291093155)
    ·
      refine ⟨85386448551409348936639733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56924299034272899291093155 85386448551409348936639733)
      ·
        refine ⟨8004979551694626462809975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85386448551409348936639733 8004979551694626462809975)
        ·
          refine ⟨12007469327541939694214963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8004979551694626462809975 12007469327541939694214963)
          ·
            refine ⟨18011203991312909541322445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12007469327541939694214963 18011203991312909541322445)
            ·
              refine ⟨6754201496742341077995917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18011203991312909541322445 6754201496742341077995917)
              ·
                refine ⟨2532825561278377904248469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6754201496742341077995917 2532825561278377904248469)
                ·
                  refine ⟨118726198184923964261647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2532825561278377904248469 118726198184923964261647)
                  ·
                    rfl

theorem cell22_1040483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 6].length) (baseStart_1040483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040483 prefixEnd_1040483 := by exact prefixLift 1040483
  have htrace : WordTrace (prefixWord ++ tailWord_1040483) baseStart_1040483 baseEnd_1040483 := by
    simpa [prefixWord, tailWord_1040483, baseEnd_1040483] using wordTrace_append hprefix tailTrace_1040483
  have hstable : (prefixWord ++ tailWord_1040483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040483).length < 2 ^ (prefixWord ++ tailWord_1040483).sum := by decide
  have hdescent : baseEnd_1040483 < baseStart_1040483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040502 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1040502 : Nat := 118140960795 + 1040502 * 2 ^ 59
def prefixEnd_1040502 : Nat := 4983230072969 + 3 ^ 40 * 1040502 * 2
def baseEnd_1040502 : Nat := 356185098643062176559883

theorem tailTrace_1040502 : CollatzResearch.WordTrace tailWord_1040502 prefixEnd_1040502 356185098643062176559883 := by
  unfold tailWord_1040502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2371889104777902027437735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25300150450964288292669173 2371889104777902027437735)
  ·
    refine ⟨3557833657166853041156603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2371889104777902027437735 3557833657166853041156603)
    ·
      refine ⟨5336750485750279561734905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3557833657166853041156603 5336750485750279561734905)
      ·
        refine ⟨4002562864312709671301179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5336750485750279561734905 4002562864312709671301179)
        ·
          refine ⟨6003844296469064506951769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002562864312709671301179 6003844296469064506951769)
          ·
            refine ⟨4502883222351798380213827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6003844296469064506951769 4502883222351798380213827)
            ·
              refine ⟨6754324833527697570320741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502883222351798380213827 6754324833527697570320741)
              ·
                refine ⟨1266435906286443294435139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6754324833527697570320741 1266435906286443294435139)
                ·
                  refine ⟨1899653859429664941652709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266435906286443294435139 1899653859429664941652709)
                  ·
                    refine ⟨356185098643062176559883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1899653859429664941652709 356185098643062176559883)
                    ·
                      rfl

theorem cell22_1040502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1040502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040502 prefixEnd_1040502 := by exact prefixLift 1040502
  have htrace : WordTrace (prefixWord ++ tailWord_1040502) baseStart_1040502 baseEnd_1040502 := by
    simpa [prefixWord, tailWord_1040502, baseEnd_1040502] using wordTrace_append hprefix tailTrace_1040502
  have hstable : (prefixWord ++ tailWord_1040502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040502).length < 2 ^ (prefixWord ++ tailWord_1040502).sum := by decide
  have hdescent : baseEnd_1040502 < baseStart_1040502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040515 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 4, 3]
def baseStart_1040515 : Nat := 118140960795 + 1040515 * 2 ^ 59
def prefixEnd_1040515 : Nat := 4983230072969 + 3 ^ 40 * 1040515 * 2
def baseEnd_1040515 : Nat := 356189548808734475984843

theorem tailTrace_1040515 : CollatzResearch.WordTrace tailWord_1040515 prefixEnd_1040515 356189548808734475984843 := by
  unfold tailWord_1040515
  simp only [CollatzResearch.WordTrace]
  refine ⟨37950699825399335659226999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25300466550266223772817999 37950699825399335659226999)
  ·
    refine ⟨56926049738099003488840499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37950699825399335659226999 56926049738099003488840499)
    ·
      refine ⟨85389074607148505233260749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56926049738099003488840499 85389074607148505233260749)
      ·
        refine ⟨32020902977680689462472781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85389074607148505233260749 32020902977680689462472781)
        ·
          refine ⟨12007838616630258548427293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32020902977680689462472781 12007838616630258548427293)
          ·
            refine ⟨4502939481236346955660235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12007838616630258548427293 4502939481236346955660235)
            ·
              refine ⟨6754409221854520433490353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502939481236346955660235 6754409221854520433490353)
              ·
                refine ⟨5065806916390890325117765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754409221854520433490353 5065806916390890325117765)
                ·
                  refine ⟨949838796823291935959581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5065806916390890325117765 949838796823291935959581)
                  ·
                    refine ⟨356189548808734475984843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949838796823291935959581 356189548808734475984843)
                    ·
                      rfl

theorem cell22_1040515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 3].length) (baseStart_1040515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040515 prefixEnd_1040515 := by exact prefixLift 1040515
  have htrace : WordTrace (prefixWord ++ tailWord_1040515) baseStart_1040515 baseEnd_1040515 := by
    simpa [prefixWord, tailWord_1040515, baseEnd_1040515] using wordTrace_append hprefix tailTrace_1040515
  have hstable : (prefixWord ++ tailWord_1040515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040515).length < 2 ^ (prefixWord ++ tailWord_1040515).sum := by decide
  have hdescent : baseEnd_1040515 < baseStart_1040515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040517 : List Nat := [1, 3, 1, 1, 5, 1, 3, 3, 4]
def baseStart_1040517 : Nat := 118140960795 + 1040517 * 2 ^ 59
def prefixEnd_1040517 : Nat := 4983230072969 + 3 ^ 40 * 1040517 * 2
def baseEnd_1040517 : Nat := 118730077816535712478279

theorem tailTrace_1040517 : CollatzResearch.WordTrace tailWord_1040517 prefixEnd_1040517 118730077816535712478279 := by
  unfold tailWord_1040517
  simp only [CollatzResearch.WordTrace]
  refine ⟨37950772771392090000799805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25300515180928060000533203 37950772771392090000799805)
  ·
    refine ⟨14231539789272033750299927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37950772771392090000799805 14231539789272033750299927)
    ·
      refine ⟨21347309683908050625449891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14231539789272033750299927 21347309683908050625449891)
      ·
        refine ⟨32020964525862075938174837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21347309683908050625449891 32020964525862075938174837)
        ·
          refine ⟨3001965424299569619203891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32020964525862075938174837 3001965424299569619203891)
          ·
            refine ⟨4502948136449354428805837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001965424299569619203891 4502948136449354428805837)
            ·
              refine ⟨1688605551168507910802189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4502948136449354428805837 1688605551168507910802189)
              ·
                refine ⟨633227081688190466550821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1688605551168507910802189 633227081688190466550821)
                ·
                  refine ⟨118730077816535712478279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633227081688190466550821 118730077816535712478279)
                  ·
                    rfl

theorem cell22_1040517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_1040517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040517 prefixEnd_1040517 := by exact prefixLift 1040517
  have htrace : WordTrace (prefixWord ++ tailWord_1040517) baseStart_1040517 baseEnd_1040517 := by
    simpa [prefixWord, tailWord_1040517, baseEnd_1040517] using wordTrace_append hprefix tailTrace_1040517
  have hstable : (prefixWord ++ tailWord_1040517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040517).length < 2 ^ (prefixWord ++ tailWord_1040517).sum := by decide
  have hdescent : baseEnd_1040517 < baseStart_1040517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040545 : List Nat := [1, 2, 3, 3, 1, 3, 2, 7]
def baseStart_1040545 : Nat := 118140960795 + 1040545 * 2 ^ 59
def prefixEnd_1040545 : Nat := 4983230072969 + 3 ^ 40 * 1040545 * 2
def baseEnd_1040545 : Nat := 39577757602424933081639

theorem tailTrace_1040545 : CollatzResearch.WordTrace tailWord_1040545 prefixEnd_1040545 39577757602424933081639 := by
  unfold tailWord_1040545
  simp only [CollatzResearch.WordTrace]
  refine ⟨37951794015290650782819089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25301196010193767188546059 37951794015290650782819089)
  ·
    refine ⟨28463845511467988087114317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37951794015290650782819089 28463845511467988087114317)
    ·
      refine ⟨10673942066800495532667869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28463845511467988087114317 10673942066800495532667869)
      ·
        refine ⟨4002728275050185824750451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10673942066800495532667869 4002728275050185824750451)
        ·
          refine ⟨6004092412575278737125677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002728275050185824750451 6004092412575278737125677)
          ·
            refine ⟨2251534654715729526422129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6004092412575278737125677 2251534654715729526422129)
            ·
              refine ⟨1688650991036797144816597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251534654715729526422129 1688650991036797144816597)
              ·
                refine ⟨39577757602424933081639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1688650991036797144816597 39577757602424933081639)
                ·
                  rfl

theorem cell22_1040545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 7].length) (baseStart_1040545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040545 prefixEnd_1040545 := by exact prefixLift 1040545
  have htrace : WordTrace (prefixWord ++ tailWord_1040545) baseStart_1040545 baseEnd_1040545 := by
    simpa [prefixWord, tailWord_1040545, baseEnd_1040545] using wordTrace_append hprefix tailTrace_1040545
  have hstable : (prefixWord ++ tailWord_1040545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040545).length < 2 ^ (prefixWord ++ tailWord_1040545).sum := by decide
  have hdescent : baseEnd_1040545 < baseStart_1040545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040603 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 2, 8]
def baseStart_1040603 : Nat := 118140960795 + 1040603 * 2 ^ 59
def prefixEnd_1040603 : Nat := 4983230072969 + 3 ^ 40 * 1040603 * 2
def baseEnd_1040603 : Nat := 356219673007131579784573

theorem tailTrace_1040603 : CollatzResearch.WordTrace tailWord_1040603 prefixEnd_1040603 356219673007131579784573 := by
  unfold tailWord_1040603
  simp only [CollatzResearch.WordTrace]
  refine ⟨37953909449080526688430463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25302606299387017792286975 37953909449080526688430463)
  ·
    refine ⟨56930864173620790032645695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37953909449080526688430463 56930864173620790032645695)
    ·
      refine ⟨85396296260431185048968543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56930864173620790032645695 85396296260431185048968543)
      ·
        refine ⟨128094444390646777573452815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85396296260431185048968543 128094444390646777573452815)
        ·
          refine ⟨192141666585970166360179223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128094444390646777573452815 192141666585970166360179223)
          ·
            refine ⟨288212499878955249540268835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192141666585970166360179223 288212499878955249540268835)
            ·
              refine ⟨432318749818432874310403253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288212499878955249540268835 432318749818432874310403253)
              ·
                refine ⟨40529882795478081966600305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432318749818432874310403253 40529882795478081966600305)
                ·
                  refine ⟨30397412096608561474950229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40529882795478081966600305 30397412096608561474950229)
                  ·
                    refine ⟨356219673007131579784573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30397412096608561474950229 356219673007131579784573)
                    ·
                      rfl

theorem cell22_1040603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_1040603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040603 prefixEnd_1040603 := by exact prefixLift 1040603
  have htrace : WordTrace (prefixWord ++ tailWord_1040603) baseStart_1040603 baseEnd_1040603 := by
    simpa [prefixWord, tailWord_1040603, baseEnd_1040603] using wordTrace_append hprefix tailTrace_1040603
  have hstable : (prefixWord ++ tailWord_1040603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040603).length < 2 ^ (prefixWord ++ tailWord_1040603).sum := by decide
  have hdescent : baseEnd_1040603 < baseStart_1040603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040620 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_1040620 : Nat := 118140960795 + 1040620 * 2 ^ 59
def prefixEnd_1040620 : Nat := 4983230072969 + 3 ^ 40 * 1040620 * 2
def baseEnd_1040620 : Nat := 356225492454549202109521

theorem tailTrace_1040620 : CollatzResearch.WordTrace tailWord_1040620 prefixEnd_1040620 356225492454549202109521 := by
  unfold tailWord_1040620
  simp only [CollatzResearch.WordTrace]
  refine ⟨18977264745009469295899657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25303019660012625727866209 18977264745009469295899657)
  ·
    refine ⟨14232948558757101971924743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18977264745009469295899657 14232948558757101971924743)
    ·
      refine ⟨21349422838135652957887115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14232948558757101971924743 21349422838135652957887115)
      ·
        refine ⟨32024134257203479436830673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21349422838135652957887115 32024134257203479436830673)
        ·
          refine ⟨24018100692902609577623005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32024134257203479436830673 24018100692902609577623005)
          ·
            refine ⟨9006787759838478591608627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24018100692902609577623005 9006787759838478591608627)
            ·
              refine ⟨13510181639757717887412941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9006787759838478591608627 13510181639757717887412941)
              ·
                refine ⟨5066318114909144207779853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13510181639757717887412941 5066318114909144207779853)
                ·
                  refine ⟨1899869293090929077917445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5066318114909144207779853 1899869293090929077917445)
                  ·
                    refine ⟨356225492454549202109521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1899869293090929077917445 356225492454549202109521)
                    ·
                      rfl

theorem cell22_1040620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_1040620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040620 prefixEnd_1040620 := by exact prefixLift 1040620
  have htrace : WordTrace (prefixWord ++ tailWord_1040620) baseStart_1040620 baseEnd_1040620 := by
    simpa [prefixWord, tailWord_1040620, baseEnd_1040620] using wordTrace_append hprefix tailTrace_1040620
  have hstable : (prefixWord ++ tailWord_1040620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040620).length < 2 ^ (prefixWord ++ tailWord_1040620).sum := by decide
  have hdescent : baseEnd_1040620 < baseStart_1040620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040650 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1040650 : Nat := 118140960795 + 1040650 * 2 ^ 59
def prefixEnd_1040650 : Nat := 4983230072969 + 3 ^ 40 * 1040650 * 2
def baseEnd_1040650 : Nat := 356235762067639123859429

theorem tailTrace_1040650 : CollatzResearch.WordTrace tailWord_1040650 prefixEnd_1040650 356235762067639123859429 := by
  unfold tailWord_1040650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488905919977563428847851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25303749119940169143594269 9488905919977563428847851)
  ·
    refine ⟨14233358879966345143271777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9488905919977563428847851 14233358879966345143271777)
    ·
      refine ⟨10675019159974758857453833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14233358879966345143271777 10675019159974758857453833)
      ·
        refine ⟨8006264369981069143090375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10675019159974758857453833 8006264369981069143090375)
        ·
          refine ⟨12009396554971603714635563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006264369981069143090375 12009396554971603714635563)
          ·
            refine ⟨18014094832457405571953345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009396554971603714635563 18014094832457405571953345)
            ·
              refine ⟨13510571124343054178965009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18014094832457405571953345 13510571124343054178965009)
              ·
                refine ⟨10132928343257290634223757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13510571124343054178965009 10132928343257290634223757)
                ·
                  refine ⟨3799848128721483987833909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10132928343257290634223757 3799848128721483987833909)
                  ·
                    refine ⟨356235762067639123859429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3799848128721483987833909 356235762067639123859429)
                    ·
                      rfl

theorem cell22_1040650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1040650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040650 prefixEnd_1040650 := by exact prefixLift 1040650
  have htrace : WordTrace (prefixWord ++ tailWord_1040650) baseStart_1040650 baseEnd_1040650 := by
    simpa [prefixWord, tailWord_1040650, baseEnd_1040650] using wordTrace_append hprefix tailTrace_1040650
  have hstable : (prefixWord ++ tailWord_1040650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040650).length < 2 ^ (prefixWord ++ tailWord_1040650).sum := by decide
  have hdescent : baseEnd_1040650 < baseStart_1040650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040652 : List Nat := [2, 2, 1, 2, 2, 2, 1, 6, 4]
def baseStart_1040652 : Nat := 118140960795 + 1040652 * 2 ^ 59
def prefixEnd_1040652 : Nat := 4983230072969 + 3 ^ 40 * 1040652 * 2
def baseEnd_1040652 : Nat := 118745482236170595103141

theorem tailTrace_1040652 : CollatzResearch.WordTrace tailWord_1040652 prefixEnd_1040652 118745482236170595103141 := by
  unfold tailWord_1040652
  simp only [CollatzResearch.WordTrace]
  refine ⟨18977848312951504028482105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25303797750602005371309473 18977848312951504028482105)
  ·
    refine ⟨14233386234713628021361579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18977848312951504028482105 14233386234713628021361579)
    ·
      refine ⟨21350079352070442032042369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14233386234713628021361579 21350079352070442032042369)
      ·
        refine ⟨16012559514052831524031777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21350079352070442032042369 16012559514052831524031777)
        ·
          refine ⟨12009419635539623643023833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16012559514052831524031777 12009419635539623643023833)
          ·
            refine ⟨9007064726654717732267875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12009419635539623643023833 9007064726654717732267875)
            ·
              refine ⟨13510597089982076598401813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007064726654717732267875 13510597089982076598401813)
              ·
                refine ⟨633309238592909840550085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13510597089982076598401813 633309238592909840550085)
                ·
                  refine ⟨118745482236170595103141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633309238592909840550085 118745482236170595103141)
                  ·
                    rfl

theorem cell22_1040652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_1040652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040652 prefixEnd_1040652 := by exact prefixLift 1040652
  have htrace : WordTrace (prefixWord ++ tailWord_1040652) baseStart_1040652 baseEnd_1040652 := by
    simpa [prefixWord, tailWord_1040652, baseEnd_1040652] using wordTrace_append hprefix tailTrace_1040652
  have hstable : (prefixWord ++ tailWord_1040652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040652).length < 2 ^ (prefixWord ++ tailWord_1040652).sum := by decide
  have hdescent : baseEnd_1040652 < baseStart_1040652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040667 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 2, 3]
def baseStart_1040667 : Nat := 118140960795 + 1040667 * 2 ^ 59
def prefixEnd_1040667 : Nat := 4983230072969 + 3 ^ 40 * 1040667 * 2
def baseEnd_1040667 : Nat := 356241581515056746184377

theorem tailTrace_1040667 : CollatzResearch.WordTrace tailWord_1040667 prefixEnd_1040667 356241581515056746184377 := by
  unfold tailWord_1040667
  simp only [CollatzResearch.WordTrace]
  refine ⟨37956243720848665618760255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25304162480565777079173503 37956243720848665618760255)
  ·
    refine ⟨56934365581272998428140383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37956243720848665618760255 56934365581272998428140383)
    ·
      refine ⟨85401548371909497642210575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56934365581272998428140383 85401548371909497642210575)
      ·
        refine ⟨128102322557864246463315863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85401548371909497642210575 128102322557864246463315863)
        ·
          refine ⟨192153483836796369694973795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128102322557864246463315863 192153483836796369694973795)
          ·
            refine ⟨288230225755194554542460693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192153483836796369694973795 288230225755194554542460693)
            ·
              refine ⟨13510791832274744744177845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288230225755194554542460693 13510791832274744744177845)
              ·
                refine ⟨1266636734275757319766673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13510791832274744744177845 1266636734275757319766673)
                ·
                  refine ⟨949977550706817989825005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1266636734275757319766673 949977550706817989825005)
                  ·
                    refine ⟨356241581515056746184377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 949977550706817989825005 356241581515056746184377)
                    ·
                      rfl

theorem cell22_1040667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 3].length) (baseStart_1040667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040667 prefixEnd_1040667 := by exact prefixLift 1040667
  have htrace : WordTrace (prefixWord ++ tailWord_1040667) baseStart_1040667 baseEnd_1040667 := by
    simpa [prefixWord, tailWord_1040667, baseEnd_1040667] using wordTrace_append hprefix tailTrace_1040667
  have hstable : (prefixWord ++ tailWord_1040667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040667).length < 2 ^ (prefixWord ++ tailWord_1040667).sum := by decide
  have hdescent : baseEnd_1040667 < baseStart_1040667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040697 : List Nat := [1, 2, 1, 6, 1, 3, 8]
def baseStart_1040697 : Nat := 118140960795 + 1040697 * 2 ^ 59
def prefixEnd_1040697 : Nat := 4983230072969 + 3 ^ 40 * 1040697 * 2
def baseEnd_1040697 : Nat := 13194513004746172886455

theorem tailTrace_1040697 : CollatzResearch.WordTrace tailWord_1040697 prefixEnd_1040697 13194513004746172886455 := by
  unfold tailWord_1040697
  simp only [CollatzResearch.WordTrace]
  refine ⟨37957337910739980742352345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25304891940493320494901563 37957337910739980742352345)
  ·
    refine ⟨28468003433054985556764259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37957337910739980742352345 28468003433054985556764259)
    ·
      refine ⟨42702005149582478335146389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28468003433054985556764259 42702005149582478335146389)
      ·
        refine ⟨2001656491386678671959987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42702005149582478335146389 2001656491386678671959987)
        ·
          refine ⟨3002484737080018007939981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001656491386678671959987 3002484737080018007939981)
          ·
            refine ⟨1125931776405006752977493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3002484737080018007939981 1125931776405006752977493)
            ·
              refine ⟨13194513004746172886455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1125931776405006752977493 13194513004746172886455)
              ·
                rfl

theorem cell22_1040697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 8].length) (baseStart_1040697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040697 prefixEnd_1040697 := by exact prefixLift 1040697
  have htrace : WordTrace (prefixWord ++ tailWord_1040697) baseStart_1040697 baseEnd_1040697 := by
    simpa [prefixWord, tailWord_1040697, baseEnd_1040697] using wordTrace_append hprefix tailTrace_1040697
  have hstable : (prefixWord ++ tailWord_1040697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040697).length < 2 ^ (prefixWord ++ tailWord_1040697).sum := by decide
  have hdescent : baseEnd_1040697 < baseStart_1040697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040763 : List Nat := [1, 1, 1, 1, 1, 9, 2, 2, 1, 3]
def baseStart_1040763 : Nat := 118140960795 + 1040763 * 2 ^ 59
def prefixEnd_1040763 : Nat := 4983230072969 + 3 ^ 40 * 1040763 * 2
def baseEnd_1040763 : Nat := 356274444276944495784083

theorem tailTrace_1040763 : CollatzResearch.WordTrace tailWord_1040763 prefixEnd_1040763 356274444276944495784083 := by
  unfold tailWord_1040763
  simp only [CollatzResearch.WordTrace]
  refine ⟨37959745128500874014254943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25306496752333916009503295 37959745128500874014254943)
  ·
    refine ⟨56939617692751311021382415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37959745128500874014254943 56939617692751311021382415)
    ·
      refine ⟨85409426539126966532073623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56939617692751311021382415 85409426539126966532073623)
      ·
        refine ⟨128114139808690449798110435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85409426539126966532073623 128114139808690449798110435)
        ·
          refine ⟨192171209713035674697165653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128114139808690449798110435 192171209713035674697165653)
          ·
            refine ⟨1126003181912318406428705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 192171209713035674697165653 1126003181912318406428705)
            ·
              refine ⟨844502386434238804821529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126003181912318406428705 844502386434238804821529)
              ·
                refine ⟨633376789825679103616147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844502386434238804821529 633376789825679103616147)
                ·
                  refine ⟨950065184738518655424221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633376789825679103616147 950065184738518655424221)
                  ·
                    refine ⟨356274444276944495784083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950065184738518655424221 356274444276944495784083)
                    ·
                      rfl

theorem cell22_1040763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 3].length) (baseStart_1040763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040763 prefixEnd_1040763 := by exact prefixLift 1040763
  have htrace : WordTrace (prefixWord ++ tailWord_1040763) baseStart_1040763 baseEnd_1040763 := by
    simpa [prefixWord, tailWord_1040763, baseEnd_1040763] using wordTrace_append hprefix tailTrace_1040763
  have hstable : (prefixWord ++ tailWord_1040763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040763).length < 2 ^ (prefixWord ++ tailWord_1040763).sum := by decide
  have hdescent : baseEnd_1040763 < baseStart_1040763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040772 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1040772 : Nat := 118140960795 + 1040772 * 2 ^ 59
def prefixEnd_1040772 : Nat := 4983230072969 + 3 ^ 40 * 1040772 * 2
def baseEnd_1040772 : Nat := 356277525160871472309055

theorem tailTrace_1040772 : CollatzResearch.WordTrace tailWord_1040772 prefixEnd_1040772 356277525160871472309055 := by
  unfold tailWord_1040772
  simp only [CollatzResearch.WordTrace]
  refine ⟨18980036692734134275666285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25306715590312179034221713 18980036692734134275666285)
  ·
    refine ⟨7117513759775300353374857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18980036692734134275666285 7117513759775300353374857)
    ·
      refine ⟨5338135319831475265031143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7117513759775300353374857 5338135319831475265031143)
      ·
        refine ⟨8007202979747212897546715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5338135319831475265031143 8007202979747212897546715)
        ·
          refine ⟨12010804469620819346320073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007202979747212897546715 12010804469620819346320073)
          ·
            refine ⟨9008103352215614509740055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12010804469620819346320073 9008103352215614509740055)
            ·
              refine ⟨13512155028323421764610083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9008103352215614509740055 13512155028323421764610083)
              ·
                refine ⟨20268232542485132646915125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13512155028323421764610083 20268232542485132646915125)
                ·
                  refine ⟨1900146800857981185648293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20268232542485132646915125 1900146800857981185648293)
                  ·
                    refine ⟨356277525160871472309055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1900146800857981185648293 356277525160871472309055)
                    ·
                      rfl

theorem cell22_1040772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1040772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040772 prefixEnd_1040772 := by exact prefixLift 1040772
  have htrace : WordTrace (prefixWord ++ tailWord_1040772) baseStart_1040772 baseEnd_1040772 := by
    simpa [prefixWord, tailWord_1040772, baseEnd_1040772] using wordTrace_append hprefix tailTrace_1040772
  have hstable : (prefixWord ++ tailWord_1040772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040772).length < 2 ^ (prefixWord ++ tailWord_1040772).sum := by decide
  have hdescent : baseEnd_1040772 < baseStart_1040772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040804 : List Nat := [2, 3, 1, 2, 1, 1, 3, 5, 4]
def baseStart_1040804 : Nat := 118140960795 + 1040804 * 2 ^ 59
def prefixEnd_1040804 : Nat := 4983230072969 + 3 ^ 40 * 1040804 * 2
def baseEnd_1040804 : Nat := 118762826471611351836319

theorem tailTrace_1040804 : CollatzResearch.WordTrace tailWord_1040804 prefixEnd_1040804 118762826471611351836319 := by
  unfold tailWord_1040804
  simp only [CollatzResearch.WordTrace]
  refine ⟨18980620260676169008248733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25307493680901558677664977 18980620260676169008248733)
  ·
    refine ⟨7117732597753563378093275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18980620260676169008248733 7117732597753563378093275)
    ·
      refine ⟨10676598896630345067139913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7117732597753563378093275 10676598896630345067139913)
      ·
        refine ⟨8007449172472758800354935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10676598896630345067139913 8007449172472758800354935)
        ·
          refine ⟨12011173758709138200532403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007449172472758800354935 12011173758709138200532403)
          ·
            refine ⟨18016760638063707300798605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12011173758709138200532403 18016760638063707300798605)
            ·
              refine ⟨6756285239273890237799477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18016760638063707300798605 6756285239273890237799477)
              ·
                refine ⟨633401741181927209793701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6756285239273890237799477 633401741181927209793701)
                ·
                  refine ⟨118762826471611351836319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633401741181927209793701 118762826471611351836319)
                  ·
                    rfl

theorem cell22_1040804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_1040804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040804 prefixEnd_1040804 := by exact prefixLift 1040804
  have htrace : WordTrace (prefixWord ++ tailWord_1040804) baseStart_1040804 baseEnd_1040804 := by
    simpa [prefixWord, tailWord_1040804, baseEnd_1040804] using wordTrace_append hprefix tailTrace_1040804
  have hstable : (prefixWord ++ tailWord_1040804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040804).length < 2 ^ (prefixWord ++ tailWord_1040804).sum := by decide
  have hdescent : baseEnd_1040804 < baseStart_1040804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040810 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_1040810 : Nat := 118140960795 + 1040810 * 2 ^ 59
def prefixEnd_1040810 : Nat := 4983230072969 + 3 ^ 40 * 1040810 * 2
def baseEnd_1040810 : Nat := 118763511112484013286313

theorem tailTrace_1040810 : CollatzResearch.WordTrace tailWord_1040810 prefixEnd_1040810 118763511112484013286313 := by
  unfold tailWord_1040810
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490364839832650260303971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25307639572887067360810589 9490364839832650260303971)
  ·
    refine ⟨14235547259748975390455957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9490364839832650260303971 14235547259748975390455957)
    ·
      refine ⟨667291277800733221427623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14235547259748975390455957 667291277800733221427623)
      ·
        refine ⟨1000936916701099832141435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667291277800733221427623 1000936916701099832141435)
        ·
          refine ⟨1501405375051649748212153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000936916701099832141435 1501405375051649748212153)
          ·
            refine ⟨1126054031288737311159115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501405375051649748212153 1126054031288737311159115)
            ·
              refine ⟨1689081046933105966738673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126054031288737311159115 1689081046933105966738673)
              ·
                refine ⟨1266810785199829475054005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689081046933105966738673 1266810785199829475054005)
                ·
                  refine ⟨118763511112484013286313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1266810785199829475054005 118763511112484013286313)
                  ·
                    rfl

theorem cell22_1040810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_1040810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040810 prefixEnd_1040810 := by exact prefixLift 1040810
  have htrace : WordTrace (prefixWord ++ tailWord_1040810) baseStart_1040810 baseEnd_1040810 := by
    simpa [prefixWord, tailWord_1040810, baseEnd_1040810] using wordTrace_append hprefix tailTrace_1040810
  have hstable : (prefixWord ++ tailWord_1040810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040810).length < 2 ^ (prefixWord ++ tailWord_1040810).sum := by decide
  have hdescent : baseEnd_1040810 < baseStart_1040810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040892 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1040892 : Nat := 118140960795 + 1040892 * 2 ^ 59
def prefixEnd_1040892 : Nat := 4983230072969 + 3 ^ 40 * 1040892 * 2
def baseEnd_1040892 : Nat := 356318603613231159308687

theorem tailTrace_1040892 : CollatzResearch.WordTrace tailWord_1040892 prefixEnd_1040892 356318603613231159308687 := by
  unfold tailWord_1040892
  simp only [CollatzResearch.WordTrace]
  refine ⟨18982225072516764522850465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25309633430022352697133953 18982225072516764522850465)
  ·
    refine ⟨14236668804387573392137849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18982225072516764522850465 14236668804387573392137849)
    ·
      refine ⟨10677501603290680044103387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14236668804387573392137849 10677501603290680044103387)
      ·
        refine ⟨16016252404936020066155081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10677501603290680044103387 16016252404936020066155081)
        ·
          refine ⟨12012189303702015049616311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16016252404936020066155081 12012189303702015049616311)
          ·
            refine ⟨18018283955553022574424467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12012189303702015049616311 18018283955553022574424467)
            ·
              refine ⟨27027425933329533861636701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18018283955553022574424467 27027425933329533861636701)
              ·
                refine ⟨10135284724998575198113763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27027425933329533861636701 10135284724998575198113763)
                ·
                  refine ⟨15202927087497862797170645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10135284724998575198113763 15202927087497862797170645)
                  ·
                    refine ⟨356318603613231159308687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15202927087497862797170645 356318603613231159308687)
                    ·
                      rfl

theorem cell22_1040892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1040892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040892 prefixEnd_1040892 := by exact prefixLift 1040892
  have htrace : WordTrace (prefixWord ++ tailWord_1040892) baseStart_1040892 baseEnd_1040892 := by
    simpa [prefixWord, tailWord_1040892, baseEnd_1040892] using wordTrace_append hprefix tailTrace_1040892
  have hstable : (prefixWord ++ tailWord_1040892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040892).length < 2 ^ (prefixWord ++ tailWord_1040892).sum := by decide
  have hdescent : baseEnd_1040892 < baseStart_1040892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040954 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_1040954 : Nat := 118140960795 + 1040954 * 2 ^ 59
def prefixEnd_1040954 : Nat := 4983230072969 + 3 ^ 40 * 1040954 * 2
def baseEnd_1040954 : Nat := 356339827480283664258497

theorem tailTrace_1040954 : CollatzResearch.WordTrace tailWord_1040954 prefixEnd_1040954 356339827480283664258497 := by
  unfold tailWord_1040954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9491677867702228408614479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25311140980539275756305277 9491677867702228408614479)
  ·
    refine ⟨14237516801553342612921719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9491677867702228408614479 14237516801553342612921719)
    ·
      refine ⟨21356275202330013919382579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14237516801553342612921719 21356275202330013919382579)
      ·
        refine ⟨32034412803495020879073869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21356275202330013919382579 32034412803495020879073869)
        ·
          refine ⟨12012904801310632829652701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32034412803495020879073869 12012904801310632829652701)
          ·
            refine ⟨4504839300491487311119763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12012904801310632829652701 4504839300491487311119763)
            ·
              refine ⟨6757258950737230966679645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504839300491487311119763 6757258950737230966679645)
              ·
                refine ⟨2533972106526461612504867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6757258950737230966679645 2533972106526461612504867)
                ·
                  refine ⟨3800958159789692418757301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533972106526461612504867 3800958159789692418757301)
                  ·
                    refine ⟨356339827480283664258497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3800958159789692418757301 356339827480283664258497)
                    ·
                      rfl

theorem cell22_1040954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_1040954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040954 prefixEnd_1040954 := by exact prefixLift 1040954
  have htrace : WordTrace (prefixWord ++ tailWord_1040954) baseStart_1040954 baseEnd_1040954 := by
    simpa [prefixWord, tailWord_1040954, baseEnd_1040954] using wordTrace_append hprefix tailTrace_1040954
  have hstable : (prefixWord ++ tailWord_1040954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040954).length < 2 ^ (prefixWord ++ tailWord_1040954).sum := by decide
  have hdescent : baseEnd_1040954 < baseStart_1040954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040973 : List Nat := [1, 6, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1040973 : Nat := 118140960795 + 1040973 * 2 ^ 59
def prefixEnd_1040973 : Nat := 4983230072969 + 3 ^ 40 * 1040973 * 2
def baseEnd_1040973 : Nat := 118782110522857982677813

theorem tailTrace_1040973 : CollatzResearch.WordTrace tailWord_1040973 prefixEnd_1040973 118782110522857982677813 := by
  unfold tailWord_1040973
  simp only [CollatzResearch.WordTrace]
  refine ⟨37967404457740079879399573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25311602971826719919599715 37967404457740079879399573)
  ·
    refine ⟨1779722083956566244346855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37967404457740079879399573 1779722083956566244346855)
    ·
      refine ⟨2669583125934849366520283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1779722083956566244346855 2669583125934849366520283)
      ·
        refine ⟨4004374688902274049780425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669583125934849366520283 4004374688902274049780425)
        ·
          refine ⟨3003281016676705537335319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4004374688902274049780425 3003281016676705537335319)
          ·
            refine ⟨4504921525015058306002979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003281016676705537335319 4504921525015058306002979)
            ·
              refine ⟨6757382287522587459004469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504921525015058306002979 6757382287522587459004469)
              ·
                refine ⟨633504589455242574281669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6757382287522587459004469 633504589455242574281669)
                ·
                  refine ⟨118782110522857982677813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633504589455242574281669 118782110522857982677813)
                  ·
                    rfl

theorem cell22_1040973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1040973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040973 prefixEnd_1040973 := by exact prefixLift 1040973
  have htrace : WordTrace (prefixWord ++ tailWord_1040973) baseStart_1040973 baseEnd_1040973 := by
    simpa [prefixWord, tailWord_1040973, baseEnd_1040973] using wordTrace_append hprefix tailTrace_1040973
  have hstable : (prefixWord ++ tailWord_1040973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040973).length < 2 ^ (prefixWord ++ tailWord_1040973).sum := by decide
  have hdescent : baseEnd_1040973 < baseStart_1040973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040988 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1040988 : Nat := 118140960795 + 1040988 * 2 ^ 59
def prefixEnd_1040988 : Nat := 4983230072969 + 3 ^ 40 * 1040988 * 2
def baseEnd_1040988 : Nat := 356351466375118908908393

theorem tailTrace_1040988 : CollatzResearch.WordTrace tailWord_1040988 prefixEnd_1040988 356351466375118908908393 := by
  unfold tailWord_1040988
  simp only [CollatzResearch.WordTrace]
  refine ⟨18983975776342868720597809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25311967701790491627463745 18983975776342868720597809)
  ·
    refine ⟨14237981832257151540448357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18983975776342868720597809 14237981832257151540448357)
    ·
      refine ⟨2669621593548215913834067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14237981832257151540448357 2669621593548215913834067)
      ·
        refine ⟨4004432390322323870751101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669621593548215913834067 4004432390322323870751101)
        ·
          refine ⟨1501662146370871451531663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4004432390322323870751101 1501662146370871451531663)
          ·
            refine ⟨2252493219556307177297495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501662146370871451531663 2252493219556307177297495)
            ·
              refine ⟨3378739829334460765946243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252493219556307177297495 3378739829334460765946243)
              ·
                refine ⟨5068109744001691148919365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378739829334460765946243 5068109744001691148919365)
                ·
                  refine ⟨950270577000317090422381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5068109744001691148919365 950270577000317090422381)
                  ·
                    refine ⟨356351466375118908908393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950270577000317090422381 356351466375118908908393)
                    ·
                      rfl

theorem cell22_1040988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1040988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1040988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1040988 prefixEnd_1040988 := by exact prefixLift 1040988
  have htrace : WordTrace (prefixWord ++ tailWord_1040988) baseStart_1040988 baseEnd_1040988 := by
    simpa [prefixWord, tailWord_1040988, baseEnd_1040988] using wordTrace_append hprefix tailTrace_1040988
  have hstable : (prefixWord ++ tailWord_1040988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040988).length < 2 ^ (prefixWord ++ tailWord_1040988).sum := by decide
  have hdescent : baseEnd_1040988 < baseStart_1040988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041005 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_1041005 : Nat := 118140960795 + 1041005 * 2 ^ 59
def prefixEnd_1041005 : Nat := 4983230072969 + 3 ^ 40 * 1041005 * 2
def baseEnd_1041005 : Nat := 356357285822536531233341

theorem tailTrace_1041005 : CollatzResearch.WordTrace tailWord_1041005 prefixEnd_1041005 356357285822536531233341 := by
  unfold tailWord_1041005
  simp only [CollatzResearch.WordTrace]
  refine ⟨37968571593624149344564469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25312381062416099563042979 37968571593624149344564469)
  ·
    refine ⟨3559553586902264001052919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37968571593624149344564469 3559553586902264001052919)
    ·
      refine ⟨5339330380353396001579379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3559553586902264001052919 5339330380353396001579379)
      ·
        refine ⟨8008995570530094002369069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339330380353396001579379 8008995570530094002369069)
        ·
          refine ⟨3003373338948785250888401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8008995570530094002369069 3003373338948785250888401)
          ·
            refine ⟨2252530004211588938166301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3003373338948785250888401 2252530004211588938166301)
            ·
              refine ⟨844698751579345851812363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2252530004211588938166301 844698751579345851812363)
              ·
                refine ⟨1267048127369018777718545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844698751579345851812363 1267048127369018777718545)
                ·
                  refine ⟨950286095526764083288909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1267048127369018777718545 950286095526764083288909)
                  ·
                    refine ⟨356357285822536531233341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950286095526764083288909 356357285822536531233341)
                    ·
                      rfl

theorem cell22_1041005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_1041005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041005 prefixEnd_1041005 := by exact prefixLift 1041005
  have htrace : WordTrace (prefixWord ++ tailWord_1041005) baseStart_1041005 baseEnd_1041005 := by
    simpa [prefixWord, tailWord_1041005, baseEnd_1041005] using wordTrace_append hprefix tailTrace_1041005
  have hstable : (prefixWord ++ tailWord_1041005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041005).length < 2 ^ (prefixWord ++ tailWord_1041005).sum := by decide
  have hdescent : baseEnd_1041005 < baseStart_1041005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041029 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 7]
def baseStart_1041029 : Nat := 118140960795 + 1041029 * 2 ^ 59
def prefixEnd_1041029 : Nat := 4983230072969 + 3 ^ 40 * 1041029 * 2
def baseEnd_1041029 : Nat := 118788500504336156211089

theorem tailTrace_1041029 : CollatzResearch.WordTrace tailWord_1041029 prefixEnd_1041029 118788500504336156211089 := by
  unfold tailWord_1041029
  simp only [CollatzResearch.WordTrace]
  refine ⟨37969446945537201443438141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25312964630358134295625427 37969446945537201443438141)
  ·
    refine ⟨14238542604576450541289303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37969446945537201443438141 14238542604576450541289303)
    ·
      refine ⟨21357813906864675811933955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14238542604576450541289303 21357813906864675811933955)
      ·
        refine ⟨32036720860297013717900933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21357813906864675811933955 32036720860297013717900933)
        ·
          refine ⟨6006885161305690072106425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32036720860297013717900933 6006885161305690072106425)
          ·
            refine ⟨4505163870979267554079819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6006885161305690072106425 4505163870979267554079819)
            ·
              refine ⟨6757745806468901331119729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505163870979267554079819 6757745806468901331119729)
              ·
                refine ⟨5068309354851675998339797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757745806468901331119729 5068309354851675998339797)
                ·
                  refine ⟨118788500504336156211089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5068309354851675998339797 118788500504336156211089)
                  ·
                    rfl

theorem cell22_1041029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_1041029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041029 prefixEnd_1041029 := by exact prefixLift 1041029
  have htrace : WordTrace (prefixWord ++ tailWord_1041029) baseStart_1041029 baseEnd_1041029 := by
    simpa [prefixWord, tailWord_1041029, baseEnd_1041029] using wordTrace_append hprefix tailTrace_1041029
  have hstable : (prefixWord ++ tailWord_1041029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041029).length < 2 ^ (prefixWord ++ tailWord_1041029).sum := by decide
  have hdescent : baseEnd_1041029 < baseStart_1041029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041074 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_1041074 : Nat := 118140960795 + 1041074 * 2 ^ 59
def prefixEnd_1041074 : Nat := 4983230072969 + 3 ^ 40 * 1041074 * 2
def baseEnd_1041074 : Nat := 118793635310881117086043

theorem tailTrace_1041074 : CollatzResearch.WordTrace tailWord_1041074 prefixEnd_1041074 118793635310881117086043 := by
  unfold tailWord_1041074
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492772057593543532206569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25314058820249449419217517 9492772057593543532206569)
  ·
    refine ⟨7119579043195157649154927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9492772057593543532206569 7119579043195157649154927)
    ·
      refine ⟨10679368564792736473732391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119579043195157649154927 10679368564792736473732391)
      ·
        refine ⟨16019052847189104710598587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10679368564792736473732391 16019052847189104710598587)
        ·
          refine ⟨24028579270783657065897881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16019052847189104710598587 24028579270783657065897881)
          ·
            refine ⟨18021434453087742799423411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24028579270783657065897881 18021434453087742799423411)
            ·
              refine ⟨27032151679631614199135117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18021434453087742799423411 27032151679631614199135117)
              ·
                refine ⟨10137056879861855324675669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27032151679631614199135117 10137056879861855324675669)
                ·
                  refine ⟨118793635310881117086043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10137056879861855324675669 118793635310881117086043)
                  ·
                    rfl

theorem cell22_1041074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_1041074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041074 prefixEnd_1041074 := by exact prefixLift 1041074
  have htrace : WordTrace (prefixWord ++ tailWord_1041074) baseStart_1041074 baseEnd_1041074 := by
    simpa [prefixWord, tailWord_1041074, baseEnd_1041074] using wordTrace_append hprefix tailTrace_1041074
  have hstable : (prefixWord ++ tailWord_1041074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041074).length < 2 ^ (prefixWord ++ tailWord_1041074).sum := by decide
  have hdescent : baseEnd_1041074 < baseStart_1041074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041101 : List Nat := [1, 6, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1041101 : Nat := 118140960795 + 1041101 * 2 ^ 59
def prefixEnd_1041101 : Nat := 4983230072969 + 3 ^ 40 * 1041101 * 2
def baseEnd_1041101 : Nat := 356390148584424280833047

theorem tailTrace_1041101 : CollatzResearch.WordTrace tailWord_1041101 prefixEnd_1041101 356390148584424280833047 := by
  unfold tailWord_1041101
  simp only [CollatzResearch.WordTrace]
  refine ⟨37972073001276357740059157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25314715334184238493372771 37972073001276357740059157)
  ·
    refine ⟨1779940921934829269065273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37972073001276357740059157 1779940921934829269065273)
    ·
      refine ⟨1334955691451121951798955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1779940921934829269065273 1334955691451121951798955)
      ·
        refine ⟨2002433537176682927698433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334955691451121951798955 2002433537176682927698433)
        ·
          refine ⟨1501825152882512195773825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2002433537176682927698433 1501825152882512195773825)
          ·
            refine ⟨1126368864661884146830369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501825152882512195773825 1126368864661884146830369)
            ·
              refine ⟨844776648496413110122777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126368864661884146830369 844776648496413110122777)
              ·
                refine ⟨633582486372309832592083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844776648496413110122777 633582486372309832592083)
                ·
                  refine ⟨950373729558464748888125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633582486372309832592083 950373729558464748888125)
                  ·
                    refine ⟨356390148584424280833047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950373729558464748888125 356390148584424280833047)
                    ·
                      rfl

theorem cell22_1041101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1041101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041101 prefixEnd_1041101 := by exact prefixLift 1041101
  have htrace : WordTrace (prefixWord ++ tailWord_1041101) baseStart_1041101 baseEnd_1041101 := by
    simpa [prefixWord, tailWord_1041101, baseEnd_1041101] using wordTrace_append hprefix tailTrace_1041101
  have hstable : (prefixWord ++ tailWord_1041101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041101).length < 2 ^ (prefixWord ++ tailWord_1041101).sum := by decide
  have hdescent : baseEnd_1041101 < baseStart_1041101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041123 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 1, 5]
def baseStart_1041123 : Nat := 118140960795 + 1041123 * 2 ^ 59
def prefixEnd_1041123 : Nat := 4983230072969 + 3 ^ 40 * 1041123 * 2
def baseEnd_1041123 : Nat := 356397679634023556782979

theorem tailTrace_1041123 : CollatzResearch.WordTrace tailWord_1041123 prefixEnd_1041123 356397679634023556782979 := by
  unfold tailWord_1041123
  simp only [CollatzResearch.WordTrace]
  refine ⟨37972875407196655497360023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25315250271464436998240015 37972875407196655497360023)
  ·
    refine ⟨56959313110794983246040035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37972875407196655497360023 56959313110794983246040035)
    ·
      refine ⟨85438969666192474869060053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56959313110794983246040035 85438969666192474869060053)
      ·
        refine ⟨2002475851551386129743595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 85438969666192474869060053 2002475851551386129743595)
        ·
          refine ⟨3003713777327079194615393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002475851551386129743595 3003713777327079194615393)
          ·
            refine ⟨2252785332995309395961545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3003713777327079194615393 2252785332995309395961545)
            ·
              refine ⟨1689588999746482046971159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2252785332995309395961545 1689588999746482046971159)
              ·
                refine ⟨2534383499619723070456739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689588999746482046971159 2534383499619723070456739)
                ·
                  refine ⟨3801575249429584605685109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534383499619723070456739 3801575249429584605685109)
                  ·
                    refine ⟨356397679634023556782979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3801575249429584605685109 356397679634023556782979)
                    ·
                      rfl

theorem cell22_1041123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 5].length) (baseStart_1041123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041123 prefixEnd_1041123 := by exact prefixLift 1041123
  have htrace : WordTrace (prefixWord ++ tailWord_1041123) baseStart_1041123 baseEnd_1041123 := by
    simpa [prefixWord, tailWord_1041123, baseEnd_1041123] using wordTrace_append hprefix tailTrace_1041123
  have hstable : (prefixWord ++ tailWord_1041123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041123).length < 2 ^ (prefixWord ++ tailWord_1041123).sum := by decide
  have hdescent : baseEnd_1041123 < baseStart_1041123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041136 : List Nat := [2, 1, 1, 1, 3, 1, 7, 6]
def baseStart_1041136 : Nat := 118140960795 + 1041136 * 2 ^ 59
def prefixEnd_1041136 : Nat := 4983230072969 + 3 ^ 40 * 1041136 * 2
def baseEnd_1041136 : Nat := 39600236644410650689771

theorem tailTrace_1041136 : CollatzResearch.WordTrace tailWord_1041136 prefixEnd_1041136 39600236644410650689771 := by
  unfold tailWord_1041136
  simp only [CollatzResearch.WordTrace]
  refine ⟨18986674778074779358791631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25315566370766372478388841 18986674778074779358791631)
  ·
    refine ⟨28480012167112169038187447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18986674778074779358791631 28480012167112169038187447)
    ·
      refine ⟨42720018250668253557281171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28480012167112169038187447 42720018250668253557281171)
      ·
        refine ⟨64080027376002380335921757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42720018250668253557281171 64080027376002380335921757)
        ·
          refine ⟨24030010266000892625970659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64080027376002380335921757 24030010266000892625970659)
          ·
            refine ⟨36045015399001338938955989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24030010266000892625970659 36045015399001338938955989)
            ·
              refine ⟨844805048414093881381781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36045015399001338938955989 844805048414093881381781)
              ·
                refine ⟨39600236644410650689771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 844805048414093881381781 39600236644410650689771)
                ·
                  rfl

theorem cell22_1041136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 6].length) (baseStart_1041136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041136 prefixEnd_1041136 := by exact prefixLift 1041136
  have htrace : WordTrace (prefixWord ++ tailWord_1041136) baseStart_1041136 baseEnd_1041136 := by
    simpa [prefixWord, tailWord_1041136, baseEnd_1041136] using wordTrace_append hprefix tailTrace_1041136
  have hstable : (prefixWord ++ tailWord_1041136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041136).length < 2 ^ (prefixWord ++ tailWord_1041136).sum := by decide
  have hdescent : baseEnd_1041136 < baseStart_1041136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041138 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1041138 : Nat := 118140960795 + 1041138 * 2 ^ 59
def prefixEnd_1041138 : Nat := 4983230072969 + 3 ^ 40 * 1041138 * 2
def baseEnd_1041138 : Nat := 356402814440568517657933

theorem tailTrace_1041138 : CollatzResearch.WordTrace tailWord_1041138 prefixEnd_1041138 356402814440568517657933 := by
  unfold tailWord_1041138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493355625535578264789017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25315615001428208706104045 9493355625535578264789017)
  ·
    refine ⟨7120016719151683698591763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9493355625535578264789017 7120016719151683698591763)
    ·
      refine ⟨10680025078727525547887645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7120016719151683698591763 10680025078727525547887645)
      ·
        refine ⟨4005009404522822080457867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10680025078727525547887645 4005009404522822080457867)
        ·
          refine ⟨6007514106784233120686801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005009404522822080457867 6007514106784233120686801)
          ·
            refine ⟨4505635580088174840515101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6007514106784233120686801 4505635580088174840515101)
            ·
              refine ⟨1689613342533065565193163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4505635580088174840515101 1689613342533065565193163)
              ·
                refine ⟨2534420013799598347789745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689613342533065565193163 2534420013799598347789745)
                ·
                  refine ⟨1900815010349698760842309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534420013799598347789745 1900815010349698760842309)
                  ·
                    refine ⟨356402814440568517657933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1900815010349698760842309 356402814440568517657933)
                    ·
                      rfl

theorem cell22_1041138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1041138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041138 prefixEnd_1041138 := by exact prefixLift 1041138
  have htrace : WordTrace (prefixWord ++ tailWord_1041138) baseStart_1041138 baseEnd_1041138 := by
    simpa [prefixWord, tailWord_1041138, baseEnd_1041138] using wordTrace_append hprefix tailTrace_1041138
  have hstable : (prefixWord ++ tailWord_1041138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041138).length < 2 ^ (prefixWord ++ tailWord_1041138).sum := by decide
  have hdescent : baseEnd_1041138 < baseStart_1041138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041151 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 7, 3]
def baseStart_1041151 : Nat := 118140960795 + 1041151 * 2 ^ 59
def prefixEnd_1041151 : Nat := 4983230072969 + 3 ^ 40 * 1041151 * 2
def baseEnd_1041151 : Nat := 356407264606240817082893

theorem tailTrace_1041151 : CollatzResearch.WordTrace tailWord_1041151 prefixEnd_1041151 356407264606240817082893 := by
  unfold tailWord_1041151
  simp only [CollatzResearch.WordTrace]
  refine ⟨37973896651095216279379307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25315931100730144186252871 37973896651095216279379307)
  ·
    refine ⟨56960844976642824419068961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37973896651095216279379307 56960844976642824419068961)
    ·
      refine ⟨42720633732482118314301721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56960844976642824419068961 42720633732482118314301721)
      ·
        refine ⟨32040475299361588735726291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42720633732482118314301721 32040475299361588735726291)
        ·
          refine ⟨48060712949042383103589437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32040475299361588735726291 48060712949042383103589437)
          ·
            refine ⟨18022767355890893663846039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48060712949042383103589437 18022767355890893663846039)
            ·
              refine ⟨27034151033836340495769059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18022767355890893663846039 27034151033836340495769059)
              ·
                refine ⟨40551226550754510743653589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27034151033836340495769059 40551226550754510743653589)
                ·
                  refine ⟨950419372283308845554381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40551226550754510743653589 950419372283308845554381)
                  ·
                    refine ⟨356407264606240817082893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950419372283308845554381 356407264606240817082893)
                    ·
                      rfl

theorem cell22_1041151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_1041151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041151 prefixEnd_1041151 := by exact prefixLift 1041151
  have htrace : WordTrace (prefixWord ++ tailWord_1041151) baseStart_1041151 baseEnd_1041151 := by
    simpa [prefixWord, tailWord_1041151, baseEnd_1041151] using wordTrace_append hprefix tailTrace_1041151
  have hstable : (prefixWord ++ tailWord_1041151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041151).length < 2 ^ (prefixWord ++ tailWord_1041151).sum := by decide
  have hdescent : baseEnd_1041151 < baseStart_1041151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041198 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_1041198 : Nat := 118140960795 + 1041198 * 2 ^ 59
def prefixEnd_1041198 : Nat := 4983230072969 + 3 ^ 40 * 1041198 * 2
def baseEnd_1041198 : Nat := 118807784555582787052583

theorem tailTrace_1041198 : CollatzResearch.WordTrace tailWord_1041198 prefixEnd_1041198 118807784555582787052583 := by
  unfold tailWord_1041198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746951360240617913292531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25317073921283295537560165 4746951360240617913292531)
  ·
    refine ⟨7120427040360926869938797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4746951360240617913292531 7120427040360926869938797)
    ·
      refine ⟨2670160140135347576227049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7120427040360926869938797 2670160140135347576227049)
      ·
        refine ⟨2002620105101510682170287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2670160140135347576227049 2002620105101510682170287)
        ·
          refine ⟨3003930157652266023255431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002620105101510682170287 3003930157652266023255431)
          ·
            refine ⟨4505895236478399034883147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003930157652266023255431 4505895236478399034883147)
            ·
              refine ⟨6758842854717598552324721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505895236478399034883147 6758842854717598552324721)
              ·
                refine ⟨5069132141038198914243541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6758842854717598552324721 5069132141038198914243541)
                ·
                  refine ⟨118807784555582787052583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5069132141038198914243541 118807784555582787052583)
                  ·
                    rfl

theorem cell22_1041198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_1041198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041198 prefixEnd_1041198 := by exact prefixLift 1041198
  have htrace : WordTrace (prefixWord ++ tailWord_1041198) baseStart_1041198 baseEnd_1041198 := by
    simpa [prefixWord, tailWord_1041198, baseEnd_1041198] using wordTrace_append hprefix tailTrace_1041198
  have hstable : (prefixWord ++ tailWord_1041198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041198).length < 2 ^ (prefixWord ++ tailWord_1041198).sum := by decide
  have hdescent : baseEnd_1041198 < baseStart_1041198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041226 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_1041226 : Nat := 118140960795 + 1041226 * 2 ^ 59
def prefixEnd_1041226 : Nat := 4983230072969 + 3 ^ 40 * 1041226 * 2
def baseEnd_1041226 : Nat := 118810979546321873819221

theorem tailTrace_1041226 : CollatzResearch.WordTrace tailWord_1041226 prefixEnd_1041226 118810979546321873819221 := by
  unfold tailWord_1041226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494158031455876022089883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25317754750549002725573021 9494158031455876022089883)
  ·
    refine ⟨14241237047183814033134825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9494158031455876022089883 14241237047183814033134825)
    ·
      refine ⟨10680927785387860524851119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14241237047183814033134825 10680927785387860524851119)
      ·
        refine ⟨16021391678081790787276679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680927785387860524851119 16021391678081790787276679)
        ·
          refine ⟨24032087517122686180915019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16021391678081790787276679 24032087517122686180915019)
          ·
            refine ⟨36048131275684029271372529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24032087517122686180915019 36048131275684029271372529)
            ·
              refine ⟨27036098456763021953529397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36048131275684029271372529 27036098456763021953529397)
              ·
                refine ⟨2534634230321533308143381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27036098456763021953529397 2534634230321533308143381)
                ·
                  refine ⟨118810979546321873819221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2534634230321533308143381 118810979546321873819221)
                  ·
                    rfl

theorem cell22_1041226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_1041226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041226 prefixEnd_1041226 := by exact prefixLift 1041226
  have htrace : WordTrace (prefixWord ++ tailWord_1041226) baseStart_1041226 baseEnd_1041226 := by
    simpa [prefixWord, tailWord_1041226, baseEnd_1041226] using wordTrace_append hprefix tailTrace_1041226
  have hstable : (prefixWord ++ tailWord_1041226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041226).length < 2 ^ (prefixWord ++ tailWord_1041226).sum := by decide
  have hdescent : baseEnd_1041226 < baseStart_1041226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041273 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_1041273 : Nat := 118140960795 + 1041273 * 2 ^ 59
def prefixEnd_1041273 : Nat := 4983230072969 + 3 ^ 40 * 1041273 * 2
def baseEnd_1041273 : Nat := 356449027699473165532519

theorem tailTrace_1041273 : CollatzResearch.WordTrace tailWord_1041273 prefixEnd_1041273 356449027699473165532519 := by
  unfold tailWord_1041273
  simp only [CollatzResearch.WordTrace]
  refine ⟨37978346356653231115320473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25318897571102154076880315 37978346356653231115320473)
  ·
    refine ⟨28483759767489923336490355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37978346356653231115320473 28483759767489923336490355)
    ·
      refine ⟨42725639651234885004735533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28483759767489923336490355 42725639651234885004735533)
      ·
        refine ⟨16022114869213081876775825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42725639651234885004735533 16022114869213081876775825)
        ·
          refine ⟨12016586151909811407581869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16022114869213081876775825 12016586151909811407581869)
          ·
            refine ⟨4506219806966179277843201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12016586151909811407581869 4506219806966179277843201)
            ·
              refine ⟨3379664855224634458382401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506219806966179277843201 3379664855224634458382401)
              ·
                refine ⟨2534748641418475843786801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379664855224634458382401 2534748641418475843786801)
                ·
                  refine ⟨1901061481063856882840101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534748641418475843786801 1901061481063856882840101)
                  ·
                    refine ⟨356449027699473165532519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901061481063856882840101 356449027699473165532519)
                    ·
                      rfl

theorem cell22_1041273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_1041273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041273 prefixEnd_1041273 := by exact prefixLift 1041273
  have htrace : WordTrace (prefixWord ++ tailWord_1041273) baseStart_1041273 baseEnd_1041273 := by
    simpa [prefixWord, tailWord_1041273, baseEnd_1041273] using wordTrace_append hprefix tailTrace_1041273
  have hstable : (prefixWord ++ tailWord_1041273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041273).length < 2 ^ (prefixWord ++ tailWord_1041273).sum := by decide
  have hdescent : baseEnd_1041273 < baseStart_1041273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041288 : List Nat := [2, 1, 3, 3, 2, 1, 3, 7]
def baseStart_1041288 : Nat := 118140960795 + 1041288 * 2 ^ 59
def prefixEnd_1041288 : Nat := 4983230072969 + 3 ^ 40 * 1041288 * 2
def baseEnd_1041288 : Nat := 39606018056224236267497

theorem tailTrace_1041288 : CollatzResearch.WordTrace tailWord_1041288 prefixEnd_1041288 39606018056224236267497 := by
  unfold tailWord_1041288
  simp only [CollatzResearch.WordTrace]
  refine ⟨18989446725799444338558259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25319262301065925784744345 18989446725799444338558259)
  ·
    refine ⟨28484170088699166507837389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18989446725799444338558259 28484170088699166507837389)
    ·
      refine ⟨10681563783262187440439021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28484170088699166507837389 10681563783262187440439021)
      ·
        refine ⟨4005586418723320290164633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10681563783262187440439021 4005586418723320290164633)
        ·
          refine ⟨3004189814042490217623475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4005586418723320290164633 3004189814042490217623475)
          ·
            refine ⟨4506284721063735326435213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004189814042490217623475 4506284721063735326435213)
            ·
              refine ⟨1689856770398900747413205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4506284721063735326435213 1689856770398900747413205)
              ·
                refine ⟨39606018056224236267497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1689856770398900747413205 39606018056224236267497)
                ·
                  rfl

theorem cell22_1041288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 7].length) (baseStart_1041288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041288 prefixEnd_1041288 := by exact prefixLift 1041288
  have htrace : WordTrace (prefixWord ++ tailWord_1041288) baseStart_1041288 baseEnd_1041288 := by
    simpa [prefixWord, tailWord_1041288, baseEnd_1041288] using wordTrace_append hprefix tailTrace_1041288
  have hstable : (prefixWord ++ tailWord_1041288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041288).length < 2 ^ (prefixWord ++ tailWord_1041288).sum := by decide
  have hdescent : baseEnd_1041288 < baseStart_1041288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041333 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 7]
def baseStart_1041333 : Nat := 118140960795 + 1041333 * 2 ^ 59
def prefixEnd_1041333 : Nat := 4983230072969 + 3 ^ 40 * 1041333 * 2
def baseEnd_1041333 : Nat := 118823188975217669677445

theorem tailTrace_1041333 : CollatzResearch.WordTrace tailWord_1041333 prefixEnd_1041333 118823188975217669677445 := by
  unfold tailWord_1041333
  simp only [CollatzResearch.WordTrace]
  refine ⟨37980534736435861362504653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25320356490957240908336435 37980534736435861362504653)
  ·
    refine ⟨14242700526163448010939245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37980534736435861362504653 14242700526163448010939245)
    ·
      refine ⟨5341012697311293004102217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14242700526163448010939245 5341012697311293004102217)
      ·
        refine ⟨4005759522983469753076663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5341012697311293004102217 4005759522983469753076663)
        ·
          refine ⟨6008639284475204629614995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005759522983469753076663 6008639284475204629614995)
          ·
            refine ⟨9012958926712806944422493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008639284475204629614995 9012958926712806944422493)
            ·
              refine ⟨3379859597517302604158435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9012958926712806944422493 3379859597517302604158435)
              ·
                refine ⟨5069789396275953906237653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379859597517302604158435 5069789396275953906237653)
                ·
                  refine ⟨118823188975217669677445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5069789396275953906237653 118823188975217669677445)
                  ·
                    rfl

theorem cell22_1041333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_1041333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041333 prefixEnd_1041333 := by exact prefixLift 1041333
  have htrace : WordTrace (prefixWord ++ tailWord_1041333) baseStart_1041333 baseEnd_1041333 := by
    simpa [prefixWord, tailWord_1041333, baseEnd_1041333] using wordTrace_append hprefix tailTrace_1041333
  have hstable : (prefixWord ++ tailWord_1041333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041333).length < 2 ^ (prefixWord ++ tailWord_1041333).sum := by decide
  have hdescent : baseEnd_1041333 < baseStart_1041333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041337 : List Nat := [1, 2, 1, 4, 2, 2, 2, 4, 1, 3]
def baseStart_1041337 : Nat := 118140960795 + 1041337 * 2 ^ 59
def prefixEnd_1041337 : Nat := 4983230072969 + 3 ^ 40 * 1041337 * 2
def baseEnd_1041337 : Nat := 356470936207398331932323

theorem tailTrace_1041337 : CollatzResearch.WordTrace tailWord_1041337 prefixEnd_1041337 356470936207398331932323 := by
  unfold tailWord_1041337
  simp only [CollatzResearch.WordTrace]
  refine ⟨37980680628421370045650265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25320453752280913363766843 37980680628421370045650265)
  ·
    refine ⟨28485510471316027534237699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37980680628421370045650265 28485510471316027534237699)
    ·
      refine ⟨42728265706974041301356549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28485510471316027534237699 42728265706974041301356549)
      ·
        refine ⟨8011549820057632744004353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42728265706974041301356549 8011549820057632744004353)
        ·
          refine ⟨6008662365043224558003265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8011549820057632744004353 6008662365043224558003265)
          ·
            refine ⟨4506496773782418418502449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6008662365043224558003265 4506496773782418418502449)
            ·
              refine ⟨3379872580336813813876837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506496773782418418502449 3379872580336813813876837)
              ·
                refine ⟨633726108813152590101907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3379872580336813813876837 633726108813152590101907)
                ·
                  refine ⟨950589163219728885152861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633726108813152590101907 950589163219728885152861)
                  ·
                    refine ⟨356470936207398331932323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950589163219728885152861 356470936207398331932323)
                    ·
                      rfl

theorem cell22_1041337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 3].length) (baseStart_1041337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041337 prefixEnd_1041337 := by exact prefixLift 1041337
  have htrace : WordTrace (prefixWord ++ tailWord_1041337) baseStart_1041337 baseEnd_1041337 := by
    simpa [prefixWord, tailWord_1041337, baseEnd_1041337] using wordTrace_append hprefix tailTrace_1041337
  have hstable : (prefixWord ++ tailWord_1041337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041337).length < 2 ^ (prefixWord ++ tailWord_1041337).sum := by decide
  have hdescent : baseEnd_1041337 < baseStart_1041337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041440 : List Nat := [2, 1, 1, 7, 1, 10]
def baseStart_1041440 : Nat := 118140960795 + 1041440 * 2 ^ 59
def prefixEnd_1041440 : Nat := 4983230072969 + 3 ^ 40 * 1041440 * 2
def baseEnd_1041440 : Nat := 4401311052004202427247

theorem tailTrace_1041440 : CollatzResearch.WordTrace tailWord_1041440 prefixEnd_1041440 4401311052004202427247 := by
  unfold tailWord_1041440
  simp only [CollatzResearch.WordTrace]
  refine ⟨18992218673524109318324887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25322958231365479091099849 18992218673524109318324887)
  ·
    refine ⟨28488328010286163977487331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18992218673524109318324887 28488328010286163977487331)
    ·
      refine ⟨42732492015429245966230997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28488328010286163977487331 42732492015429245966230997)
      ·
        refine ⟨1001542781611622952333539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 42732492015429245966230997 1001542781611622952333539)
        ·
          refine ⟨1502314172417434428500309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001542781611622952333539 1502314172417434428500309)
          ·
            refine ⟨4401311052004202427247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1502314172417434428500309 4401311052004202427247)
            ·
              rfl

theorem cell22_1041440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 10].length) (baseStart_1041440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041440 prefixEnd_1041440 := by exact prefixLift 1041440
  have htrace : WordTrace (prefixWord ++ tailWord_1041440) baseStart_1041440 baseEnd_1041440 := by
    simpa [prefixWord, tailWord_1041440, baseEnd_1041440] using wordTrace_append hprefix tailTrace_1041440
  have hstable : (prefixWord ++ tailWord_1041440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041440).length < 2 ^ (prefixWord ++ tailWord_1041440).sum := by decide
  have hdescent : baseEnd_1041440 < baseStart_1041440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041444 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_1041444 : Nat := 118140960795 + 1041444 * 2 ^ 59
def prefixEnd_1041444 : Nat := 4983230072969 + 3 ^ 40 * 1041444 * 2
def baseEnd_1041444 : Nat := 356507564494085719506995

theorem tailTrace_1041444 : CollatzResearch.WordTrace tailWord_1041444 prefixEnd_1041444 356507564494085719506995 := by
  unfold tailWord_1041444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18992291619516863659897693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25323055492689151546530257 18992291619516863659897693)
  ·
    refine ⟨7122109357318823872461635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18992291619516863659897693 7122109357318823872461635)
    ·
      refine ⟨10683164035978235808692453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122109357318823872461635 10683164035978235808692453)
      ·
        refine ⟨2003093256745919214129835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10683164035978235808692453 2003093256745919214129835)
        ·
          refine ⟨3004639885118878821194753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003093256745919214129835 3004639885118878821194753)
          ·
            refine ⟨2253479913839159115896065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004639885118878821194753 2253479913839159115896065)
            ·
              refine ⟨1690109935379369336922049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253479913839159115896065 1690109935379369336922049)
              ·
                refine ⟨1267582451534527002691537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690109935379369336922049 1267582451534527002691537)
                ·
                  refine ⟨950686838650895252018653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1267582451534527002691537 950686838650895252018653)
                  ·
                    refine ⟨356507564494085719506995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950686838650895252018653 356507564494085719506995)
                    ·
                      rfl

theorem cell22_1041444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_1041444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041444 prefixEnd_1041444 := by exact prefixLift 1041444
  have htrace : WordTrace (prefixWord ++ tailWord_1041444) baseStart_1041444 baseEnd_1041444 := by
    simpa [prefixWord, tailWord_1041444, baseEnd_1041444] using wordTrace_append hprefix tailTrace_1041444
  have hstable : (prefixWord ++ tailWord_1041444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041444).length < 2 ^ (prefixWord ++ tailWord_1041444).sum := by decide
  have hdescent : baseEnd_1041444 < baseStart_1041444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041483 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 6, 5]
def baseStart_1041483 : Nat := 118140960795 + 1041483 * 2 ^ 59
def prefixEnd_1041483 : Nat := 4983230072969 + 3 ^ 40 * 1041483 * 2
def baseEnd_1041483 : Nat := 356520914991102617781875

theorem tailTrace_1041483 : CollatzResearch.WordTrace tailWord_1041483 prefixEnd_1041483 356520914991102617781875 := by
  unfold tailWord_1041483
  simp only [CollatzResearch.WordTrace]
  refine ⟨37986005685892436980465103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25324003790594957986976735 37986005685892436980465103)
  ·
    refine ⟨56979008528838655470697655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37986005685892436980465103 56979008528838655470697655)
    ·
      refine ⟨85468512793257983206046483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56979008528838655470697655 85468512793257983206046483)
      ·
        refine ⟨128202769189886974809069725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85468512793257983206046483 128202769189886974809069725)
        ·
          refine ⟨48076038446207615553401147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128202769189886974809069725 48076038446207615553401147)
          ·
            refine ⟨72114057669311423330101721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48076038446207615553401147 72114057669311423330101721)
            ·
              refine ⟨54085543251983567497576291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72114057669311423330101721 54085543251983567497576291)
              ·
                refine ⟨81128314877975351246364437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54085543251983567497576291 81128314877975351246364437)
                ·
                  refine ⟨3802889759905094589673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81128314877975351246364437 3802889759905094589673333)
                  ·
                    refine ⟨356520914991102617781875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3802889759905094589673333 356520914991102617781875)
                    ·
                      rfl

theorem cell22_1041483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_1041483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041483 prefixEnd_1041483 := by exact prefixLift 1041483
  have htrace : WordTrace (prefixWord ++ tailWord_1041483) baseStart_1041483 baseEnd_1041483 := by
    simpa [prefixWord, tailWord_1041483, baseEnd_1041483] using wordTrace_append hprefix tailTrace_1041483
  have hstable : (prefixWord ++ tailWord_1041483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041483).length < 2 ^ (prefixWord ++ tailWord_1041483).sum := by decide
  have hdescent : baseEnd_1041483 < baseStart_1041483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041500 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1041500 : Nat := 118140960795 + 1041500 * 2 ^ 59
def prefixEnd_1041500 : Nat := 4983230072969 + 3 ^ 40 * 1041500 * 2
def baseEnd_1041500 : Nat := 356526734438520240106823

theorem tailTrace_1041500 : CollatzResearch.WordTrace tailWord_1041500 prefixEnd_1041500 356526734438520240106823 := by
  unfold tailWord_1041500
  simp only [CollatzResearch.WordTrace]
  refine ⟨18993312863415424441916977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25324417151220565922555969 18993312863415424441916977)
  ·
    refine ⟨14244984647561568331437733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18993312863415424441916977 14244984647561568331437733)
    ·
      refine ⟨2670934621417794062144575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14244984647561568331437733 2670934621417794062144575)
      ·
        refine ⟨4006401932126691093216863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670934621417794062144575 4006401932126691093216863)
        ·
          refine ⟨6009602898190036639825295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006401932126691093216863 6009602898190036639825295)
          ·
            refine ⟨9014404347285054959737943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009602898190036639825295 9014404347285054959737943)
            ·
              refine ⟨13521606520927582439606915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014404347285054959737943 13521606520927582439606915)
              ·
                refine ⟨20282409781391373659410373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13521606520927582439606915 20282409781391373659410373)
                ·
                  refine ⟨3802951834010882561139445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20282409781391373659410373 3802951834010882561139445)
                  ·
                    refine ⟨356526734438520240106823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3802951834010882561139445 356526734438520240106823)
                    ·
                      rfl

theorem cell22_1041500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1041500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041500 prefixEnd_1041500 := by exact prefixLift 1041500
  have htrace : WordTrace (prefixWord ++ tailWord_1041500) baseStart_1041500 baseEnd_1041500 := by
    simpa [prefixWord, tailWord_1041500, baseEnd_1041500] using wordTrace_append hprefix tailTrace_1041500
  have hstable : (prefixWord ++ tailWord_1041500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041500).length < 2 ^ (prefixWord ++ tailWord_1041500).sum := by decide
  have hdescent : baseEnd_1041500 < baseStart_1041500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041506 : List Nat := [3, 3, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1041506 : Nat := 118140960795 + 1041506 * 2 ^ 59
def prefixEnd_1041506 : Nat := 4983230072969 + 3 ^ 40 * 1041506 * 2
def baseEnd_1041506 : Nat := 356528788361138224456805

theorem tailTrace_1041506 : CollatzResearch.WordTrace tailWord_1041506 prefixEnd_1041506 356528788361138224456805 := by
  unfold tailWord_1041506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9496711141202277977138093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25324563043206074605701581 9496711141202277977138093)
  ·
    refine ⟨3561266677950854241426785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9496711141202277977138093 3561266677950854241426785)
    ·
      refine ⟨2670950008463140681070089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3561266677950854241426785 2670950008463140681070089)
      ·
        refine ⟨2003212506347355510802567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2670950008463140681070089 2003212506347355510802567)
        ·
          refine ⟨3004818759521033266203851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003212506347355510802567 3004818759521033266203851)
          ·
            refine ⟨4507228139281549899305777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004818759521033266203851 4507228139281549899305777)
            ·
              refine ⟨3380421104461162424479333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4507228139281549899305777 3380421104461162424479333)
              ·
                refine ⟨633828957086467954589875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3380421104461162424479333 633828957086467954589875)
                ·
                  refine ⟨950743435629701931884813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633828957086467954589875 950743435629701931884813)
                  ·
                    refine ⟨356528788361138224456805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950743435629701931884813 356528788361138224456805)
                    ·
                      rfl

theorem cell22_1041506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1041506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041506 prefixEnd_1041506 := by exact prefixLift 1041506
  have htrace : WordTrace (prefixWord ++ tailWord_1041506) baseStart_1041506 baseEnd_1041506 := by
    simpa [prefixWord, tailWord_1041506, baseEnd_1041506] using wordTrace_append hprefix tailTrace_1041506
  have hstable : (prefixWord ++ tailWord_1041506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041506).length < 2 ^ (prefixWord ++ tailWord_1041506).sum := by decide
  have hdescent : baseEnd_1041506 < baseStart_1041506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041532 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_1041532 : Nat := 118140960795 + 1041532 * 2 ^ 59
def prefixEnd_1041532 : Nat := 4983230072969 + 3 ^ 40 * 1041532 * 2
def baseEnd_1041532 : Nat := 356537688692482823306725

theorem tailTrace_1041532 : CollatzResearch.WordTrace tailWord_1041532 prefixEnd_1041532 356537688692482823306725 := by
  unfold tailWord_1041532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18993896431357459174499425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25325195241809945565999233 18993896431357459174499425)
  ·
    refine ⟨14245422323518094380874569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18993896431357459174499425 14245422323518094380874569)
    ·
      refine ⟨10684066742638570785655927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14245422323518094380874569 10684066742638570785655927)
      ·
        refine ⟨16026100113957856178483891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10684066742638570785655927 16026100113957856178483891)
        ·
          refine ⟨24039150170936784267725837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16026100113957856178483891 24039150170936784267725837)
          ·
            refine ⟨9014681314101294100397189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24039150170936784267725837 9014681314101294100397189)
            ·
              refine ⟨1690252746393992643824473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9014681314101294100397189 1690252746393992643824473)
              ·
                refine ⟨1267689559795494482868355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690252746393992643824473 1267689559795494482868355)
                ·
                  refine ⟨1901534339693241724302533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267689559795494482868355 1901534339693241724302533)
                  ·
                    refine ⟨356537688692482823306725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901534339693241724302533 356537688692482823306725)
                    ·
                      rfl

theorem cell22_1041532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_1041532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041532 prefixEnd_1041532 := by exact prefixLift 1041532
  have htrace : WordTrace (prefixWord ++ tailWord_1041532) baseStart_1041532 baseEnd_1041532 := by
    simpa [prefixWord, tailWord_1041532, baseEnd_1041532] using wordTrace_append hprefix tailTrace_1041532
  have hstable : (prefixWord ++ tailWord_1041532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041532).length < 2 ^ (prefixWord ++ tailWord_1041532).sum := by decide
  have hdescent : baseEnd_1041532 < baseStart_1041532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041712 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_1041712 : Nat := 118140960795 + 1041712 * 2 ^ 59
def prefixEnd_1041712 : Nat := 4983230072969 + 3 ^ 40 * 1041712 * 2
def baseEnd_1041712 : Nat := 356599306371022353806173

theorem tailTrace_1041712 : CollatzResearch.WordTrace tailWord_1041712 prefixEnd_1041712 356599306371022353806173 := by
  unfold tailWord_1041712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18997179001031404545275695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25329572001375206060367593 18997179001031404545275695)
  ·
    refine ⟨28495768501547106817913543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18997179001031404545275695 28495768501547106817913543)
    ·
      refine ⟨42743652752320660226870315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28495768501547106817913543 42743652752320660226870315)
      ·
        refine ⟨64115479128480990340305473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42743652752320660226870315 64115479128480990340305473)
        ·
          refine ⟨48086609346360742755229105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64115479128480990340305473 48086609346360742755229105)
          ·
            refine ⟨36064957009770557066421829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48086609346360742755229105 36064957009770557066421829)
            ·
              refine ⟨6762179439331979449954093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36064957009770557066421829 6762179439331979449954093)
              ·
                refine ⟨2535817289749492293732785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6762179439331979449954093 2535817289749492293732785)
                ·
                  refine ⟨1901862967312119220299589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2535817289749492293732785 1901862967312119220299589)
                  ·
                    refine ⟨356599306371022353806173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901862967312119220299589 356599306371022353806173)
                    ·
                      rfl

theorem cell22_1041712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_1041712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041712 prefixEnd_1041712 := by exact prefixLift 1041712
  have htrace : WordTrace (prefixWord ++ tailWord_1041712) baseStart_1041712 baseEnd_1041712 := by
    simpa [prefixWord, tailWord_1041712, baseEnd_1041712] using wordTrace_append hprefix tailTrace_1041712
  have hstable : (prefixWord ++ tailWord_1041712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041712).length < 2 ^ (prefixWord ++ tailWord_1041712).sum := by decide
  have hdescent : baseEnd_1041712 < baseStart_1041712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041714 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_1041714 : Nat := 118140960795 + 1041714 * 2 ^ 59
def prefixEnd_1041714 : Nat := 4983230072969 + 3 ^ 40 * 1041714 * 2
def baseEnd_1041714 : Nat := 356599991011895015256167

theorem tailTrace_1041714 : CollatzResearch.WordTrace tailWord_1041714 prefixEnd_1041714 356599991011895015256167 := by
  unfold tailWord_1041714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498607737013890858031049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25329620632037042288082797 9498607737013890858031049)
  ·
    refine ⟨7123955802760418143523287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9498607737013890858031049 7123955802760418143523287)
    ·
      refine ⟨10685933704140627215284931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7123955802760418143523287 10685933704140627215284931)
      ·
        refine ⟨16028900556210940822927397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10685933704140627215284931 16028900556210940822927397)
        ·
          refine ⟨3005418854289551404298887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16028900556210940822927397 3005418854289551404298887)
          ·
            refine ⟨4508128281434327106448331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005418854289551404298887 4508128281434327106448331)
            ·
              refine ⟨6762192422151490659672497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508128281434327106448331 6762192422151490659672497)
              ·
                refine ⟨5071644316613617994754373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762192422151490659672497 5071644316613617994754373)
                ·
                  refine ⟨950933309365053374016445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5071644316613617994754373 950933309365053374016445)
                  ·
                    refine ⟨356599991011895015256167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950933309365053374016445 356599991011895015256167)
                    ·
                      rfl

theorem cell22_1041714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_1041714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041714 prefixEnd_1041714 := by exact prefixLift 1041714
  have htrace : WordTrace (prefixWord ++ tailWord_1041714) baseStart_1041714 baseEnd_1041714 := by
    simpa [prefixWord, tailWord_1041714, baseEnd_1041714] using wordTrace_append hprefix tailTrace_1041714
  have hstable : (prefixWord ++ tailWord_1041714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041714).length < 2 ^ (prefixWord ++ tailWord_1041714).sum := by decide
  have hdescent : baseEnd_1041714 < baseStart_1041714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041727 : List Nat := [1, 1, 2, 2, 4, 4, 8]
def baseStart_1041727 : Nat := 118140960795 + 1041727 * 2 ^ 59
def prefixEnd_1041727 : Nat := 4983230072969 + 3 ^ 40 * 1041727 * 2
def baseEnd_1041727 : Nat := 13207571895465456099301

theorem tailTrace_1041727 : CollatzResearch.WordTrace tailWord_1041727 prefixEnd_1041727 13207571895465456099301 := by
  unfold tailWord_1041727
  simp only [CollatzResearch.WordTrace]
  refine ⟨37994905097008466652347435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25329936731338977768231623 37994905097008466652347435)
  ·
    refine ⟨56992357645512699978521153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37994905097008466652347435 56992357645512699978521153)
    ·
      refine ⟨42744268234134524983890865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56992357645512699978521153 42744268234134524983890865)
      ·
        refine ⟨32058201175600893737918149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42744268234134524983890865 32058201175600893737918149)
        ·
          refine ⟨6010912720425167575859653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32058201175600893737918149 6010912720425167575859653)
          ·
            refine ⟨1127046135079718920473685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6010912720425167575859653 1127046135079718920473685)
            ·
              refine ⟨13207571895465456099301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1127046135079718920473685 13207571895465456099301)
              ·
                rfl

theorem cell22_1041727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 8].length) (baseStart_1041727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041727 prefixEnd_1041727 := by exact prefixLift 1041727
  have htrace : WordTrace (prefixWord ++ tailWord_1041727) baseStart_1041727 baseEnd_1041727 := by
    simpa [prefixWord, tailWord_1041727, baseEnd_1041727] using wordTrace_append hprefix tailTrace_1041727
  have hstable : (prefixWord ++ tailWord_1041727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041727).length < 2 ^ (prefixWord ++ tailWord_1041727).sum := by decide
  have hdescent : baseEnd_1041727 < baseStart_1041727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041729 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1041729 : Nat := 118140960795 + 1041729 * 2 ^ 59
def prefixEnd_1041729 : Nat := 4983230072969 + 3 ^ 40 * 1041729 * 2
def baseEnd_1041729 : Nat := 356605125818439976131121

theorem tailTrace_1041729 : CollatzResearch.WordTrace tailWord_1041729 prefixEnd_1041729 356605125818439976131121 := by
  unfold tailWord_1041729
  simp only [CollatzResearch.WordTrace]
  refine ⟨37994978043001220993920241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25329985362000813995946827 37994978043001220993920241)
  ·
    refine ⟨28496233532250915745440181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37994978043001220993920241 28496233532250915745440181)
    ·
      refine ⟨2671521893648523351135017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28496233532250915745440181 2671521893648523351135017)
      ·
        refine ⟨2003641420236392513351263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2671521893648523351135017 2003641420236392513351263)
        ·
          refine ⟨3005462130354588770026895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003641420236392513351263 3005462130354588770026895)
          ·
            refine ⟨4508193195531883155040343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005462130354588770026895 4508193195531883155040343)
            ·
              refine ⟨6762289793297824732560515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508193195531883155040343 6762289793297824732560515)
              ·
                refine ⟨10143434689946737098840773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762289793297824732560515 10143434689946737098840773)
                ·
                  refine ⟨1901894004365013206032645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10143434689946737098840773 1901894004365013206032645)
                  ·
                    refine ⟨356605125818439976131121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1901894004365013206032645 356605125818439976131121)
                    ·
                      rfl

theorem cell22_1041729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1041729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041729 prefixEnd_1041729 := by exact prefixLift 1041729
  have htrace : WordTrace (prefixWord ++ tailWord_1041729) baseStart_1041729 baseEnd_1041729 := by
    simpa [prefixWord, tailWord_1041729, baseEnd_1041729] using wordTrace_append hprefix tailTrace_1041729
  have hstable : (prefixWord ++ tailWord_1041729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041729).length < 2 ^ (prefixWord ++ tailWord_1041729).sum := by decide
  have hdescent : baseEnd_1041729 < baseStart_1041729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041776 : List Nat := [2, 1, 1, 1, 4, 2, 2, 5, 1, 3]
def baseStart_1041776 : Nat := 118140960795 + 1041776 * 2 ^ 59
def prefixEnd_1041776 : Nat := 4983230072969 + 3 ^ 40 * 1041776 * 2
def baseEnd_1041776 : Nat := 356621214878947520205977

theorem tailTrace_1041776 : CollatzResearch.WordTrace tailWord_1041776 prefixEnd_1041776 356621214878947520205977 := by
  unfold tailWord_1041776
  simp only [CollatzResearch.WordTrace]
  refine ⟨18998346136915474010440591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25331128182553965347254121 18998346136915474010440591)
  ·
    refine ⟨28497519205373211015660887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18998346136915474010440591 28497519205373211015660887)
    ·
      refine ⟨42746278808059816523491331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28497519205373211015660887 42746278808059816523491331)
      ·
        refine ⟨64119418212089724785236997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42746278808059816523491331 64119418212089724785236997)
        ·
          refine ⟨12022390914766823397231937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64119418212089724785236997 12022390914766823397231937)
          ·
            refine ⟨9016793186075117547923953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12022390914766823397231937 9016793186075117547923953)
            ·
              refine ⟨6762594889556338160942965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9016793186075117547923953 6762594889556338160942965)
              ·
                refine ⟨633993270895906702588403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6762594889556338160942965 633993270895906702588403)
                ·
                  refine ⟨950989906343860053882605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633993270895906702588403 950989906343860053882605)
                  ·
                    refine ⟨356621214878947520205977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 950989906343860053882605 356621214878947520205977)
                    ·
                      rfl

theorem cell22_1041776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 3].length) (baseStart_1041776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041776 prefixEnd_1041776 := by exact prefixLift 1041776
  have htrace : WordTrace (prefixWord ++ tailWord_1041776) baseStart_1041776 baseEnd_1041776 := by
    simpa [prefixWord, tailWord_1041776, baseEnd_1041776] using wordTrace_append hprefix tailTrace_1041776
  have hstable : (prefixWord ++ tailWord_1041776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041776).length < 2 ^ (prefixWord ++ tailWord_1041776).sum := by decide
  have hdescent : baseEnd_1041776 < baseStart_1041776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041787 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 2, 5]
def baseStart_1041787 : Nat := 118140960795 + 1041787 * 2 ^ 59
def prefixEnd_1041787 : Nat := 4983230072969 + 3 ^ 40 * 1041787 * 2
def baseEnd_1041787 : Nat := 356624980403747158180943

theorem tailTrace_1041787 : CollatzResearch.WordTrace tailWord_1041787 prefixEnd_1041787 356624980403747158180943 := by
  unfold tailWord_1041787
  simp only [CollatzResearch.WordTrace]
  refine ⟨37997093476791096899531615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25331395651194064599687743 37997093476791096899531615)
  ·
    refine ⟨56995640215186645349297423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37997093476791096899531615 56995640215186645349297423)
    ·
      refine ⟨85493460322779968023946135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56995640215186645349297423 85493460322779968023946135)
      ·
        refine ⟨128240190484169952035919203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85493460322779968023946135 128240190484169952035919203)
        ·
          refine ⟨192360285726254928053878805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128240190484169952035919203 192360285726254928053878805)
          ·
            refine ⟨9016888393418199752525569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192360285726254928053878805 9016888393418199752525569)
            ·
              refine ⟨6762666295063649814394177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9016888393418199752525569 6762666295063649814394177)
              ·
                refine ⟨5071999721297737360795633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762666295063649814394177 5071999721297737360795633)
                ·
                  refine ⟨3803999790973303020596725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5071999721297737360795633 3803999790973303020596725)
                  ·
                    refine ⟨356624980403747158180943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3803999790973303020596725 356624980403747158180943)
                    ·
                      rfl

theorem cell22_1041787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_1041787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041787 prefixEnd_1041787 := by exact prefixLift 1041787
  have htrace : WordTrace (prefixWord ++ tailWord_1041787) baseStart_1041787 baseEnd_1041787 := by
    simpa [prefixWord, tailWord_1041787, baseEnd_1041787] using wordTrace_append hprefix tailTrace_1041787
  have hstable : (prefixWord ++ tailWord_1041787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041787).length < 2 ^ (prefixWord ++ tailWord_1041787).sum := by decide
  have hdescent : baseEnd_1041787 < baseStart_1041787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041789 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 5]
def baseStart_1041789 : Nat := 118140960795 + 1041789 * 2 ^ 59
def prefixEnd_1041789 : Nat := 4983230072969 + 3 ^ 40 * 1041789 * 2
def baseEnd_1041789 : Nat := 118875221681539939876979

theorem tailTrace_1041789 : CollatzResearch.WordTrace tailWord_1041789 prefixEnd_1041789 118875221681539939876979 := by
  unfold tailWord_1041789
  simp only [CollatzResearch.WordTrace]
  refine ⟨37997166422783851241104421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25331444281855900827402947 37997166422783851241104421)
  ·
    refine ⟨7124468704271972107707079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37997166422783851241104421 7124468704271972107707079)
    ·
      refine ⟨10686703056407958161560619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7124468704271972107707079 10686703056407958161560619)
      ·
        refine ⟨16030054584611937242340929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10686703056407958161560619 16030054584611937242340929)
        ·
          refine ⟨12022540938458952931755697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16030054584611937242340929 12022540938458952931755697)
          ·
            refine ⟨9016905703844214698816773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12022540938458952931755697 9016905703844214698816773)
            ·
              refine ⟨1690669819470790256028145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9016905703844214698816773 1690669819470790256028145)
              ·
                refine ⟨1268002364603092692021109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690669819470790256028145 1268002364603092692021109)
                ·
                  refine ⟨118875221681539939876979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1268002364603092692021109 118875221681539939876979)
                  ·
                    rfl

theorem cell22_1041789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_1041789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041789 prefixEnd_1041789 := by exact prefixLift 1041789
  have htrace : WordTrace (prefixWord ++ tailWord_1041789) baseStart_1041789 baseEnd_1041789 := by
    simpa [prefixWord, tailWord_1041789, baseEnd_1041789] using wordTrace_append hprefix tailTrace_1041789
  have hstable : (prefixWord ++ tailWord_1041789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041789).length < 2 ^ (prefixWord ++ tailWord_1041789).sum := by decide
  have hdescent : baseEnd_1041789 < baseStart_1041789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041817 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 8]
def baseStart_1041817 : Nat := 118140960795 + 1041817 * 2 ^ 59
def prefixEnd_1041817 : Nat := 4983230072969 + 3 ^ 40 * 1041817 * 2
def baseEnd_1041817 : Nat := 118878416672279026643617

theorem tailTrace_1041817 : CollatzResearch.WordTrace tailWord_1041817 prefixEnd_1041817 118878416672279026643617 := by
  unfold tailWord_1041817
  simp only [CollatzResearch.WordTrace]
  refine ⟨37998187666682412023123705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25332125111121608015415803 37998187666682412023123705)
  ·
    refine ⟨28498640750011809017342779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37998187666682412023123705 28498640750011809017342779)
    ·
      refine ⟨42747961125017713526014169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28498640750011809017342779 42747961125017713526014169)
      ·
        refine ⟨32060970843763285144510627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42747961125017713526014169 32060970843763285144510627)
        ·
          refine ⟨48091456265644927716765941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32060970843763285144510627 48091456265644927716765941)
          ·
            refine ⟨4508574024904211973446807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48091456265644927716765941 4508574024904211973446807)
            ·
              refine ⟨6762861037356317960170211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508574024904211973446807 6762861037356317960170211)
              ·
                refine ⟨10144291556034476940255317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762861037356317960170211 10144291556034476940255317)
                ·
                  refine ⟨118878416672279026643617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10144291556034476940255317 118878416672279026643617)
                  ·
                    rfl

theorem cell22_1041817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_1041817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041817 prefixEnd_1041817 := by exact prefixLift 1041817
  have htrace : WordTrace (prefixWord ++ tailWord_1041817) baseStart_1041817 baseEnd_1041817 := by
    simpa [prefixWord, tailWord_1041817, baseEnd_1041817] using wordTrace_append hprefix tailTrace_1041817
  have hstable : (prefixWord ++ tailWord_1041817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041817).length < 2 ^ (prefixWord ++ tailWord_1041817).sum := by decide
  have hdescent : baseEnd_1041817 < baseStart_1041817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041836 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 1, 4]
def baseStart_1041836 : Nat := 118140960795 + 1041836 * 2 ^ 59
def prefixEnd_1041836 : Nat := 4983230072969 + 3 ^ 40 * 1041836 * 2
def baseEnd_1041836 : Nat := 356641754105127363705793

theorem tailTrace_1041836 : CollatzResearch.WordTrace tailWord_1041836 prefixEnd_1041836 356641754105127363705793 := by
  unfold tailWord_1041836
  simp only [CollatzResearch.WordTrace]
  refine ⟨18999440326806789134032681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25332587102409052178710241 18999440326806789134032681)
  ·
    refine ⟨14249580245105091850524511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18999440326806789134032681 14249580245105091850524511)
    ·
      refine ⟨21374370367657637775786767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14249580245105091850524511 21374370367657637775786767)
      ·
        refine ⟨32061555551486456663680151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21374370367657637775786767 32061555551486456663680151)
        ·
          refine ⟨48092333327229684995520227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32061555551486456663680151 48092333327229684995520227)
          ·
            refine ⟨72138499990844527493280341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48092333327229684995520227 72138499990844527493280341)
            ·
              refine ⟨845373046767709306561879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 72138499990844527493280341 845373046767709306561879)
              ·
                refine ⟨1268059570151563959842819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845373046767709306561879 1268059570151563959842819)
                ·
                  refine ⟨1902089355227345939764229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268059570151563959842819 1902089355227345939764229)
                  ·
                    refine ⟨356641754105127363705793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1902089355227345939764229 356641754105127363705793)
                    ·
                      rfl

theorem cell22_1041836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_1041836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041836 prefixEnd_1041836 := by exact prefixLift 1041836
  have htrace : WordTrace (prefixWord ++ tailWord_1041836) baseStart_1041836 baseEnd_1041836 := by
    simpa [prefixWord, tailWord_1041836, baseEnd_1041836] using wordTrace_append hprefix tailTrace_1041836
  have hstable : (prefixWord ++ tailWord_1041836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041836).length < 2 ^ (prefixWord ++ tailWord_1041836).sum := by decide
  have hdescent : baseEnd_1041836 < baseStart_1041836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041866 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_1041866 : Nat := 118140960795 + 1041866 * 2 ^ 59
def prefixEnd_1041866 : Nat := 4983230072969 + 3 ^ 40 * 1041866 * 2
def baseEnd_1041866 : Nat := 356652023718217285455701

theorem tailTrace_1041866 : CollatzResearch.WordTrace tailWord_1041866 prefixEnd_1041866 356652023718217285455701 := by
  unfold tailWord_1041866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9499993710876223347914363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25333316562336595594438301 9499993710876223347914363)
  ·
    refine ⟨14249990566314335021871545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9499993710876223347914363 14249990566314335021871545)
    ·
      refine ⟨10687492924735751266403659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14249990566314335021871545 10687492924735751266403659)
      ·
        refine ⟨16031239387103626899605489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10687492924735751266403659 16031239387103626899605489)
        ·
          refine ⟨12023429540327720174704117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16031239387103626899605489 12023429540327720174704117)
          ·
            refine ⟨1127196519405723766378511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12023429540327720174704117 1127196519405723766378511)
            ·
              refine ⟨1690794779108585649567767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127196519405723766378511 1690794779108585649567767)
              ·
                refine ⟨2536192168662878474351651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690794779108585649567767 2536192168662878474351651)
                ·
                  refine ⟨3804288252994317711527477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536192168662878474351651 3804288252994317711527477)
                  ·
                    refine ⟨356652023718217285455701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3804288252994317711527477 356652023718217285455701)
                    ·
                      rfl

theorem cell22_1041866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_1041866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041866 prefixEnd_1041866 := by exact prefixLift 1041866
  have htrace : WordTrace (prefixWord ++ tailWord_1041866) baseStart_1041866 baseEnd_1041866 := by
    simpa [prefixWord, tailWord_1041866, baseEnd_1041866] using wordTrace_append hprefix tailTrace_1041866
  have hstable : (prefixWord ++ tailWord_1041866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041866).length < 2 ^ (prefixWord ++ tailWord_1041866).sum := by decide
  have hdescent : baseEnd_1041866 < baseStart_1041866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041969 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 6]
def baseStart_1041969 : Nat := 118140960795 + 1041969 * 2 ^ 59
def prefixEnd_1041969 : Nat := 4983230072969 + 3 ^ 40 * 1041969 * 2
def baseEnd_1041969 : Nat := 118895760907719783376795

theorem tailTrace_1041969 : CollatzResearch.WordTrace tailWord_1041969 prefixEnd_1041969 118895760907719783376795 := by
  unfold tailWord_1041969
  simp only [CollatzResearch.WordTrace]
  refine ⟨38003731562131741982656961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25335821041421161321771307 38003731562131741982656961)
  ·
    refine ⟨28502798671598806486992721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38003731562131741982656961 28502798671598806486992721)
    ·
      refine ⟨21377099003699104865244541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28502798671598806486992721 21377099003699104865244541)
      ·
        refine ⟨8016412126387164324466703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21377099003699104865244541 8016412126387164324466703)
        ·
          refine ⟨12024618189580746486700055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8016412126387164324466703 12024618189580746486700055)
          ·
            refine ⟨18036927284371119730050083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024618189580746486700055 18036927284371119730050083)
            ·
              refine ⟨27055390926556679595075125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18036927284371119730050083 27055390926556679595075125)
              ·
                refine ⟨2536442899364688712038293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27055390926556679595075125 2536442899364688712038293)
                ·
                  refine ⟨118895760907719783376795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2536442899364688712038293 118895760907719783376795)
                  ·
                    rfl

theorem cell22_1041969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_1041969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1041969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1041969 prefixEnd_1041969 := by exact prefixLift 1041969
  have htrace : WordTrace (prefixWord ++ tailWord_1041969) baseStart_1041969 baseEnd_1041969 := by
    simpa [prefixWord, tailWord_1041969, baseEnd_1041969] using wordTrace_append hprefix tailTrace_1041969
  have hstable : (prefixWord ++ tailWord_1041969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041969).length < 2 ^ (prefixWord ++ tailWord_1041969).sum := by decide
  have hdescent : baseEnd_1041969 < baseStart_1041969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042001 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 4, 3]
def baseStart_1042001 : Nat := 118140960795 + 1042001 * 2 ^ 59
def prefixEnd_1042001 : Nat := 4983230072969 + 3 ^ 40 * 1042001 * 2
def baseEnd_1042001 : Nat := 356698236977121933330287

theorem tailTrace_1042001 : CollatzResearch.WordTrace tailWord_1042001 prefixEnd_1042001 356698236977121933330287 := by
  unfold tailWord_1042001
  simp only [CollatzResearch.WordTrace]
  refine ⟨38004898698015811447821857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25336599132010540965214571 38004898698015811447821857)
  ·
    refine ⟨28503674023511858585866393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38004898698015811447821857 28503674023511858585866393)
    ·
      refine ⟨21377755517633893939399795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28503674023511858585866393 21377755517633893939399795)
      ·
        refine ⟨32066633276450840909099693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21377755517633893939399795 32066633276450840909099693)
        ·
          refine ⟨12024987478669065340912385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32066633276450840909099693 12024987478669065340912385)
          ·
            refine ⟨9018740609001799005684289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12024987478669065340912385 9018740609001799005684289)
            ·
              refine ⟨6764055456751349254263217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9018740609001799005684289 6764055456751349254263217)
              ·
                refine ⟨5073041592563511940697413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6764055456751349254263217 5073041592563511940697413)
                ·
                  refine ⟨951195298605658488880765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5073041592563511940697413 951195298605658488880765)
                  ·
                    refine ⟨356698236977121933330287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 951195298605658488880765 356698236977121933330287)
                    ·
                      rfl

theorem cell22_1042001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_1042001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042001 prefixEnd_1042001 := by exact prefixLift 1042001
  have htrace : WordTrace (prefixWord ++ tailWord_1042001) baseStart_1042001 baseEnd_1042001 := by
    simpa [prefixWord, tailWord_1042001, baseEnd_1042001] using wordTrace_append hprefix tailTrace_1042001
  have hstable : (prefixWord ++ tailWord_1042001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042001).length < 2 ^ (prefixWord ++ tailWord_1042001).sum := by decide
  have hdescent : baseEnd_1042001 < baseStart_1042001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042059 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 9]
def baseStart_1042059 : Nat := 118140960795 + 1042059 * 2 ^ 59
def prefixEnd_1042059 : Nat := 4983230072969 + 3 ^ 40 * 1042059 * 2
def baseEnd_1042059 : Nat := 118906030520809705126703

theorem tailTrace_1042059 : CollatzResearch.WordTrace tailWord_1042059 prefixEnd_1042059 118906030520809705126703 := by
  unfold tailWord_1042059
  simp only [CollatzResearch.WordTrace]
  refine ⟨38007014131805687353433231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25338009421203791568955487 38007014131805687353433231)
  ·
    refine ⟨57010521197708531030149847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38007014131805687353433231 57010521197708531030149847)
    ·
      refine ⟨85515781796562796545224771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57010521197708531030149847 85515781796562796545224771)
      ·
        refine ⟨128273672694844194817837157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85515781796562796545224771 128273672694844194817837157)
        ·
          refine ⟨24051313630283286528344467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128273672694844194817837157 24051313630283286528344467)
          ·
            refine ⟨36076970445424929792516701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24051313630283286528344467 36076970445424929792516701)
            ·
              refine ⟨13528863917034348672193763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36076970445424929792516701 13528863917034348672193763)
              ·
                refine ⟨20293295875551523008290645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13528863917034348672193763 20293295875551523008290645)
                ·
                  refine ⟨118906030520809705126703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20293295875551523008290645 118906030520809705126703)
                  ·
                    rfl

theorem cell22_1042059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 9].length) (baseStart_1042059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042059 prefixEnd_1042059 := by exact prefixLift 1042059
  have htrace : WordTrace (prefixWord ++ tailWord_1042059) baseStart_1042059 baseEnd_1042059 := by
    simpa [prefixWord, tailWord_1042059, baseEnd_1042059] using wordTrace_append hprefix tailTrace_1042059
  have hstable : (prefixWord ++ tailWord_1042059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042059).length < 2 ^ (prefixWord ++ tailWord_1042059).sum := by decide
  have hdescent : baseEnd_1042059 < baseStart_1042059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042080 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 3, 3]
def baseStart_1042080 : Nat := 118140960795 + 1042080 * 2 ^ 59
def prefixEnd_1042080 : Nat := 4983230072969 + 3 ^ 40 * 1042080 * 2
def baseEnd_1042080 : Nat := 356725280291592060605045

theorem tailTrace_1042080 : CollatzResearch.WordTrace tailWord_1042080 prefixEnd_1042080 356725280291592060605045 := by
  unfold tailWord_1042080
  simp only [CollatzResearch.WordTrace]
  refine ⟨19003890032364803969973847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25338520043153071959965129 19003890032364803969973847)
  ·
    refine ⟨28505835048547205954960771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19003890032364803969973847 28505835048547205954960771)
    ·
      refine ⟨42758752572820808932441157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28505835048547205954960771 42758752572820808932441157)
      ·
        refine ⟨8017266107403901674832717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42758752572820808932441157 8017266107403901674832717)
        ·
          refine ⟨3006474790276463128062269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8017266107403901674832717 3006474790276463128062269)
          ·
            refine ⟨1127428046353673673023351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3006474790276463128062269 1127428046353673673023351)
            ·
              refine ⟨1691142069530510509535027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127428046353673673023351 1691142069530510509535027)
              ·
                refine ⟨2536713104295765764302541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691142069530510509535027 2536713104295765764302541)
                ·
                  refine ⟨951267414110912161613453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2536713104295765764302541 951267414110912161613453)
                  ·
                    refine ⟨356725280291592060605045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 951267414110912161613453 356725280291592060605045)
                    ·
                      rfl

theorem cell22_1042080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_1042080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042080 prefixEnd_1042080 := by exact prefixLift 1042080
  have htrace : WordTrace (prefixWord ++ tailWord_1042080) baseStart_1042080 baseEnd_1042080 := by
    simpa [prefixWord, tailWord_1042080, baseEnd_1042080] using wordTrace_append hprefix tailTrace_1042080
  have hstable : (prefixWord ++ tailWord_1042080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042080).length < 2 ^ (prefixWord ++ tailWord_1042080).sum := by decide
  have hdescent : baseEnd_1042080 < baseStart_1042080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042093 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1042093 : Nat := 118140960795 + 1042093 * 2 ^ 59
def prefixEnd_1042093 : Nat := 4983230072969 + 3 ^ 40 * 1042093 * 2
def baseEnd_1042093 : Nat := 118909910152421453343335

theorem tailTrace_1042093 : CollatzResearch.WordTrace tailWord_1042093 prefixEnd_1042093 118909910152421453343335 := by
  unfold tailWord_1042093
  simp only [CollatzResearch.WordTrace]
  refine ⟨38008254213682511160170933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25338836142455007440113955 38008254213682511160170933)
  ·
    refine ⟨3563273832532735421266025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38008254213682511160170933 3563273832532735421266025)
    ·
      refine ⟨2672455374399551565949519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3563273832532735421266025 2672455374399551565949519)
      ·
        refine ⟨4008683061599327348924279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672455374399551565949519 4008683061599327348924279)
        ·
          refine ⟨6013024592398991023386419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008683061599327348924279 6013024592398991023386419)
          ·
            refine ⟨9019536888598486535079629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013024592398991023386419 9019536888598486535079629)
            ·
              refine ⟨3382326333224432450654861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9019536888598486535079629 3382326333224432450654861)
              ·
                refine ⟨1268372374959162168995573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3382326333224432450654861 1268372374959162168995573)
                ·
                  refine ⟨118909910152421453343335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1268372374959162168995573 118909910152421453343335)
                  ·
                    rfl

theorem cell22_1042093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1042093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042093 prefixEnd_1042093 := by exact prefixLift 1042093
  have htrace : WordTrace (prefixWord ++ tailWord_1042093) baseStart_1042093 baseEnd_1042093 := by
    simpa [prefixWord, tailWord_1042093, baseEnd_1042093] using wordTrace_append hprefix tailTrace_1042093
  have hstable : (prefixWord ++ tailWord_1042093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042093).length < 2 ^ (prefixWord ++ tailWord_1042093).sum := by decide
  have hdescent : baseEnd_1042093 < baseStart_1042093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042136 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_1042136 : Nat := 118140960795 + 1042136 * 2 ^ 59
def prefixEnd_1042136 : Nat := 4983230072969 + 3 ^ 40 * 1042136 * 2
def baseEnd_1042136 : Nat := 356744450236026581204873

theorem tailTrace_1042136 : CollatzResearch.WordTrace tailWord_1042136 prefixEnd_1042136 356744450236026581204873 := by
  unfold tailWord_1042136
  simp only [CollatzResearch.WordTrace]
  refine ⟨19004911276263364751993131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25339881701684486335990841 19004911276263364751993131)
  ·
    refine ⟨28507366914395047127989697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19004911276263364751993131 28507366914395047127989697)
    ·
      refine ⟨21380525185796285345992273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28507366914395047127989697 21380525185796285345992273)
      ·
        refine ⟨16035393889347214009494205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21380525185796285345992273 16035393889347214009494205)
        ·
          refine ⟨6013272708505205253560327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16035393889347214009494205 6013272708505205253560327)
          ·
            refine ⟨9019909062757807880340491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013272708505205253560327 9019909062757807880340491)
            ·
              refine ⟨13529863594136711820510737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019909062757807880340491 13529863594136711820510737)
              ·
                refine ⟨10147397695602533865383053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13529863594136711820510737 10147397695602533865383053)
                ·
                  refine ⟨3805274135850950199518645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10147397695602533865383053 3805274135850950199518645)
                  ·
                    refine ⟨356744450236026581204873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3805274135850950199518645 356744450236026581204873)
                    ·
                      rfl

theorem cell22_1042136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_1042136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042136 prefixEnd_1042136 := by exact prefixLift 1042136
  have htrace : WordTrace (prefixWord ++ tailWord_1042136) baseStart_1042136 baseEnd_1042136 := by
    simpa [prefixWord, tailWord_1042136, baseEnd_1042136] using wordTrace_append hprefix tailTrace_1042136
  have hstable : (prefixWord ++ tailWord_1042136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042136).length < 2 ^ (prefixWord ++ tailWord_1042136).sum := by decide
  have hdescent : baseEnd_1042136 < baseStart_1042136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042174 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1042174 : Nat := 118140960795 + 1042174 * 2 ^ 59
def prefixEnd_1042174 : Nat := 4983230072969 + 3 ^ 40 * 1042174 * 2
def baseEnd_1042174 : Nat := 356757458412607148754757

theorem tailTrace_1042174 : CollatzResearch.WordTrace tailWord_1042174 prefixEnd_1042174 356757458412607148754757 := by
  unfold tailWord_1042174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751401065798632749233697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25340805684259374662579717 4751401065798632749233697)
  ·
    refine ⟨3563550799348974561925273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4751401065798632749233697 3563550799348974561925273)
    ·
      refine ⟨2672663099511730921443955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3563550799348974561925273 2672663099511730921443955)
      ·
        refine ⟨4008994649267596382165933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672663099511730921443955 4008994649267596382165933)
        ·
          refine ⟨1503372993475348643312225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4008994649267596382165933 1503372993475348643312225)
          ·
            refine ⟨1127529745106511482484169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503372993475348643312225 1127529745106511482484169)
            ·
              refine ⟨845647308829883611863127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127529745106511482484169 845647308829883611863127)
              ·
                refine ⟨1268470963244825417794691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845647308829883611863127 1268470963244825417794691)
                ·
                  refine ⟨1902706444867238126692037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268470963244825417794691 1902706444867238126692037)
                  ·
                    refine ⟨356757458412607148754757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1902706444867238126692037 356757458412607148754757)
                    ·
                      rfl

theorem cell22_1042174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1042174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042174 prefixEnd_1042174 := by exact prefixLift 1042174
  have htrace : WordTrace (prefixWord ++ tailWord_1042174) baseStart_1042174 baseEnd_1042174 := by
    simpa [prefixWord, tailWord_1042174, baseEnd_1042174] using wordTrace_append hprefix tailTrace_1042174
  have hstable : (prefixWord ++ tailWord_1042174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042174).length < 2 ^ (prefixWord ++ tailWord_1042174).sum := by decide
  have hdescent : baseEnd_1042174 < baseStart_1042174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042183 : List Nat := [1, 1, 4, 4, 2, 1, 9]
def baseStart_1042183 : Nat := 118140960795 + 1042183 * 2 ^ 59
def prefixEnd_1042183 : Nat := 4983230072969 + 3 ^ 40 * 1042183 * 2
def baseEnd_1042183 : Nat := 13213353307279041677027

theorem tailTrace_1042183 : CollatzResearch.WordTrace tailWord_1042183 prefixEnd_1042183 13213353307279041677027 := by
  unfold tailWord_1042183
  simp only [CollatzResearch.WordTrace]
  refine ⟨38011536783356456530947203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25341024522237637687298135 38011536783356456530947203)
  ·
    refine ⟨57017305175034684796420805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38011536783356456530947203 57017305175034684796420805)
    ·
      refine ⟨10690744720319003399328901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57017305175034684796420805 10690744720319003399328901)
      ·
        refine ⟨2004514635059813137374169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10690744720319003399328901 2004514635059813137374169)
        ·
          refine ⟨1503385976294859853030627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2004514635059813137374169 1503385976294859853030627)
          ·
            refine ⟨2255078964442289779545941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503385976294859853030627 2255078964442289779545941)
            ·
              refine ⟨13213353307279041677027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2255078964442289779545941 13213353307279041677027)
              ·
                rfl

theorem cell22_1042183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 9].length) (baseStart_1042183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042183 prefixEnd_1042183 := by exact prefixLift 1042183
  have htrace : WordTrace (prefixWord ++ tailWord_1042183) baseStart_1042183 baseEnd_1042183 := by
    simpa [prefixWord, tailWord_1042183, baseEnd_1042183] using wordTrace_append hprefix tailTrace_1042183
  have hstable : (prefixWord ++ tailWord_1042183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042183).length < 2 ^ (prefixWord ++ tailWord_1042183).sum := by decide
  have hdescent : baseEnd_1042183 < baseStart_1042183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042232 : List Nat := [2, 1, 2, 1, 3, 3, 3, 3, 1, 3]
def baseStart_1042232 : Nat := 118140960795 + 1042232 * 2 ^ 59
def prefixEnd_1042232 : Nat := 4983230072969 + 3 ^ 40 * 1042232 * 2
def baseEnd_1042232 : Nat := 356777312997914330804579

theorem tailTrace_1042232 : CollatzResearch.WordTrace tailWord_1042232 prefixEnd_1042232 356777312997914330804579 := by
  unfold tailWord_1042232
  simp only [CollatzResearch.WordTrace]
  refine ⟨19006661980089468949740475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25342215973452625266320633 19006661980089468949740475)
  ·
    refine ⟨28509992970134203424610713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19006661980089468949740475 28509992970134203424610713)
    ·
      refine ⟨21382494727600652568458035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28509992970134203424610713 21382494727600652568458035)
      ·
        refine ⟨32073742091400978852687053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21382494727600652568458035 32073742091400978852687053)
        ·
          refine ⟨12027653284275367069757645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32073742091400978852687053 12027653284275367069757645)
          ·
            refine ⟨4510369981603262651159117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12027653284275367069757645 4510369981603262651159117)
            ·
              refine ⟨1691388743101223494184669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4510369981603262651159117 1691388743101223494184669)
              ·
                refine ⟨634270778662958810319251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1691388743101223494184669 634270778662958810319251)
                ·
                  refine ⟨951406167994438215478877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634270778662958810319251 951406167994438215478877)
                  ·
                    refine ⟨356777312997914330804579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 951406167994438215478877 356777312997914330804579)
                    ·
                      rfl

theorem cell22_1042232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_1042232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042232 prefixEnd_1042232 := by exact prefixLift 1042232
  have htrace : WordTrace (prefixWord ++ tailWord_1042232) baseStart_1042232 baseEnd_1042232 := by
    simpa [prefixWord, tailWord_1042232, baseEnd_1042232] using wordTrace_append hprefix tailTrace_1042232
  have hstable : (prefixWord ++ tailWord_1042232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042232).length < 2 ^ (prefixWord ++ tailWord_1042232).sum := by decide
  have hdescent : baseEnd_1042232 < baseStart_1042232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042275 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 3, 4]
def baseStart_1042275 : Nat := 118140960795 + 1042275 * 2 ^ 59
def prefixEnd_1042275 : Nat := 4983230072969 + 3 ^ 40 * 1042275 * 2
def baseEnd_1042275 : Nat := 356792032776676551979447

theorem tailTrace_1042275 : CollatzResearch.WordTrace tailWord_1042275 prefixEnd_1042275 356792032776676551979447 := by
  unfold tailWord_1042275
  simp only [CollatzResearch.WordTrace]
  refine ⟨38014892299023156243296279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25343261532682104162197519 38014892299023156243296279)
  ·
    refine ⟨57022338448534734364944419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38014892299023156243296279 57022338448534734364944419)
    ·
      refine ⟨85533507672802101547416629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57022338448534734364944419 85533507672802101547416629)
      ·
        refine ⟨8018766344325197020070309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85533507672802101547416629 8018766344325197020070309)
        ·
          refine ⟨1503518689560974441263183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8018766344325197020070309 1503518689560974441263183)
          ·
            refine ⟨2255278034341461661894775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503518689560974441263183 2255278034341461661894775)
            ·
              refine ⟨3382917051512192492842163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255278034341461661894775 3382917051512192492842163)
              ·
                refine ⟨5074375577268288739263245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382917051512192492842163 5074375577268288739263245)
                ·
                  refine ⟨1902890841475608277223717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5074375577268288739263245 1902890841475608277223717)
                  ·
                    refine ⟨356792032776676551979447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1902890841475608277223717 356792032776676551979447)
                    ·
                      rfl

theorem cell22_1042275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 4].length) (baseStart_1042275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042275 prefixEnd_1042275 := by exact prefixLift 1042275
  have htrace : WordTrace (prefixWord ++ tailWord_1042275) baseStart_1042275 baseEnd_1042275 := by
    simpa [prefixWord, tailWord_1042275, baseEnd_1042275] using wordTrace_append hprefix tailTrace_1042275
  have hstable : (prefixWord ++ tailWord_1042275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042275).length < 2 ^ (prefixWord ++ tailWord_1042275).sum := by decide
  have hdescent : baseEnd_1042275 < baseStart_1042275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042290 : List Nat := [3, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_1042290 : Nat := 118140960795 + 1042290 * 2 ^ 59
def prefixEnd_1042290 : Nat := 4983230072969 + 3 ^ 40 * 1042290 * 2
def baseEnd_1042290 : Nat := 118932389194407170951467

theorem tailTrace_1042290 : CollatzResearch.WordTrace tailWord_1042290 prefixEnd_1042290 118932389194407170951467 := by
  unfold tailWord_1042290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9503859848492203451273081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25343626262645875870061549 9503859848492203451273081)
  ·
    refine ⟨7127894886369152588454811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9503859848492203451273081 7127894886369152588454811)
    ·
      refine ⟨10691842329553728882682217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7127894886369152588454811 10691842329553728882682217)
      ·
        refine ⟨8018881747165296662011663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10691842329553728882682217 8018881747165296662011663)
        ·
          refine ⟨12028322620747944993017495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018881747165296662011663 12028322620747944993017495)
          ·
            refine ⟨18042483931121917489526243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12028322620747944993017495 18042483931121917489526243)
            ·
              refine ⟨27063725896682876234289365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18042483931121917489526243 27063725896682876234289365)
              ·
                refine ⟨634306075703504911741157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27063725896682876234289365 634306075703504911741157)
                ·
                  refine ⟨118932389194407170951467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634306075703504911741157 118932389194407170951467)
                  ·
                    rfl

theorem cell22_1042290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_1042290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042290 prefixEnd_1042290 := by exact prefixLift 1042290
  have htrace : WordTrace (prefixWord ++ tailWord_1042290) baseStart_1042290 baseEnd_1042290 := by
    simpa [prefixWord, tailWord_1042290, baseEnd_1042290] using wordTrace_append hprefix tailTrace_1042290
  have hstable : (prefixWord ++ tailWord_1042290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042290).length < 2 ^ (prefixWord ++ tailWord_1042290).sum := by decide
  have hdescent : baseEnd_1042290 < baseStart_1042290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042307 : List Nat := [1, 1, 1, 3, 4, 2, 4, 2, 4]
def baseStart_1042307 : Nat := 118140960795 + 1042307 * 2 ^ 59
def prefixEnd_1042307 : Nat := 4983230072969 + 3 ^ 40 * 1042307 * 2
def baseEnd_1042307 : Nat := 118934329010213045059783

theorem tailTrace_1042307 : CollatzResearch.WordTrace tailWord_1042307 prefixEnd_1042307 118934329010213045059783 := by
  unfold tailWord_1042307
  simp only [CollatzResearch.WordTrace]
  refine ⟨38016059434907225708461175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25344039623271483805640783 38016059434907225708461175)
  ·
    refine ⟨57024089152360838562691763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38016059434907225708461175 57024089152360838562691763)
    ·
      refine ⟨85536133728541257844037645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57024089152360838562691763 85536133728541257844037645)
      ·
        refine ⟨32076050148202971691514117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85536133728541257844037645 32076050148202971691514117)
        ·
          refine ⟨6014259402788057192158897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32076050148202971691514117 6014259402788057192158897)
          ·
            refine ⟨4510694552091042894119173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6014259402788057192158897 4510694552091042894119173)
            ·
              refine ⟨845755228517070542647345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4510694552091042894119173 845755228517070542647345)
              ·
                refine ⟨634316421387802906985509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845755228517070542647345 634316421387802906985509)
                ·
                  refine ⟨118934329010213045059783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634316421387802906985509 118934329010213045059783)
                  ·
                    rfl

theorem cell22_1042307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 4].length) (baseStart_1042307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042307 prefixEnd_1042307 := by exact prefixLift 1042307
  have htrace : WordTrace (prefixWord ++ tailWord_1042307) baseStart_1042307 baseEnd_1042307 := by
    simpa [prefixWord, tailWord_1042307, baseEnd_1042307] using wordTrace_append hprefix tailTrace_1042307
  have hstable : (prefixWord ++ tailWord_1042307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042307).length < 2 ^ (prefixWord ++ tailWord_1042307).sum := by decide
  have hdescent : baseEnd_1042307 < baseStart_1042307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042322 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1042322 : Nat := 118140960795 + 1042322 * 2 ^ 59
def prefixEnd_1042322 : Nat := 4983230072969 + 3 ^ 40 * 1042322 * 2
def baseEnd_1042322 : Nat := 356808121837184096054303

theorem tailTrace_1042322 : CollatzResearch.WordTrace tailWord_1042322 prefixEnd_1042322 356808121837184096054303 := by
  unfold tailWord_1042322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504151632463220817564305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25344404353235255513504813 9504151632463220817564305)
  ·
    refine ⟨7128113724347415613173229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9504151632463220817564305 7128113724347415613173229)
    ·
      refine ⟨2673042646630280854939961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7128113724347415613173229 2673042646630280854939961)
      ·
        refine ⟨2004781984972710641204971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673042646630280854939961 2004781984972710641204971)
        ·
          refine ⟨3007172977459065961807457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2004781984972710641204971 3007172977459065961807457)
          ·
            refine ⟨2255379733094299471355593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3007172977459065961807457 2255379733094299471355593)
            ·
              refine ⟨1691534799820724603516695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255379733094299471355593 1691534799820724603516695)
              ·
                refine ⟨2537302199731086905275043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691534799820724603516695 2537302199731086905275043)
                ·
                  refine ⟨3805953299596630357912565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537302199731086905275043 3805953299596630357912565)
                  ·
                    refine ⟨356808121837184096054303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3805953299596630357912565 356808121837184096054303)
                    ·
                      rfl

theorem cell22_1042322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1042322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042322 prefixEnd_1042322 := by exact prefixLift 1042322
  have htrace : WordTrace (prefixWord ++ tailWord_1042322) baseStart_1042322 baseEnd_1042322 := by
    simpa [prefixWord, tailWord_1042322, baseEnd_1042322] using wordTrace_append hprefix tailTrace_1042322
  have hstable : (prefixWord ++ tailWord_1042322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042322).length < 2 ^ (prefixWord ++ tailWord_1042322).sum := by decide
  have hdescent : baseEnd_1042322 < baseStart_1042322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042367 : List Nat := [1, 1, 2, 2, 2, 1, 3, 6, 1, 3]
def baseStart_1042367 : Nat := 118140960795 + 1042367 * 2 ^ 59
def prefixEnd_1042367 : Nat := 4983230072969 + 3 ^ 40 * 1042367 * 2
def baseEnd_1042367 : Nat := 356823526256818978679165

theorem tailTrace_1042367 : CollatzResearch.WordTrace tailWord_1042367 prefixEnd_1042367 356823526256818978679165 := by
  unfold tailWord_1042367
  simp only [CollatzResearch.WordTrace]
  refine ⟨38018247814689855955645355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25345498543126570637096903 38018247814689855955645355)
  ·
    refine ⟨57027371722034783933468033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38018247814689855955645355 57027371722034783933468033)
    ·
      refine ⟨42770528791526087950101025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57027371722034783933468033 42770528791526087950101025)
      ·
        refine ⟨32077896593644565962575769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42770528791526087950101025 32077896593644565962575769)
        ·
          refine ⟨24058422445233424471931827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32077896593644565962575769 24058422445233424471931827)
          ·
            refine ⟨36087633667850136707897741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24058422445233424471931827 36087633667850136707897741)
            ·
              refine ⟨13532862625443801265461653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36087633667850136707897741 13532862625443801265461653)
              ·
                refine ⟨634352935567678184318515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13532862625443801265461653 634352935567678184318515)
                ·
                  refine ⟨951529403351517276477773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634352935567678184318515 951529403351517276477773)
                  ·
                    refine ⟨356823526256818978679165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 951529403351517276477773 356823526256818978679165)
                    ·
                      rfl

theorem cell22_1042367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 3].length) (baseStart_1042367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042367 prefixEnd_1042367 := by exact prefixLift 1042367
  have htrace : WordTrace (prefixWord ++ tailWord_1042367) baseStart_1042367 baseEnd_1042367 := by
    simpa [prefixWord, tailWord_1042367, baseEnd_1042367] using wordTrace_append hprefix tailTrace_1042367
  have hstable : (prefixWord ++ tailWord_1042367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042367).length < 2 ^ (prefixWord ++ tailWord_1042367).sum := by decide
  have hdescent : baseEnd_1042367 < baseStart_1042367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042425 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 6]
def baseStart_1042425 : Nat := 118140960795 + 1042425 * 2 ^ 59
def prefixEnd_1042425 : Nat := 4983230072969 + 3 ^ 40 * 1042425 * 2
def baseEnd_1042425 : Nat := 118947793614042053576329

theorem tailTrace_1042425 : CollatzResearch.WordTrace tailWord_1042425 prefixEnd_1042425 118947793614042053576329 := by
  unfold tailWord_1042425
  simp only [CollatzResearch.WordTrace]
  refine ⟨38020363248479731861256729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25346908832319821240837819 38020363248479731861256729)
  ·
    refine ⟨28515272436359798895942547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38020363248479731861256729 28515272436359798895942547)
    ·
      refine ⟨42772908654539698343913821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28515272436359798895942547 42772908654539698343913821)
      ·
        refine ⟨16039840745452386878967683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42772908654539698343913821 16039840745452386878967683)
        ·
          refine ⟨24059761118178580318451525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16039840745452386878967683 24059761118178580318451525)
          ·
            refine ⟨4511205209658483809709661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24059761118178580318451525 4511205209658483809709661)
            ·
              refine ⟨1691701953621931428641123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4511205209658483809709661 1691701953621931428641123)
              ·
                refine ⟨2537552930432897142961685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691701953621931428641123 2537552930432897142961685)
                ·
                  refine ⟨118947793614042053576329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2537552930432897142961685 118947793614042053576329)
                  ·
                    rfl

theorem cell22_1042425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_1042425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042425 prefixEnd_1042425 := by exact prefixLift 1042425
  have htrace : WordTrace (prefixWord ++ tailWord_1042425) baseStart_1042425 baseEnd_1042425 := by
    simpa [prefixWord, tailWord_1042425, baseEnd_1042425] using wordTrace_append hprefix tailTrace_1042425
  have hstable : (prefixWord ++ tailWord_1042425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042425).length < 2 ^ (prefixWord ++ tailWord_1042425).sum := by decide
  have hdescent : baseEnd_1042425 < baseStart_1042425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042440 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1042440 : Nat := 118140960795 + 1042440 * 2 ^ 59
def prefixEnd_1042440 : Nat := 4983230072969 + 3 ^ 40 * 1042440 * 2
def baseEnd_1042440 : Nat := 356848515648671121603941

theorem tailTrace_1042440 : CollatzResearch.WordTrace tailWord_1042440 prefixEnd_1042440 356848515648671121603941 := by
  unfold tailWord_1042440
  simp only [CollatzResearch.WordTrace]
  refine ⟨19010455171712694711526387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25347273562283592948701849 19010455171712694711526387)
  ·
    refine ⟨28515682757569042067289581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19010455171712694711526387 28515682757569042067289581)
    ·
      refine ⟨10693381034088390775233593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28515682757569042067289581 10693381034088390775233593)
      ·
        refine ⟨8020035775566293081425195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10693381034088390775233593 8020035775566293081425195)
        ·
          refine ⟨12030053663349439622137793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8020035775566293081425195 12030053663349439622137793)
          ·
            refine ⟨9022540247512079716603345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12030053663349439622137793 9022540247512079716603345)
            ·
              refine ⟨6766905185634059787452509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9022540247512079716603345 6766905185634059787452509)
              ·
                refine ⟨2537589444612772420294691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6766905185634059787452509 2537589444612772420294691)
                ·
                  refine ⟨3806384166919158630442037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537589444612772420294691 3806384166919158630442037)
                  ·
                    refine ⟨356848515648671121603941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3806384166919158630442037 356848515648671121603941)
                    ·
                      rfl

theorem cell22_1042440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1042440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042440 prefixEnd_1042440 := by exact prefixLift 1042440
  have htrace : WordTrace (prefixWord ++ tailWord_1042440) baseStart_1042440 baseEnd_1042440 := by
    simpa [prefixWord, tailWord_1042440, baseEnd_1042440] using wordTrace_append hprefix tailTrace_1042440
  have hstable : (prefixWord ++ tailWord_1042440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042440).length < 2 ^ (prefixWord ++ tailWord_1042440).sum := by decide
  have hdescent : baseEnd_1042440 < baseStart_1042440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042474 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1042474 : Nat := 118140960795 + 1042474 * 2 ^ 59
def prefixEnd_1042474 : Nat := 4983230072969 + 3 ^ 40 * 1042474 * 2
def baseEnd_1042474 : Nat := 356860154543506366253837

theorem tailTrace_1042474 : CollatzResearch.WordTrace tailWord_1042474 prefixEnd_1042474 356860154543506366253837 := by
  unfold tailWord_1042474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9505537606325553307447619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25348100283534808819860317 9505537606325553307447619)
  ·
    refine ⟨14258306409488329961171429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9505537606325553307447619 14258306409488329961171429)
    ·
      refine ⟨2673432451779061867719643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14258306409488329961171429 2673432451779061867719643)
      ·
        refine ⟨4010148677668592801579465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673432451779061867719643 4010148677668592801579465)
        ·
          refine ⟨3007611508251444601184599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4010148677668592801579465 3007611508251444601184599)
          ·
            refine ⟨4511417262377166901776899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007611508251444601184599 4511417262377166901776899)
            ·
              refine ⟨6767125893565750352665349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511417262377166901776899 6767125893565750352665349)
              ·
                refine ⟨1268836105043578191124753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6767125893565750352665349 1268836105043578191124753)
                ·
                  refine ⟨951627078782683643343565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1268836105043578191124753 951627078782683643343565)
                  ·
                    refine ⟨356860154543506366253837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 951627078782683643343565 356860154543506366253837)
                    ·
                      rfl

theorem cell22_1042474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1042474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042474 prefixEnd_1042474 := by exact prefixLift 1042474
  have htrace : WordTrace (prefixWord ++ tailWord_1042474) baseStart_1042474 baseEnd_1042474 := by
    simpa [prefixWord, tailWord_1042474, baseEnd_1042474] using wordTrace_append hprefix tailTrace_1042474
  have hstable : (prefixWord ++ tailWord_1042474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042474).length < 2 ^ (prefixWord ++ tailWord_1042474).sum := by decide
  have hdescent : baseEnd_1042474 < baseStart_1042474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042519 : List Nat := [1, 1, 3, 2, 2, 1, 3, 5, 1, 3]
def baseStart_1042519 : Nat := 118140960795 + 1042519 * 2 ^ 59
def prefixEnd_1042519 : Nat := 4983230072969 + 3 ^ 40 * 1042519 * 2
def baseEnd_1042519 : Nat := 356875558963141248878699

theorem tailTrace_1042519 : CollatzResearch.WordTrace tailWord_1042519 prefixEnd_1042519 356875558963141248878699 := by
  unfold tailWord_1042519
  simp only [CollatzResearch.WordTrace]
  refine ⟨38023791710139185915178611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25349194473426123943452407 38023791710139185915178611)
  ·
    refine ⟨57035687565208778872767917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38023791710139185915178611 57035687565208778872767917)
    ·
      refine ⟨21388382836953292077287969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57035687565208778872767917 21388382836953292077287969)
      ·
        refine ⟨16041287127714969057965977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21388382836953292077287969 16041287127714969057965977)
        ·
          refine ⟨12030965345786226793474483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16041287127714969057965977 12030965345786226793474483)
          ·
            refine ⟨18046448018679340190211725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12030965345786226793474483 18046448018679340190211725)
            ·
              refine ⟨6767418007004752571329397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18046448018679340190211725 6767418007004752571329397)
              ·
                refine ⟨634445438156695553562131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6767418007004752571329397 634445438156695553562131)
                ·
                  refine ⟨951668157235043330343197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634445438156695553562131 951668157235043330343197)
                  ·
                    refine ⟨356875558963141248878699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 951668157235043330343197 356875558963141248878699)
                    ·
                      rfl

theorem cell22_1042519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_1042519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042519 prefixEnd_1042519 := by exact prefixLift 1042519
  have htrace : WordTrace (prefixWord ++ tailWord_1042519) baseStart_1042519 baseEnd_1042519 := by
    simpa [prefixWord, tailWord_1042519, baseEnd_1042519] using wordTrace_append hprefix tailTrace_1042519
  have hstable : (prefixWord ++ tailWord_1042519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042519).length < 2 ^ (prefixWord ++ tailWord_1042519).sum := by decide
  have hdescent : baseEnd_1042519 < baseStart_1042519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042532 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 5]
def baseStart_1042532 : Nat := 118140960795 + 1042532 * 2 ^ 59
def prefixEnd_1042532 : Nat := 4983230072969 + 3 ^ 40 * 1042532 * 2
def baseEnd_1042532 : Nat := 118960003042937849434553

theorem tailTrace_1042532 : CollatzResearch.WordTrace tailWord_1042532 prefixEnd_1042532 118960003042937849434553 := by
  unfold tailWord_1042532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19012132929546044567700925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25349510572728059423601233 19012132929546044567700925)
  ·
    refine ⟨7129549848579766712887847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19012132929546044567700925 7129549848579766712887847)
    ·
      refine ⟨10694324772869650069331771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7129549848579766712887847 10694324772869650069331771)
      ·
        refine ⟨16041487159304475103997657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10694324772869650069331771 16041487159304475103997657)
        ·
          refine ⟨12031115369478356327998243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16041487159304475103997657 12031115369478356327998243)
          ·
            refine ⟨18046673054217534491997365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12031115369478356327998243 18046673054217534491997365)
            ·
              refine ⟨1691875598832893858624753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18046673054217534491997365 1691875598832893858624753)
              ·
                refine ⟨1268906699124670393968565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691875598832893858624753 1268906699124670393968565)
                ·
                  refine ⟨118960003042937849434553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1268906699124670393968565 118960003042937849434553)
                  ·
                    rfl

theorem cell22_1042532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_1042532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042532 prefixEnd_1042532 := by exact prefixLift 1042532
  have htrace : WordTrace (prefixWord ++ tailWord_1042532) baseStart_1042532 baseEnd_1042532 := by
    simpa [prefixWord, tailWord_1042532, baseEnd_1042532] using wordTrace_append hprefix tailTrace_1042532
  have hstable : (prefixWord ++ tailWord_1042532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042532).length < 2 ^ (prefixWord ++ tailWord_1042532).sum := by decide
  have hdescent : baseEnd_1042532 < baseStart_1042532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042594 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1042594 : Nat := 118140960795 + 1042594 * 2 ^ 59
def prefixEnd_1042594 : Nat := 4983230072969 + 3 ^ 40 * 1042594 * 2
def baseEnd_1042594 : Nat := 118967077665288684417823

theorem tailTrace_1042594 : CollatzResearch.WordTrace tailWord_1042594 prefixEnd_1042594 118967077665288684417823 := by
  unfold tailWord_1042594
  simp only [CollatzResearch.WordTrace]
  refine ⟨9506631796216868431039709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25351018123244982482772557 9506631796216868431039709)
  ·
    refine ⟨3564986923581325661639891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9506631796216868431039709 3564986923581325661639891)
    ·
      refine ⟨5347480385371988492459837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3564986923581325661639891 5347480385371988492459837)
      ·
        refine ⟨2005305144514495684672439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5347480385371988492459837 2005305144514495684672439)
        ·
          refine ⟨3007957716771743527008659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005305144514495684672439 3007957716771743527008659)
          ·
            refine ⟨4511936575157615290512989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007957716771743527008659 4511936575157615290512989)
            ·
              refine ⟨1691976215684105733942371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4511936575157615290512989 1691976215684105733942371)
              ·
                refine ⟨2537964323526158600913557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691976215684105733942371 2537964323526158600913557)
                ·
                  refine ⟨118967077665288684417823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2537964323526158600913557 118967077665288684417823)
                  ·
                    rfl

theorem cell22_1042594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1042594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042594 prefixEnd_1042594 := by exact prefixLift 1042594
  have htrace : WordTrace (prefixWord ++ tailWord_1042594) baseStart_1042594 baseEnd_1042594 := by
    simpa [prefixWord, tailWord_1042594, baseEnd_1042594] using wordTrace_append hprefix tailTrace_1042594
  have hstable : (prefixWord ++ tailWord_1042594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042594).length < 2 ^ (prefixWord ++ tailWord_1042594).sum := by decide
  have hdescent : baseEnd_1042594 < baseStart_1042594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042613 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_1042613 : Nat := 118140960795 + 1042613 * 2 ^ 59
def prefixEnd_1042613 : Nat := 4983230072969 + 3 ^ 40 * 1042613 * 2
def baseEnd_1042613 : Nat := 356907737084156337028411

theorem tailTrace_1042613 : CollatzResearch.WordTrace tailWord_1042613 prefixEnd_1042613 356907737084156337028411 := by
  unfold tailWord_1042613
  simp only [CollatzResearch.WordTrace]
  refine ⟨38027220171798639969100493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25351480114532426646066995 38027220171798639969100493)
  ·
    refine ⟨14260207564424489988412685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38027220171798639969100493 14260207564424489988412685)
    ·
      refine ⟨5347577836659183745654757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14260207564424489988412685 5347577836659183745654757)
      ·
        refine ⟨1002670844373596952310267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5347577836659183745654757 1002670844373596952310267)
        ·
          refine ⟨1504006266560395428465401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002670844373596952310267 1504006266560395428465401)
          ·
            refine ⟨1128004699920296571349051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1504006266560395428465401 1128004699920296571349051)
            ·
              refine ⟨1692007049880444857023577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128004699920296571349051 1692007049880444857023577)
              ·
                refine ⟨1269005287410333642767683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692007049880444857023577 1269005287410333642767683)
                ·
                  refine ⟨1903507931115500464151525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269005287410333642767683 1903507931115500464151525)
                  ·
                    refine ⟨356907737084156337028411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903507931115500464151525 356907737084156337028411)
                    ·
                      rfl

theorem cell22_1042613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_1042613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042613 prefixEnd_1042613 := by exact prefixLift 1042613
  have htrace : WordTrace (prefixWord ++ tailWord_1042613) baseStart_1042613 baseEnd_1042613 := by
    simpa [prefixWord, tailWord_1042613, baseEnd_1042613] using wordTrace_append hprefix tailTrace_1042613
  have hstable : (prefixWord ++ tailWord_1042613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042613).length < 2 ^ (prefixWord ++ tailWord_1042613).sum := by decide
  have hdescent : baseEnd_1042613 < baseStart_1042613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042624 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_1042624 : Nat := 118140960795 + 1042624 * 2 ^ 59
def prefixEnd_1042624 : Nat := 4983230072969 + 3 ^ 40 * 1042624 * 2
def baseEnd_1042624 : Nat := 356911502608955975003377

theorem tailTrace_1042624 : CollatzResearch.WordTrace tailWord_1042624 prefixEnd_1042624 356911502608955975003377 := by
  unfold tailWord_1042624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19013810687379394423875463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25351747583172525898500617 19013810687379394423875463)
  ·
    refine ⟨28520716031069091635813195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19013810687379394423875463 28520716031069091635813195)
    ·
      refine ⟨42781074046603637453719793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28520716031069091635813195 42781074046603637453719793)
      ·
        refine ⟨32085805534952728090289845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42781074046603637453719793 32085805534952728090289845)
        ·
          refine ⟨3008044268901818258464673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32085805534952728090289845 3008044268901818258464673)
          ·
            refine ⟨2256033201676363693848505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3008044268901818258464673 2256033201676363693848505)
            ·
              refine ⟨1692024901257272770386379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256033201676363693848505 1692024901257272770386379)
              ·
                refine ⟨2538037351885909155579569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692024901257272770386379 2538037351885909155579569)
                ·
                  refine ⟨1903528013914431866684677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2538037351885909155579569 1903528013914431866684677)
                  ·
                    refine ⟨356911502608955975003377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903528013914431866684677 356911502608955975003377)
                    ·
                      rfl

theorem cell22_1042624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_1042624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042624 prefixEnd_1042624 := by exact prefixLift 1042624
  have htrace : WordTrace (prefixWord ++ tailWord_1042624) baseStart_1042624 baseEnd_1042624 := by
    simpa [prefixWord, tailWord_1042624, baseEnd_1042624] using wordTrace_append hprefix tailTrace_1042624
  have hstable : (prefixWord ++ tailWord_1042624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042624).length < 2 ^ (prefixWord ++ tailWord_1042624).sum := by decide
  have hdescent : baseEnd_1042624 < baseStart_1042624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042626 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1042626 : Nat := 118140960795 + 1042626 * 2 ^ 59
def prefixEnd_1042626 : Nat := 4983230072969 + 3 ^ 40 * 1042626 * 2
def baseEnd_1042626 : Nat := 356912187249828636453371

theorem tailTrace_1042626 : CollatzResearch.WordTrace tailWord_1042626 prefixEnd_1042626 356912187249828636453371 := by
  unfold tailWord_1042626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9506923580187885797330933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25351796213834362126215821 9506923580187885797330933)
  ·
    refine ⟨891274085642614293499775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9506923580187885797330933 891274085642614293499775)
    ·
      refine ⟨1336911128463921440249663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 891274085642614293499775 1336911128463921440249663)
      ·
        refine ⟨2005366692695882160374495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336911128463921440249663 2005366692695882160374495)
        ·
          refine ⟨3008050039043823240561743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005366692695882160374495 3008050039043823240561743)
          ·
            refine ⟨4512075058565734860842615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008050039043823240561743 4512075058565734860842615)
            ·
              refine ⟨6768112587848602291263923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512075058565734860842615 6768112587848602291263923)
              ·
                refine ⟨10152168881772903436895885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768112587848602291263923 10152168881772903436895885)
                ·
                  refine ⟨3807063330664838788835957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10152168881772903436895885 3807063330664838788835957)
                  ·
                    refine ⟨356912187249828636453371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3807063330664838788835957 356912187249828636453371)
                    ·
                      rfl

theorem cell22_1042626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1042626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042626 prefixEnd_1042626 := by exact prefixLift 1042626
  have htrace : WordTrace (prefixWord ++ tailWord_1042626) baseStart_1042626 baseEnd_1042626 := by
    simpa [prefixWord, tailWord_1042626, baseEnd_1042626] using wordTrace_append hprefix tailTrace_1042626
  have hstable : (prefixWord ++ tailWord_1042626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042626).length < 2 ^ (prefixWord ++ tailWord_1042626).sum := by decide
  have hdescent : baseEnd_1042626 < baseStart_1042626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042645 : List Nat := [1, 3, 2, 4, 3, 1, 2, 2, 4]
def baseStart_1042645 : Nat := 118140960795 + 1042645 * 2 ^ 59
def prefixEnd_1042645 : Nat := 4983230072969 + 3 ^ 40 * 1042645 * 2
def baseEnd_1042645 : Nat := 118972897112706306742771

theorem tailTrace_1042645 : CollatzResearch.WordTrace tailWord_1042645 prefixEnd_1042645 118972897112706306742771 := by
  unfold tailWord_1042645
  simp only [CollatzResearch.WordTrace]
  refine ⟨38028387307682709434265389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25352258205121806289510259 38028387307682709434265389)
  ·
    refine ⟨14260645240381016037849521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38028387307682709434265389 14260645240381016037849521)
    ·
      refine ⟨10695483930285762028387141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14260645240381016037849521 10695483930285762028387141)
      ·
        refine ⟨2005403236928580380322589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10695483930285762028387141 2005403236928580380322589)
        ·
          refine ⟨752026213848217642620971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2005403236928580380322589 752026213848217642620971)
          ·
            refine ⟨1128039320772326463931457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752026213848217642620971 1128039320772326463931457)
            ·
              refine ⟨846029490579244847948593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128039320772326463931457 846029490579244847948593)
              ·
                refine ⟨634522117934433635961445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846029490579244847948593 634522117934433635961445)
                ·
                  refine ⟨118972897112706306742771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634522117934433635961445 118972897112706306742771)
                  ·
                    rfl

theorem cell22_1042645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_1042645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042645 prefixEnd_1042645 := by exact prefixLift 1042645
  have htrace : WordTrace (prefixWord ++ tailWord_1042645) baseStart_1042645 baseEnd_1042645 := by
    simpa [prefixWord, tailWord_1042645, baseEnd_1042645] using wordTrace_append hprefix tailTrace_1042645
  have hstable : (prefixWord ++ tailWord_1042645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042645).length < 2 ^ (prefixWord ++ tailWord_1042645).sum := by decide
  have hdescent : baseEnd_1042645 < baseStart_1042645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042667 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 5]
def baseStart_1042667 : Nat := 118140960795 + 1042667 * 2 ^ 59
def prefixEnd_1042667 : Nat := 4983230072969 + 3 ^ 40 * 1042667 * 2
def baseEnd_1042667 : Nat := 118975407462572732059415

theorem tailTrace_1042667 : CollatzResearch.WordTrace tailWord_1042667 prefixEnd_1042667 118975407462572732059415 := by
  unfold tailWord_1042667
  simp only [CollatzResearch.WordTrace]
  refine ⟨38029189713603007191566255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25352793142402004794377503 38029189713603007191566255)
  ·
    refine ⟨57043784570404510787349383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38029189713603007191566255 57043784570404510787349383)
    ·
      refine ⟨85565676855606766181024075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57043784570404510787349383 85565676855606766181024075)
      ·
        refine ⟨128348515283410149271536113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85565676855606766181024075 128348515283410149271536113)
        ·
          refine ⟨96261386462557611953652085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128348515283410149271536113 96261386462557611953652085)
          ·
            refine ⟨9024504980864776120654883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96261386462557611953652085 9024504980864776120654883)
            ·
              refine ⟨13536757471297164180982325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9024504980864776120654883 13536757471297164180982325)
              ·
                refine ⟨1269071012934109141967093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13536757471297164180982325 1269071012934109141967093)
                ·
                  refine ⟨118975407462572732059415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1269071012934109141967093 118975407462572732059415)
                  ·
                    rfl

theorem cell22_1042667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 5].length) (baseStart_1042667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042667 prefixEnd_1042667 := by exact prefixLift 1042667
  have htrace : WordTrace (prefixWord ++ tailWord_1042667) baseStart_1042667 baseEnd_1042667 := by
    simpa [prefixWord, tailWord_1042667, baseEnd_1042667] using wordTrace_append hprefix tailTrace_1042667
  have hstable : (prefixWord ++ tailWord_1042667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042667).length < 2 ^ (prefixWord ++ tailWord_1042667).sum := by decide
  have hdescent : baseEnd_1042667 < baseStart_1042667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042744 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 4, 3]
def baseStart_1042744 : Nat := 118140960795 + 1042744 * 2 ^ 59
def prefixEnd_1042744 : Nat := 4983230072969 + 3 ^ 40 * 1042744 * 2
def baseEnd_1042744 : Nat := 356952581061315662003009

theorem tailTrace_1042744 : CollatzResearch.WordTrace tailWord_1042744 prefixEnd_1042744 356952581061315662003009 := by
  unfold tailWord_1042744
  simp only [CollatzResearch.WordTrace]
  refine ⟨19015999067162024671059643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25354665422882699561412857 19015999067162024671059643)
  ·
    refine ⟨28523998600743037006589465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19015999067162024671059643 28523998600743037006589465)
    ·
      refine ⟨21392998950557277754942099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28523998600743037006589465 21392998950557277754942099)
      ·
        refine ⟨32089498425835916632413149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21392998950557277754942099 32089498425835916632413149)
        ·
          refine ⟨12033561909688468737154931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32089498425835916632413149 12033561909688468737154931)
          ·
            refine ⟨18050342864532703105732397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12033561909688468737154931 18050342864532703105732397)
            ·
              refine ⟨6768878574199763664649649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18050342864532703105732397 6768878574199763664649649)
              ·
                refine ⟨5076658930649822748487237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6768878574199763664649649 5076658930649822748487237)
                ·
                  refine ⟨951873549496841765341357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5076658930649822748487237 951873549496841765341357)
                  ·
                    refine ⟨356952581061315662003009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 951873549496841765341357 356952581061315662003009)
                    ·
                      rfl

theorem cell22_1042744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_1042744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042744 prefixEnd_1042744 := by exact prefixLift 1042744
  have htrace : WordTrace (prefixWord ++ tailWord_1042744) baseStart_1042744 baseEnd_1042744 := by
    simpa [prefixWord, tailWord_1042744, baseEnd_1042744] using wordTrace_append hprefix tailTrace_1042744
  have hstable : (prefixWord ++ tailWord_1042744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042744).length < 2 ^ (prefixWord ++ tailWord_1042744).sum := by decide
  have hdescent : baseEnd_1042744 < baseStart_1042744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042746 : List Nat := [3, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_1042746 : Nat := 118140960795 + 1042746 * 2 ^ 59
def prefixEnd_1042746 : Nat := 4983230072969 + 3 ^ 40 * 1042746 * 2
def baseEnd_1042746 : Nat := 118984421900729441151001

theorem tailTrace_1042746 : CollatzResearch.WordTrace tailWord_1042746 prefixEnd_1042746 118984421900729441151001 := by
  unfold tailWord_1042746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9508017770079200920923023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25354714053544535789128061 9508017770079200920923023)
  ·
    refine ⟨14262026655118801381384535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9508017770079200920923023 14262026655118801381384535)
    ·
      refine ⟨21393039982678202072076803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14262026655118801381384535 21393039982678202072076803)
      ·
        refine ⟨32089559974017303108115205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21393039982678202072076803 32089559974017303108115205)
        ·
          refine ⟨6016792495128244332771601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32089559974017303108115205 6016792495128244332771601)
          ·
            refine ⟨4512594371346183249578701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6016792495128244332771601 4512594371346183249578701)
            ·
              refine ⟨1692222889254818718592013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4512594371346183249578701 1692222889254818718592013)
              ·
                refine ⟨634583583470557019472005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1692222889254818718592013 634583583470557019472005)
                ·
                  refine ⟨118984421900729441151001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634583583470557019472005 118984421900729441151001)
                  ·
                    rfl

theorem cell22_1042746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_1042746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042746 prefixEnd_1042746 := by exact prefixLift 1042746
  have htrace : WordTrace (prefixWord ++ tailWord_1042746) baseStart_1042746 baseEnd_1042746 := by
    simpa [prefixWord, tailWord_1042746, baseEnd_1042746] using wordTrace_append hprefix tailTrace_1042746
  have hstable : (prefixWord ++ tailWord_1042746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042746).length < 2 ^ (prefixWord ++ tailWord_1042746).sum := by decide
  have hdescent : baseEnd_1042746 < baseStart_1042746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042759 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1042759 : Nat := 118140960795 + 1042759 * 2 ^ 59
def prefixEnd_1042759 : Nat := 4983230072969 + 3 ^ 40 * 1042759 * 2
def baseEnd_1042759 : Nat := 356957715867860622877963

theorem tailTrace_1042759 : CollatzResearch.WordTrace tailWord_1042759 prefixEnd_1042759 356957715867860622877963 := by
  unfold tailWord_1042759
  simp only [CollatzResearch.WordTrace]
  refine ⟨38032545229269706903915331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25355030152846471269276887 38032545229269706903915331)
  ·
    refine ⟨57048817843904560355872997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38032545229269706903915331 57048817843904560355872997)
    ·
      refine ⟨10696653345732105066726187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57048817843904560355872997 10696653345732105066726187)
      ·
        refine ⟨16044980018598157600089281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10696653345732105066726187 16044980018598157600089281)
        ·
          refine ⟨12033735013948618200066961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16044980018598157600089281 12033735013948618200066961)
          ·
            refine ⟨9025301260461463650050221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12033735013948618200066961 9025301260461463650050221)
            ·
              refine ⟨3384487972673048868768833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9025301260461463650050221 3384487972673048868768833)
              ·
                refine ⟨2538365979504786651576625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3384487972673048868768833 2538365979504786651576625)
                ·
                  refine ⟨1903774484628589988682469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2538365979504786651576625 1903774484628589988682469)
                  ·
                    refine ⟨356957715867860622877963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903774484628589988682469 356957715867860622877963)
                    ·
                      rfl

theorem cell22_1042759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1042759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042759 prefixEnd_1042759 := by exact prefixLift 1042759
  have htrace : WordTrace (prefixWord ++ tailWord_1042759) baseStart_1042759 baseEnd_1042759 := by
    simpa [prefixWord, tailWord_1042759, baseEnd_1042759] using wordTrace_append hprefix tailTrace_1042759
  have hstable : (prefixWord ++ tailWord_1042759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042759).length < 2 ^ (prefixWord ++ tailWord_1042759).sum := by decide
  have hdescent : baseEnd_1042759 < baseStart_1042759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042782 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1042782 : Nat := 118140960795 + 1042782 * 2 ^ 59
def prefixEnd_1042782 : Nat := 4983230072969 + 3 ^ 40 * 1042782 * 2
def baseEnd_1042782 : Nat := 356965589237896229552893

theorem tailTrace_1042782 : CollatzResearch.WordTrace tailWord_1042782 prefixEnd_1042782 356965589237896229552893 := by
  unfold tailWord_1042782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754173013523297729000325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25355589405457587888001733 4754173013523297729000325)
  ·
    refine ⟨891407440035618324187561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4754173013523297729000325 891407440035618324187561)
    ·
      refine ⟨668555580026713743140671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 891407440035618324187561 668555580026713743140671)
      ·
        refine ⟨1002833370040070614711007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668555580026713743140671 1002833370040070614711007)
        ·
          refine ⟨1504250055060105922066511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002833370040070614711007 1504250055060105922066511)
          ·
            refine ⟨2256375082590158883099767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504250055060105922066511 2256375082590158883099767)
            ·
              refine ⟨3384562623885238324649651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256375082590158883099767 3384562623885238324649651)
              ·
                refine ⟨5076843935827857486974477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384562623885238324649651 5076843935827857486974477)
                ·
                  refine ⟨1903816475935446557615429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5076843935827857486974477 1903816475935446557615429)
                  ·
                    refine ⟨356965589237896229552893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903816475935446557615429 356965589237896229552893)
                    ·
                      rfl

theorem cell22_1042782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1042782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042782 prefixEnd_1042782 := by exact prefixLift 1042782
  have htrace : WordTrace (prefixWord ++ tailWord_1042782) baseStart_1042782 baseEnd_1042782 := by
    simpa [prefixWord, tailWord_1042782, baseEnd_1042782] using wordTrace_append hprefix tailTrace_1042782
  have hstable : (prefixWord ++ tailWord_1042782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042782).length < 2 ^ (prefixWord ++ tailWord_1042782).sum := by decide
  have hdescent : baseEnd_1042782 < baseStart_1042782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042823 : List Nat := [1, 1, 4, 2, 2, 1, 3, 4, 1, 3]
def baseStart_1042823 : Nat := 118140960795 + 1042823 * 2 ^ 59
def prefixEnd_1042823 : Nat := 4983230072969 + 3 ^ 40 * 1042823 * 2
def baseEnd_1042823 : Nat := 356979624375785789277767

theorem tailTrace_1042823 : CollatzResearch.WordTrace tailWord_1042823 prefixEnd_1042823 356979624375785789277767 := by
  unfold tailWord_1042823
  simp only [CollatzResearch.WordTrace]
  refine ⟨38034879501037845834245123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25356586334025230556163415 38034879501037845834245123)
  ·
    refine ⟨57052319251556768751367685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38034879501037845834245123 57052319251556768751367685)
    ·
      refine ⟨10697309859666894140881441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57052319251556768751367685 10697309859666894140881441)
      ·
        refine ⟨8022982394750170605661081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10697309859666894140881441 8022982394750170605661081)
        ·
          refine ⟨6017236796062627954245811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8022982394750170605661081 6017236796062627954245811)
          ·
            refine ⟨9025855194093941931368717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017236796062627954245811 9025855194093941931368717)
            ·
              refine ⟨3384695697785228224263269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9025855194093941931368717 3384695697785228224263269)
              ·
                refine ⟨634630443334730292049363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3384695697785228224263269 634630443334730292049363)
                ·
                  refine ⟨951945665002095438074045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634630443334730292049363 951945665002095438074045)
                  ·
                    refine ⟨356979624375785789277767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 951945665002095438074045 356979624375785789277767)
                    ·
                      rfl

theorem cell22_1042823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_1042823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042823 prefixEnd_1042823 := by exact prefixLift 1042823
  have htrace : WordTrace (prefixWord ++ tailWord_1042823) baseStart_1042823 baseEnd_1042823 := by
    simpa [prefixWord, tailWord_1042823, baseEnd_1042823] using wordTrace_append hprefix tailTrace_1042823
  have hstable : (prefixWord ++ tailWord_1042823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042823).length < 2 ^ (prefixWord ++ tailWord_1042823).sum := by decide
  have hdescent : baseEnd_1042823 < baseStart_1042823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042866 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1042866 : Nat := 118140960795 + 1042866 * 2 ^ 59
def prefixEnd_1042866 : Nat := 4983230072969 + 3 ^ 40 * 1042866 * 2
def baseEnd_1042866 : Nat := 356994344154548010452635

theorem tailTrace_1042866 : CollatzResearch.WordTrace tailWord_1042866 prefixEnd_1042866 356994344154548010452635 := by
  unfold tailWord_1042866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9509111959970516044515113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25357631893254709452040301 9509111959970516044515113)
  ·
    refine ⟨7131833969977887033386335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9509111959970516044515113 7131833969977887033386335)
    ·
      refine ⟨10697750954966830550079503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7131833969977887033386335 10697750954966830550079503)
      ·
        refine ⟨16046626432450245825119255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10697750954966830550079503 16046626432450245825119255)
        ·
          refine ⟨24069939648675368737678883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16046626432450245825119255 24069939648675368737678883)
          ·
            refine ⟨36104909473013053106518325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24069939648675368737678883 36104909473013053106518325)
            ·
              refine ⟨3384835263094973728736093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36104909473013053106518325 3384835263094973728736093)
              ·
                refine ⟨1269313223660615148276035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3384835263094973728736093 1269313223660615148276035)
                ·
                  refine ⟨1903969835490922722414053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269313223660615148276035 1903969835490922722414053)
                  ·
                    refine ⟨356994344154548010452635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1903969835490922722414053 356994344154548010452635)
                    ·
                      rfl

theorem cell22_1042866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1042866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042866 prefixEnd_1042866 := by exact prefixLift 1042866
  have htrace : WordTrace (prefixWord ++ tailWord_1042866) baseStart_1042866 baseEnd_1042866 := by
    simpa [prefixWord, tailWord_1042866, baseEnd_1042866] using wordTrace_append hprefix tailTrace_1042866
  have hstable : (prefixWord ++ tailWord_1042866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042866).length < 2 ^ (prefixWord ++ tailWord_1042866).sum := by decide
  have hdescent : baseEnd_1042866 < baseStart_1042866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042915 : List Nat := [1, 1, 1, 6, 3, 2, 1, 3, 4]
def baseStart_1042915 : Nat := 118140960795 + 1042915 * 2 ^ 59
def prefixEnd_1042915 : Nat := 4983230072969 + 3 ^ 40 * 1042915 * 2
def baseEnd_1042915 : Nat := 119003705951976071992495

theorem tailTrace_1042915 : CollatzResearch.WordTrace tailWord_1042915 prefixEnd_1042915 119003705951976071992495 := by
  unfold tailWord_1042915
  simp only [CollatzResearch.WordTrace]
  refine ⟨38038235016704545546594199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25358823344469697031062799 38038235016704545546594199)
  ·
    refine ⟨57057352525056818319891299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38038235016704545546594199 57057352525056818319891299)
    ·
      refine ⟨85586028787585227479836949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57057352525056818319891299 85586028787585227479836949)
      ·
        refine ⟨4011845099418057538117357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85586028787585227479836949 4011845099418057538117357)
        ·
          refine ⟨1504441912281771576794009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4011845099418057538117357 1504441912281771576794009)
          ·
            refine ⟨1128331434211328682595507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1504441912281771576794009 1128331434211328682595507)
            ·
              refine ⟨1692497151316993023893261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128331434211328682595507 1692497151316993023893261)
              ·
                refine ⟨634686431743872383959973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1692497151316993023893261 634686431743872383959973)
                ·
                  refine ⟨119003705951976071992495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634686431743872383959973 119003705951976071992495)
                  ·
                    rfl

theorem cell22_1042915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 4].length) (baseStart_1042915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042915 prefixEnd_1042915 := by exact prefixLift 1042915
  have htrace : WordTrace (prefixWord ++ tailWord_1042915) baseStart_1042915 baseEnd_1042915 := by
    simpa [prefixWord, tailWord_1042915, baseEnd_1042915] using wordTrace_append hprefix tailTrace_1042915
  have hstable : (prefixWord ++ tailWord_1042915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042915).length < 2 ^ (prefixWord ++ tailWord_1042915).sum := by decide
  have hdescent : baseEnd_1042915 < baseStart_1042915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042926 : List Nat := [4, 1, 2, 1, 2, 4, 8]
def baseStart_1042926 : Nat := 118140960795 + 1042926 * 2 ^ 59
def prefixEnd_1042926 : Nat := 4983230072969 + 3 ^ 40 * 1042926 * 2
def baseEnd_1042926 : Nat := 13222773458545476072313

theorem tailTrace_1042926 : CollatzResearch.WordTrace tailWord_1042926 prefixEnd_1042926 13222773458545476072313 := by
  unfold tailWord_1042926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754829527458086803155579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25359090813109796283496421 4754829527458086803155579)
  ·
    refine ⟨7132244291187130204733369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4754829527458086803155579 7132244291187130204733369)
    ·
      refine ⟨5349183218390347653550027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7132244291187130204733369 5349183218390347653550027)
      ·
        refine ⟨8023774827585521480325041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5349183218390347653550027 8023774827585521480325041)
        ·
          refine ⟨6017831120689141110243781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8023774827585521480325041 6017831120689141110243781)
          ·
            refine ⟨1128343335129213958170709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6017831120689141110243781 1128343335129213958170709)
            ·
              refine ⟨13222773458545476072313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1128343335129213958170709 13222773458545476072313)
              ·
                rfl

theorem cell22_1042926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 8].length) (baseStart_1042926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042926 prefixEnd_1042926 := by exact prefixLift 1042926
  have htrace : WordTrace (prefixWord ++ tailWord_1042926) baseStart_1042926 baseEnd_1042926 := by
    simpa [prefixWord, tailWord_1042926, baseEnd_1042926] using wordTrace_append hprefix tailTrace_1042926
  have hstable : (prefixWord ++ tailWord_1042926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042926).length < 2 ^ (prefixWord ++ tailWord_1042926).sum := by decide
  have hdescent : baseEnd_1042926 < baseStart_1042926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042969 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_1042969 : Nat := 118140960795 + 1042969 * 2 ^ 59
def prefixEnd_1042969 : Nat := 4983230072969 + 3 ^ 40 * 1042969 * 2
def baseEnd_1042969 : Nat := 357029603159490075127319

theorem tailTrace_1042969 : CollatzResearch.WordTrace tailWord_1042969 prefixEnd_1042969 357029603159490075127319 := by
  unfold tailWord_1042969
  simp only [CollatzResearch.WordTrace]
  refine ⟨38040204558508912769059961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25360136372339275179373307 38040204558508912769059961)
  ·
    refine ⟨28530153418881684576794971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38040204558508912769059961 28530153418881684576794971)
    ·
      refine ⟨42795230128322526865192457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28530153418881684576794971 42795230128322526865192457)
      ·
        refine ⟨32096422596241895148894343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42795230128322526865192457 32096422596241895148894343)
        ·
          refine ⟨48144633894362842723341515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32096422596241895148894343 48144633894362842723341515)
          ·
            refine ⟨72216950841544264085012273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48144633894362842723341515 72216950841544264085012273)
            ·
              refine ⟨54162713131158198063759205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72216950841544264085012273 54162713131158198063759205)
              ·
                refine ⟨10155508712092162136954851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54162713131158198063759205 10155508712092162136954851)
                ·
                  refine ⟨15233263068138243205432277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10155508712092162136954851 15233263068138243205432277)
                  ·
                    refine ⟨357029603159490075127319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15233263068138243205432277 357029603159490075127319)
                    ·
                      rfl

theorem cell22_1042969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_1042969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1042969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1042969 prefixEnd_1042969 := by exact prefixLift 1042969
  have htrace : WordTrace (prefixWord ++ tailWord_1042969) baseStart_1042969 baseEnd_1042969 := by
    simpa [prefixWord, tailWord_1042969, baseEnd_1042969] using wordTrace_append hprefix tailTrace_1042969
  have hstable : (prefixWord ++ tailWord_1042969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042969).length < 2 ^ (prefixWord ++ tailWord_1042969).sum := by decide
  have hdescent : baseEnd_1042969 < baseStart_1042969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043001 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_1043001 : Nat := 118140960795 + 1043001 * 2 ^ 59
def prefixEnd_1043001 : Nat := 4983230072969 + 3 ^ 40 * 1043001 * 2
def baseEnd_1043001 : Nat := 357040557413452658327221

theorem tailTrace_1043001 : CollatzResearch.WordTrace tailWord_1043001 prefixEnd_1043001 357040557413452658327221 := by
  unfold tailWord_1043001
  simp only [CollatzResearch.WordTrace]
  refine ⟨38041371694392982234224857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25360914462928654822816571 38041371694392982234224857)
  ·
    refine ⟨28531028770794736675668643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38041371694392982234224857 28531028770794736675668643)
    ·
      refine ⟨42796543156192105013502965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28531028770794736675668643 42796543156192105013502965)
      ·
        refine ⟨4012175920893009845015903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42796543156192105013502965 4012175920893009845015903)
        ·
          refine ⟨6018263881339514767523855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012175920893009845015903 6018263881339514767523855)
          ·
            refine ⟨9027395822009272151285783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018263881339514767523855 9027395822009272151285783)
            ·
              refine ⟨13541093733013908226928675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027395822009272151285783 13541093733013908226928675)
              ·
                refine ⟨20311640599520862340393013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13541093733013908226928675 20311640599520862340393013)
                ·
                  refine ⟨1904216306205080844411845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20311640599520862340393013 1904216306205080844411845)
                  ·
                    refine ⟨357040557413452658327221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1904216306205080844411845 357040557413452658327221)
                    ·
                      rfl

theorem cell22_1043001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_1043001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043001 prefixEnd_1043001 := by exact prefixLift 1043001
  have htrace : WordTrace (prefixWord ++ tailWord_1043001) baseStart_1043001 baseEnd_1043001 := by
    simpa [prefixWord, tailWord_1043001, baseEnd_1043001] using wordTrace_append hprefix tailTrace_1043001
  have hstable : (prefixWord ++ tailWord_1043001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043001).length < 2 ^ (prefixWord ++ tailWord_1043001).sum := by decide
  have hdescent : baseEnd_1043001 < baseStart_1043001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043031 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 1, 5]
def baseStart_1043031 : Nat := 118140960795 + 1043031 * 2 ^ 59
def prefixEnd_1043031 : Nat := 4983230072969 + 3 ^ 40 * 1043031 * 2
def baseEnd_1043031 : Nat := 357050827026542580077129

theorem tailTrace_1043031 : CollatzResearch.WordTrace tailWord_1043031 prefixEnd_1043031 357050827026542580077129 := by
  unfold tailWord_1043031
  simp only [CollatzResearch.WordTrace]
  refine ⟨38042465884284297357816947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25361643922856198238544631 38042465884284297357816947)
  ·
    refine ⟨57063698826426446036725421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38042465884284297357816947 57063698826426446036725421)
    ·
      refine ⟨21398887059909917263772033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57063698826426446036725421 21398887059909917263772033)
      ·
        refine ⟨16049165294932437947829025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21398887059909917263772033 16049165294932437947829025)
        ·
          refine ⟨12036873971199328460871769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16049165294932437947829025 12036873971199328460871769)
          ·
            refine ⟨9027655478399496345653827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12036873971199328460871769 9027655478399496345653827)
            ·
              refine ⟨13541483217599244518480741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027655478399496345653827 13541483217599244518480741)
              ·
                refine ⟨2539028103299858347215139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13541483217599244518480741 2539028103299858347215139)
                ·
                  refine ⟨3808542154949787520822709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539028103299858347215139 3808542154949787520822709)
                  ·
                    refine ⟨357050827026542580077129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3808542154949787520822709 357050827026542580077129)
                    ·
                      rfl

theorem cell22_1043031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_1043031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043031 prefixEnd_1043031 := by exact prefixLift 1043031
  have htrace : WordTrace (prefixWord ++ tailWord_1043031) baseStart_1043031 baseEnd_1043031 := by
    simpa [prefixWord, tailWord_1043031, baseEnd_1043031] using wordTrace_append hprefix tailTrace_1043031
  have hstable : (prefixWord ++ tailWord_1043031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043031).length < 2 ^ (prefixWord ++ tailWord_1043031).sum := by decide
  have hdescent : baseEnd_1043031 < baseStart_1043031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043123 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 5]
def baseStart_1043123 : Nat := 118140960795 + 1043123 * 2 ^ 59
def prefixEnd_1043123 : Nat := 4983230072969 + 3 ^ 40 * 1043123 * 2
def baseEnd_1043123 : Nat := 119027440168895002258949

theorem tailTrace_1043123 : CollatzResearch.WordTrace tailWord_1043123 prefixEnd_1043123 119027440168895002258949 := by
  unfold tailWord_1043123
  simp only [CollatzResearch.WordTrace]
  refine ⟨38045821399950997070166023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25363880933300664713444015 38045821399950997070166023)
  ·
    refine ⟨57068732099926495605249035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38045821399950997070166023 57068732099926495605249035)
    ·
      refine ⟨85603098149889743407873553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57068732099926495605249035 85603098149889743407873553)
      ·
        refine ⟨64202323612417307555905165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85603098149889743407873553 64202323612417307555905165)
        ·
          refine ⟨24075871354656490333464437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64202323612417307555905165 24075871354656490333464437)
          ·
            refine ⟨2257112939499045968762291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24075871354656490333464437 2257112939499045968762291)
            ·
              refine ⟨3385669409248568953143437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257112939499045968762291 3385669409248568953143437)
              ·
                refine ⟨1269626028468213357428789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3385669409248568953143437 1269626028468213357428789)
                ·
                  refine ⟨119027440168895002258949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1269626028468213357428789 119027440168895002258949)
                  ·
                    rfl

theorem cell22_1043123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 5].length) (baseStart_1043123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043123 prefixEnd_1043123 := by exact prefixLift 1043123
  have htrace : WordTrace (prefixWord ++ tailWord_1043123) baseStart_1043123 baseEnd_1043123 := by
    simpa [prefixWord, tailWord_1043123, baseEnd_1043123] using wordTrace_append hprefix tailTrace_1043123
  have hstable : (prefixWord ++ tailWord_1043123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043123).length < 2 ^ (prefixWord ++ tailWord_1043123).sum := by decide
  have hdescent : baseEnd_1043123 < baseStart_1043123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043157 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 5]
def baseStart_1043157 : Nat := 118140960795 + 1043157 * 2 ^ 59
def prefixEnd_1043157 : Nat := 4983230072969 + 3 ^ 40 * 1043157 * 2
def baseEnd_1043157 : Nat := 119031319800506750475581

theorem tailTrace_1043157 : CollatzResearch.WordTrace tailWord_1043157 prefixEnd_1043157 119031319800506750475581 := by
  unfold tailWord_1043157
  simp only [CollatzResearch.WordTrace]
  refine ⟨38047061481827820876903725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25364707654551880584602483 38047061481827820876903725)
  ·
    refine ⟨14267648055685432828838897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38047061481827820876903725 14267648055685432828838897)
    ·
      refine ⟨10700736041764074621629173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14267648055685432828838897 10700736041764074621629173)
      ·
        refine ⟨1003194003915381995777735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10700736041764074621629173 1003194003915381995777735)
        ·
          refine ⟨1504791005873072993666603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003194003915381995777735 1504791005873072993666603)
          ·
            refine ⟨2257186508809609490499905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504791005873072993666603 2257186508809609490499905)
            ·
              refine ⟨1692889881607207117874929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2257186508809609490499905 1692889881607207117874929)
              ·
                refine ⟨1269667411205405338406197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692889881607207117874929 1269667411205405338406197)
                ·
                  refine ⟨119031319800506750475581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1269667411205405338406197 119031319800506750475581)
                  ·
                    rfl

theorem cell22_1043157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_1043157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043157 prefixEnd_1043157 := by exact prefixLift 1043157
  have htrace : WordTrace (prefixWord ++ tailWord_1043157) baseStart_1043157 baseEnd_1043157 := by
    simpa [prefixWord, tailWord_1043157, baseEnd_1043157] using wordTrace_append hprefix tailTrace_1043157
  have hstable : (prefixWord ++ tailWord_1043157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043157).length < 2 ^ (prefixWord ++ tailWord_1043157).sum := by decide
  have hdescent : baseEnd_1043157 < baseStart_1043157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043183 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 1, 5]
def baseStart_1043183 : Nat := 118140960795 + 1043183 * 2 ^ 59
def prefixEnd_1043183 : Nat := 4983230072969 + 3 ^ 40 * 1043183 * 2
def baseEnd_1043183 : Nat := 357102859732864850276663

theorem tailTrace_1043183 : CollatzResearch.WordTrace tailWord_1043183 prefixEnd_1043183 357102859732864850276663 := by
  unfold tailWord_1043183
  simp only [CollatzResearch.WordTrace]
  refine ⟨38048009779733627317350203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25365339853155751544900135 38048009779733627317350203)
  ·
    refine ⟨57072014669600440976025305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38048009779733627317350203 57072014669600440976025305)
    ·
      refine ⟨42804011002200330732018979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57072014669600440976025305 42804011002200330732018979)
      ·
        refine ⟨64206016503300496098028469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42804011002200330732018979 64206016503300496098028469)
        ·
          refine ⟨6019314047184421509190169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64206016503300496098028469 6019314047184421509190169)
          ·
            refine ⟨4514485535388316131892627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6019314047184421509190169 4514485535388316131892627)
            ·
              refine ⟨6771728303082474197838941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514485535388316131892627 6771728303082474197838941)
              ·
                refine ⟨2539398113655927824189603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6771728303082474197838941 2539398113655927824189603)
                ·
                  refine ⟨3809097170483891736284405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539398113655927824189603 3809097170483891736284405)
                  ·
                    refine ⟨357102859732864850276663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3809097170483891736284405 357102859732864850276663)
                    ·
                      rfl

theorem cell22_1043183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_1043183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043183 prefixEnd_1043183 := by exact prefixLift 1043183
  have htrace : WordTrace (prefixWord ++ tailWord_1043183) baseStart_1043183 baseEnd_1043183 := by
    simpa [prefixWord, tailWord_1043183, baseEnd_1043183] using wordTrace_append hprefix tailTrace_1043183
  have hstable : (prefixWord ++ tailWord_1043183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043183).length < 2 ^ (prefixWord ++ tailWord_1043183).sum := by decide
  have hdescent : baseEnd_1043183 < baseStart_1043183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043202 : List Nat := [3, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1043202 : Nat := 118140960795 + 1043202 * 2 ^ 59
def prefixEnd_1043202 : Nat := 4983230072969 + 3 ^ 40 * 1043202 * 2
def baseEnd_1043202 : Nat := 119036454607051711350535

theorem tailTrace_1043202 : CollatzResearch.WordTrace tailWord_1043202 prefixEnd_1043202 119036454607051711350535 := by
  unfold tailWord_1043202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9512175691666198390572965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25365801844443195708194573 9512175691666198390572965)
  ·
    refine ⟨1783532942187412198232431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9512175691666198390572965 1783532942187412198232431)
    ·
      refine ⟨2675299413281118297348647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783532942187412198232431 2675299413281118297348647)
      ·
        refine ⟨4012949119921677446022971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675299413281118297348647 4012949119921677446022971)
        ·
          refine ⟨6019423679882516169034457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012949119921677446022971 6019423679882516169034457)
          ·
            refine ⟨4514567759911887126775843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6019423679882516169034457 4514567759911887126775843)
            ·
              refine ⟨6771851639867830690163765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514567759911887126775843 6771851639867830690163765)
              ·
                refine ⟨634861091237609127202853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6771851639867830690163765 634861091237609127202853)
                ·
                  refine ⟨119036454607051711350535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634861091237609127202853 119036454607051711350535)
                  ·
                    rfl

theorem cell22_1043202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1043202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043202 prefixEnd_1043202 := by exact prefixLift 1043202
  have htrace : WordTrace (prefixWord ++ tailWord_1043202) baseStart_1043202 baseEnd_1043202 := by
    simpa [prefixWord, tailWord_1043202, baseEnd_1043202] using wordTrace_append hprefix tailTrace_1043202
  have hstable : (prefixWord ++ tailWord_1043202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043202).length < 2 ^ (prefixWord ++ tailWord_1043202).sum := by decide
  have hdescent : baseEnd_1043202 < baseStart_1043202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043234 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1043234 : Nat := 118140960795 + 1043234 * 2 ^ 59
def prefixEnd_1043234 : Nat := 4983230072969 + 3 ^ 40 * 1043234 * 2
def baseEnd_1043234 : Nat := 357120318075117717251507

theorem tailTrace_1043234 : CollatzResearch.WordTrace tailWord_1043234 prefixEnd_1043234 357120318075117717251507 := by
  unfold tailWord_1043234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9512467475637215756864189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25366579935032575351637837 9512467475637215756864189)
  ·
    refine ⟨3567175303363955908824071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9512467475637215756864189 3567175303363955908824071)
    ·
      refine ⟨5350762955045933863236107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567175303363955908824071 5350762955045933863236107)
      ·
        refine ⟨8026144432568900794854161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5350762955045933863236107 8026144432568900794854161)
        ·
          refine ⟨6019608324426675596140621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8026144432568900794854161 6019608324426675596140621)
          ·
            refine ⟨2257353121660003348552733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6019608324426675596140621 2257353121660003348552733)
            ·
              refine ⟨846507420622501255707275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2257353121660003348552733 846507420622501255707275)
              ·
                refine ⟨1269761130933751883560913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846507420622501255707275 1269761130933751883560913)
                ·
                  refine ⟨952320848200313912670685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1269761130933751883560913 952320848200313912670685)
                  ·
                    refine ⟨357120318075117717251507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 952320848200313912670685 357120318075117717251507)
                    ·
                      rfl

theorem cell22_1043234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1043234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043234 prefixEnd_1043234 := by exact prefixLift 1043234
  have htrace : WordTrace (prefixWord ++ tailWord_1043234) baseStart_1043234 baseEnd_1043234 := by
    simpa [prefixWord, tailWord_1043234, baseEnd_1043234] using wordTrace_append hprefix tailTrace_1043234
  have hstable : (prefixWord ++ tailWord_1043234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043234).length < 2 ^ (prefixWord ++ tailWord_1043234).sum := by decide
  have hdescent : baseEnd_1043234 < baseStart_1043234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043292 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 5]
def baseStart_1043292 : Nat := 118140960795 + 1043292 * 2 ^ 59
def prefixEnd_1043292 : Nat := 4983230072969 + 3 ^ 40 * 1043292 * 2
def baseEnd_1043292 : Nat := 119046724220141633100443

theorem tailTrace_1043292 : CollatzResearch.WordTrace tailWord_1043292 prefixEnd_1043292 119046724220141633100443 := by
  unfold tailWord_1043292
  simp only [CollatzResearch.WordTrace]
  refine ⟨19025992668169369466534065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25367990224225825955378753 19025992668169369466534065)
  ·
    refine ⟨14269494501127027099900549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19025992668169369466534065 14269494501127027099900549)
    ·
      refine ⟨2675530218961317581231353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14269494501127027099900549 2675530218961317581231353)
      ·
        refine ⟨2006647664220988185923515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2675530218961317581231353 2006647664220988185923515)
        ·
          refine ⟨3009971496331482278885273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2006647664220988185923515 3009971496331482278885273)
          ·
            refine ⟨2257478622248611709163955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3009971496331482278885273 2257478622248611709163955)
            ·
              refine ⟨3386217933372917563745933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257478622248611709163955 3386217933372917563745933)
              ·
                refine ⟨1269831725014844086404725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3386217933372917563745933 1269831725014844086404725)
                ·
                  refine ⟨119046724220141633100443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1269831725014844086404725 119046724220141633100443)
                  ·
                    rfl

theorem cell22_1043292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_1043292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043292 prefixEnd_1043292 := by exact prefixLift 1043292
  have htrace : WordTrace (prefixWord ++ tailWord_1043292) baseStart_1043292 baseEnd_1043292 := by
    simpa [prefixWord, tailWord_1043292, baseEnd_1043292] using wordTrace_append hprefix tailTrace_1043292
  have hstable : (prefixWord ++ tailWord_1043292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043292).length < 2 ^ (prefixWord ++ tailWord_1043292).sum := by decide
  have hdescent : baseEnd_1043292 < baseStart_1043292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043337 : List Nat := [1, 2, 1, 1, 5, 3, 1, 4, 4]
def baseStart_1043337 : Nat := 118140960795 + 1043337 * 2 ^ 59
def prefixEnd_1043337 : Nat := 4983230072969 + 3 ^ 40 * 1043337 * 2
def baseEnd_1043337 : Nat := 119051859026686593975397

theorem tailTrace_1043337 : CollatzResearch.WordTrace tailWord_1043337 prefixEnd_1043337 119051859026686593975397 := by
  unfold tailWord_1043337
  simp only [CollatzResearch.WordTrace]
  refine ⟨38053626621175711618456265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25369084414117141078970843 38053626621175711618456265)
  ·
    refine ⟨28540219965881783713842199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38053626621175711618456265 28540219965881783713842199)
    ·
      refine ⟨42810329948822675570763299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28540219965881783713842199 42810329948822675570763299)
      ·
        refine ⟨64215494923234013356144949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42810329948822675570763299 64215494923234013356144949)
        ·
          refine ⟨6020202649053188752138589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64215494923234013356144949 6020202649053188752138589)
          ·
            refine ⟨2257575993394945782051971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6020202649053188752138589 2257575993394945782051971)
            ·
              refine ⟨3386363990092418673077957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257575993394945782051971 3386363990092418673077957)
              ·
                refine ⟨634943248142328501202117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3386363990092418673077957 634943248142328501202117)
                ·
                  refine ⟨119051859026686593975397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634943248142328501202117 119051859026686593975397)
                  ·
                    rfl

theorem cell22_1043337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 4].length) (baseStart_1043337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043337 prefixEnd_1043337 := by exact prefixLift 1043337
  have htrace : WordTrace (prefixWord ++ tailWord_1043337) baseStart_1043337 baseEnd_1043337 := by
    simpa [prefixWord, tailWord_1043337, baseEnd_1043337] using wordTrace_append hprefix tailTrace_1043337
  have hstable : (prefixWord ++ tailWord_1043337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043337).length < 2 ^ (prefixWord ++ tailWord_1043337).sum := by decide
  have hdescent : baseEnd_1043337 < baseStart_1043337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043367 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1043367 : Nat := 118140960795 + 1043367 * 2 ^ 59
def prefixEnd_1043367 : Nat := 4983230072969 + 3 ^ 40 * 1043367 * 2
def baseEnd_1043367 : Nat := 357165846693149703676099

theorem tailTrace_1043367 : CollatzResearch.WordTrace tailWord_1043367 prefixEnd_1043367 357165846693149703676099 := by
  unfold tailWord_1043367
  simp only [CollatzResearch.WordTrace]
  refine ⟨38054720811067026742048355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25369813874044684494698903 38054720811067026742048355)
  ·
    refine ⟨57082081216600540113072533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38054720811067026742048355 57082081216600540113072533)
    ·
      refine ⟨2675722557028150317800275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57082081216600540113072533 2675722557028150317800275)
      ·
        refine ⟨4013583835542225476700413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675722557028150317800275 4013583835542225476700413)
        ·
          refine ⟨1505093938328334553762655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4013583835542225476700413 1505093938328334553762655)
          ·
            refine ⟨2257640907492501830643983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505093938328334553762655 2257640907492501830643983)
            ·
              refine ⟨3386461361238752745965975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257640907492501830643983 3386461361238752745965975)
              ·
                refine ⟨5079692041858129118948963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386461361238752745965975 5079692041858129118948963)
                ·
                  refine ⟨7619538062787193678423445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079692041858129118948963 7619538062787193678423445)
                  ·
                    refine ⟨357165846693149703676099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7619538062787193678423445 357165846693149703676099)
                    ·
                      rfl

theorem cell22_1043367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1043367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043367 prefixEnd_1043367 := by exact prefixLift 1043367
  have htrace : WordTrace (prefixWord ++ tailWord_1043367) baseStart_1043367 baseEnd_1043367 := by
    simpa [prefixWord, tailWord_1043367, baseEnd_1043367] using wordTrace_append hprefix tailTrace_1043367
  have hstable : (prefixWord ++ tailWord_1043367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043367).length < 2 ^ (prefixWord ++ tailWord_1043367).sum := by decide
  have hdescent : baseEnd_1043367 < baseStart_1043367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043373 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1043373 : Nat := 118140960795 + 1043373 * 2 ^ 59
def prefixEnd_1043373 : Nat := 4983230072969 + 3 ^ 40 * 1043373 * 2
def baseEnd_1043373 : Nat := 357167900615767688026081

theorem tailTrace_1043373 : CollatzResearch.WordTrace tailWord_1043373 prefixEnd_1043373 357167900615767688026081 := by
  unfold tailWord_1043373
  simp only [CollatzResearch.WordTrace]
  refine ⟨38054939649045289766766773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25369959766030193177844515 38054939649045289766766773)
  ·
    refine ⟨3567650592097995915634385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38054939649045289766766773 3567650592097995915634385)
    ·
      refine ⟨2675737944073496936725789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3567650592097995915634385 2675737944073496936725789)
      ·
        refine ⟨1003401729027561351272171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2675737944073496936725789 1003401729027561351272171)
        ·
          refine ⟨1505102593541342026908257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003401729027561351272171 1505102593541342026908257)
          ·
            refine ⟨1128826945156006520181193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505102593541342026908257 1128826945156006520181193)
            ·
              refine ⟨846620208867004890135895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128826945156006520181193 846620208867004890135895)
              ·
                refine ⟨1269930313300507335203843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846620208867004890135895 1269930313300507335203843)
                ·
                  refine ⟨1904895469950761002805765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269930313300507335203843 1904895469950761002805765)
                  ·
                    refine ⟨357167900615767688026081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1904895469950761002805765 357167900615767688026081)
                    ·
                      rfl

theorem cell22_1043373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1043373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043373 prefixEnd_1043373 := by exact prefixLift 1043373
  have htrace : WordTrace (prefixWord ++ tailWord_1043373) baseStart_1043373 baseEnd_1043373 := by
    simpa [prefixWord, tailWord_1043373, baseEnd_1043373] using wordTrace_append hprefix tailTrace_1043373
  have hstable : (prefixWord ++ tailWord_1043373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043373).length < 2 ^ (prefixWord ++ tailWord_1043373).sum := by decide
  have hdescent : baseEnd_1043373 < baseStart_1043373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043431 : List Nat := [1, 1, 5, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1043431 : Nat := 118140960795 + 1043431 * 2 ^ 59
def prefixEnd_1043431 : Nat := 4983230072969 + 3 ^ 40 * 1043431 * 2
def baseEnd_1043431 : Nat := 357187755201074870075903

theorem tailTrace_1043431 : CollatzResearch.WordTrace tailWord_1043431 prefixEnd_1043431 357187755201074870075903 := by
  unfold tailWord_1043431
  simp only [CollatzResearch.WordTrace]
  refine ⟨38057055082835165672378147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25371370055223443781585431 38057055082835165672378147)
  ·
    refine ⟨57085582624252748508567221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38057055082835165672378147 57085582624252748508567221)
    ·
      refine ⟨5351773371023695172678177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57085582624252748508567221 5351773371023695172678177)
      ·
        refine ⟨4013830028267771379508633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5351773371023695172678177 4013830028267771379508633)
        ·
          refine ⟨3010372521200828534631475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4013830028267771379508633 3010372521200828534631475)
          ·
            refine ⟨4515558781801242801947213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010372521200828534631475 4515558781801242801947213)
            ·
              refine ⟨1693334543175466050730205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4515558781801242801947213 1693334543175466050730205)
              ·
                refine ⟨635000453690799769023827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1693334543175466050730205 635000453690799769023827)
                ·
                  refine ⟨952500680536199653535741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635000453690799769023827 952500680536199653535741)
                  ·
                    refine ⟨357187755201074870075903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 952500680536199653535741 357187755201074870075903)
                    ·
                      rfl

theorem cell22_1043431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1043431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043431 prefixEnd_1043431 := by exact prefixLift 1043431
  have htrace : WordTrace (prefixWord ++ tailWord_1043431) baseStart_1043431 baseEnd_1043431 := by
    simpa [prefixWord, tailWord_1043431, baseEnd_1043431] using wordTrace_append hprefix tailTrace_1043431
  have hstable : (prefixWord ++ tailWord_1043431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043431).length < 2 ^ (prefixWord ++ tailWord_1043431).sum := by decide
  have hdescent : baseEnd_1043431 < baseStart_1043431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043440 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_1043440 : Nat := 118140960795 + 1043440 * 2 ^ 59
def prefixEnd_1043440 : Nat := 4983230072969 + 3 ^ 40 * 1043440 * 2
def baseEnd_1043440 : Nat := 357190836085001846600875

theorem tailTrace_1043440 : CollatzResearch.WordTrace tailWord_1043440 prefixEnd_1043440 357190836085001846600875 := by
  unfold tailWord_1043440
  simp only [CollatzResearch.WordTrace]
  refine ⟨19028691669901280104727887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25371588893201706806303849 19028691669901280104727887)
  ·
    refine ⟨28543037504851920157091831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19028691669901280104727887 28543037504851920157091831)
    ·
      refine ⟨42814556257277880235637747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28543037504851920157091831 42814556257277880235637747)
      ·
        refine ⟨64221834385916820353456621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42814556257277880235637747 64221834385916820353456621)
        ·
          refine ⟨24083187894718807632546233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64221834385916820353456621 24083187894718807632546233)
          ·
            refine ⟨18062390921039105724409675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24083187894718807632546233 18062390921039105724409675)
            ·
              refine ⟨27093586381558658586614513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18062390921039105724409675 27093586381558658586614513)
              ·
                refine ⟨20320189786168993939960885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27093586381558658586614513 20320189786168993939960885)
                ·
                  refine ⟨1905017792453343181871333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20320189786168993939960885 1905017792453343181871333)
                  ·
                    refine ⟨357190836085001846600875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1905017792453343181871333 357190836085001846600875)
                    ·
                      rfl

theorem cell22_1043440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_1043440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043440 prefixEnd_1043440 := by exact prefixLift 1043440
  have htrace : WordTrace (prefixWord ++ tailWord_1043440) baseStart_1043440 baseEnd_1043440 := by
    simpa [prefixWord, tailWord_1043440, baseEnd_1043440] using wordTrace_append hprefix tailTrace_1043440
  have hstable : (prefixWord ++ tailWord_1043440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043440).length < 2 ^ (prefixWord ++ tailWord_1043440).sum := by decide
  have hdescent : baseEnd_1043440 < baseStart_1043440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043487 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 1, 5]
def baseStart_1043487 : Nat := 118140960795 + 1043487 * 2 ^ 59
def prefixEnd_1043487 : Nat := 4983230072969 + 3 ^ 40 * 1043487 * 2
def baseEnd_1043487 : Nat := 357206925145509390675731

theorem tailTrace_1043487 : CollatzResearch.WordTrace tailWord_1043487 prefixEnd_1043487 357206925145509390675731 := by
  unfold tailWord_1043487
  simp only [CollatzResearch.WordTrace]
  refine ⟨38059097570632287236416715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25372731713754858157611143 38059097570632287236416715)
  ·
    refine ⟨57088646355948430854625073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38059097570632287236416715 57088646355948430854625073)
    ·
      refine ⟨42816484766961323140968805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57088646355948430854625073 42816484766961323140968805)
      ·
        refine ⟨8028090893805248088931651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42816484766961323140968805 8028090893805248088931651)
        ·
          refine ⟨12042136340707872133397477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8028090893805248088931651 12042136340707872133397477)
          ·
            refine ⟨2257900563882726025012027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12042136340707872133397477 2257900563882726025012027)
            ·
              refine ⟨3386850845824089037518041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257900563882726025012027 3386850845824089037518041)
              ·
                refine ⟨2540138134368066778138531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386850845824089037518041 2540138134368066778138531)
                ·
                  refine ⟨3810207201552100167207797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540138134368066778138531 3810207201552100167207797)
                  ·
                    refine ⟨357206925145509390675731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3810207201552100167207797 357206925145509390675731)
                    ·
                      rfl

theorem cell22_1043487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_1043487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043487 prefixEnd_1043487 := by exact prefixLift 1043487
  have htrace : WordTrace (prefixWord ++ tailWord_1043487) baseStart_1043487 baseEnd_1043487 := by
    simpa [prefixWord, tailWord_1043487, baseEnd_1043487] using wordTrace_append hprefix tailTrace_1043487
  have hstable : (prefixWord ++ tailWord_1043487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043487).length < 2 ^ (prefixWord ++ tailWord_1043487).sum := by decide
  have hdescent : baseEnd_1043487 < baseStart_1043487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043504 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 2, 3]
def baseStart_1043504 : Nat := 118140960795 + 1043504 * 2 ^ 59
def prefixEnd_1043504 : Nat := 4983230072969 + 3 ^ 40 * 1043504 * 2
def baseEnd_1043504 : Nat := 357212744592927013000679

theorem tailTrace_1043504 : CollatzResearch.WordTrace tailWord_1043504 prefixEnd_1043504 357212744592927013000679 := by
  unfold tailWord_1043504
  simp only [CollatzResearch.WordTrace]
  refine ⟨19029858805785349569892783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25373145074380466093190377 19029858805785349569892783)
  ·
    refine ⟨28544788208678024354839175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19029858805785349569892783 28544788208678024354839175)
    ·
      refine ⟨42817182313017036532258763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28544788208678024354839175 42817182313017036532258763)
      ·
        refine ⟨64225773469525554798388145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42817182313017036532258763 64225773469525554798388145)
        ·
          refine ⟨48169330102144166098791109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64225773469525554798388145 48169330102144166098791109)
          ·
            refine ⟨9031749394152031143523333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48169330102144166098791109 9031749394152031143523333)
            ·
              refine ⟨1693453011403505839410625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9031749394152031143523333 1693453011403505839410625)
              ·
                refine ⟨1270089758552629379557969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693453011403505839410625 1270089758552629379557969)
                ·
                  refine ⟨952567318914472034668477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1270089758552629379557969 952567318914472034668477)
                  ·
                    refine ⟨357212744592927013000679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 952567318914472034668477 357212744592927013000679)
                    ·
                      rfl

theorem cell22_1043504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_1043504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043504 prefixEnd_1043504 := by exact prefixLift 1043504
  have htrace : WordTrace (prefixWord ++ tailWord_1043504) baseStart_1043504 baseEnd_1043504 := by
    simpa [prefixWord, tailWord_1043504, baseEnd_1043504] using wordTrace_append hprefix tailTrace_1043504
  have hstable : (prefixWord ++ tailWord_1043504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043504).length < 2 ^ (prefixWord ++ tailWord_1043504).sum := by decide
  have hdescent : baseEnd_1043504 < baseStart_1043504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043517 : List Nat := [1, 4, 1, 3, 1, 2, 3, 7]
def baseStart_1043517 : Nat := 118140960795 + 1043517 * 2 ^ 59
def prefixEnd_1043517 : Nat := 4983230072969 + 3 ^ 40 * 1043517 * 2
def baseEnd_1043517 : Nat := 39690799417622145825071

theorem tailTrace_1043517 : CollatzResearch.WordTrace tailWord_1043517 prefixEnd_1043517 39690799417622145825071 := by
  unfold tailWord_1043517
  simp only [CollatzResearch.WordTrace]
  refine ⟨38060191760523602360008805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25373461173682401573339203 38060191760523602360008805)
  ·
    refine ⟨7136285955098175442501651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38060191760523602360008805 7136285955098175442501651)
    ·
      refine ⟨10704428932647263163752477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136285955098175442501651 10704428932647263163752477)
      ·
        refine ⟨4014160849742723686407179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10704428932647263163752477 4014160849742723686407179)
        ·
          refine ⟨6021241274614085529610769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014160849742723686407179 6021241274614085529610769)
          ·
            refine ⟨4515930955960564147208077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6021241274614085529610769 4515930955960564147208077)
            ·
              refine ⟨1693474108485211555203029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4515930955960564147208077 1693474108485211555203029)
              ·
                refine ⟨39690799417622145825071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1693474108485211555203029 39690799417622145825071)
                ·
                  rfl

theorem cell22_1043517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 7].length) (baseStart_1043517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043517 prefixEnd_1043517 := by exact prefixLift 1043517
  have htrace : WordTrace (prefixWord ++ tailWord_1043517) baseStart_1043517 baseEnd_1043517 := by
    simpa [prefixWord, tailWord_1043517, baseEnd_1043517] using wordTrace_append hprefix tailTrace_1043517
  have hstable : (prefixWord ++ tailWord_1043517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043517).length < 2 ^ (prefixWord ++ tailWord_1043517).sum := by decide
  have hdescent : baseEnd_1043517 < baseStart_1043517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043542 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1043542 : Nat := 118140960795 + 1043542 * 2 ^ 59
def prefixEnd_1043542 : Nat := 4983230072969 + 3 ^ 40 * 1043542 * 2
def baseEnd_1043542 : Nat := 357225752769507580550563

theorem tailTrace_1043542 : CollatzResearch.WordTrace tailWord_1043542 prefixEnd_1043542 357225752769507580550563 := by
  unfold tailWord_1043542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378818974089564476854305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25374069056955354419779253 2378818974089564476854305)
  ·
    refine ⟨1784114230567173357640729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2378818974089564476854305 1784114230567173357640729)
    ·
      refine ⟨1338085672925380018230547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1784114230567173357640729 1338085672925380018230547)
      ·
        refine ⟨2007128509388070027345821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338085672925380018230547 2007128509388070027345821)
        ·
          refine ⟨752673191020526260254683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2007128509388070027345821 752673191020526260254683)
          ·
            refine ⟨1129009786530789390382025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752673191020526260254683 1129009786530789390382025)
            ·
              refine ⟨846757339898092042786519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129009786530789390382025 846757339898092042786519)
              ·
                refine ⟨1270136009847138064179779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846757339898092042786519 1270136009847138064179779)
                ·
                  refine ⟨1905204014770707096269669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270136009847138064179779 1905204014770707096269669)
                  ·
                    refine ⟨357225752769507580550563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1905204014770707096269669 357225752769507580550563)
                    ·
                      rfl

theorem cell22_1043542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1043542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043542 prefixEnd_1043542 := by exact prefixLift 1043542
  have htrace : WordTrace (prefixWord ++ tailWord_1043542) baseStart_1043542 baseEnd_1043542 := by
    simpa [prefixWord, tailWord_1043542, baseEnd_1043542] using wordTrace_append hprefix tailTrace_1043542
  have hstable : (prefixWord ++ tailWord_1043542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043542).length < 2 ^ (prefixWord ++ tailWord_1043542).sum := by decide
  have hdescent : baseEnd_1043542 < baseStart_1043542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043566 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1043566 : Nat := 118140960795 + 1043566 * 2 ^ 59
def prefixEnd_1043566 : Nat := 4983230072969 + 3 ^ 40 * 1043566 * 2
def baseEnd_1043566 : Nat := 357233968459979517950489

theorem tailTrace_1043566 : CollatzResearch.WordTrace tailWord_1043566 prefixEnd_1043566 357233968459979517950489 := by
  unfold tailWord_1043566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4757747367168260466067819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25374652624897389152361701 4757747367168260466067819)
  ·
    refine ⟨7136621050752390699101729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4757747367168260466067819 7136621050752390699101729)
    ·
      refine ⟨5352465788064293024326297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7136621050752390699101729 5352465788064293024326297)
      ·
        refine ⟨4014349341048219768244723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5352465788064293024326297 4014349341048219768244723)
        ·
          refine ⟨6021524011572329652367085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014349341048219768244723 6021524011572329652367085)
          ·
            refine ⟨2258071504339623619637657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6021524011572329652367085 2258071504339623619637657)
            ·
              refine ⟨1693553628254717714728243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258071504339623619637657 1693553628254717714728243)
              ·
                refine ⟨2540330442382076572092365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693553628254717714728243 2540330442382076572092365)
                ·
                  refine ⟨952623915893278714534637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2540330442382076572092365 952623915893278714534637)
                  ·
                    refine ⟨357233968459979517950489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 952623915893278714534637 357233968459979517950489)
                    ·
                      rfl

theorem cell22_1043566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1043566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043566 prefixEnd_1043566 := by exact prefixLift 1043566
  have htrace : WordTrace (prefixWord ++ tailWord_1043566) baseStart_1043566 baseEnd_1043566 := by
    simpa [prefixWord, tailWord_1043566, baseEnd_1043566] using wordTrace_append hprefix tailTrace_1043566
  have hstable : (prefixWord ++ tailWord_1043566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043566).length < 2 ^ (prefixWord ++ tailWord_1043566).sum := by decide
  have hdescent : baseEnd_1043566 < baseStart_1043566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043697 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 9]
def baseStart_1043697 : Nat := 118140960795 + 1043697 * 2 ^ 59
def prefixEnd_1043697 : Nat := 4983230072969 + 3 ^ 40 * 1043697 * 2
def baseEnd_1043697 : Nat := 119092937479046280975029

theorem tailTrace_1043697 : CollatzResearch.WordTrace tailWord_1043697 prefixEnd_1043697 119092937479046280975029 := by
  unfold tailWord_1043697
  simp only [CollatzResearch.WordTrace]
  refine ⟨38066756899871493101561345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25377837933247662067707563 38066756899871493101561345)
  ·
    refine ⟨28550067674903619826171009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38066756899871493101561345 28550067674903619826171009)
    ·
      refine ⟨21412550756177714869628257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28550067674903619826171009 21412550756177714869628257)
      ·
        refine ⟨16059413067133286152221193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21412550756177714869628257 16059413067133286152221193)
        ·
          refine ⟨12044559800349964614165895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16059413067133286152221193 12044559800349964614165895)
          ·
            refine ⟨18066839700524946921248843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044559800349964614165895 18066839700524946921248843)
            ·
              refine ⟨27100259550787420381873265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18066839700524946921248843 27100259550787420381873265)
              ·
                refine ⟨20325194663090565286404949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27100259550787420381873265 20325194663090565286404949)
                ·
                  refine ⟨119092937479046280975029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20325194663090565286404949 119092937479046280975029)
                  ·
                    rfl

theorem cell22_1043697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_1043697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043697 prefixEnd_1043697 := by exact prefixLift 1043697
  have htrace : WordTrace (prefixWord ++ tailWord_1043697) baseStart_1043697 baseEnd_1043697 := by
    simpa [prefixWord, tailWord_1043697, baseEnd_1043697] using wordTrace_append hprefix tailTrace_1043697
  have hstable : (prefixWord ++ tailWord_1043697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043697).length < 2 ^ (prefixWord ++ tailWord_1043697).sum := by decide
  have hdescent : baseEnd_1043697 < baseStart_1043697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043712 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_1043712 : Nat := 118140960795 + 1043712 * 2 ^ 59
def prefixEnd_1043712 : Nat := 4983230072969 + 3 ^ 40 * 1043712 * 2
def baseEnd_1043712 : Nat := 357283947243683803800041

theorem tailTrace_1043712 : CollatzResearch.WordTrace tailWord_1043712 prefixEnd_1043712 357283947243683803800041 := by
  unfold tailWord_1043712
  simp only [CollatzResearch.WordTrace]
  refine ⟨19033651997408575331678695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25378202663211433775571593 19033651997408575331678695)
  ·
    refine ⟨28550477996112862997518043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19033651997408575331678695 28550477996112862997518043)
    ·
      refine ⟨42825716994169294496277065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28550477996112862997518043 42825716994169294496277065)
      ·
        refine ⟨32119287745626970872207799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42825716994169294496277065 32119287745626970872207799)
        ·
          refine ⟨48178931618440456308311699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32119287745626970872207799 48178931618440456308311699)
          ·
            refine ⟨72268397427660684462467549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48178931618440456308311699 72268397427660684462467549)
            ·
              refine ⟨27100649035372756673425331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72268397427660684462467549 27100649035372756673425331)
              ·
                refine ⟨40650973553059135010137997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27100649035372756673425331 40650973553059135010137997)
                ·
                  refine ⟨15244115082397175628801749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40650973553059135010137997 15244115082397175628801749)
                  ·
                    refine ⟨357283947243683803800041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15244115082397175628801749 357283947243683803800041)
                    ·
                      rfl

theorem cell22_1043712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_1043712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043712 prefixEnd_1043712 := by exact prefixLift 1043712
  have htrace : WordTrace (prefixWord ++ tailWord_1043712) baseStart_1043712 baseEnd_1043712 := by
    simpa [prefixWord, tailWord_1043712, baseEnd_1043712] using wordTrace_append hprefix tailTrace_1043712
  have hstable : (prefixWord ++ tailWord_1043712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043712).length < 2 ^ (prefixWord ++ tailWord_1043712).sum := by decide
  have hdescent : baseEnd_1043712 < baseStart_1043712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043761 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_1043761 : Nat := 118140960795 + 1043761 * 2 ^ 59
def prefixEnd_1043761 : Nat := 4983230072969 + 3 ^ 40 * 1043761 * 2
def baseEnd_1043761 : Nat := 357300720945064009324891

theorem tailTrace_1043761 : CollatzResearch.WordTrace tailWord_1043761 prefixEnd_1043761 357300720945064009324891 := by
  unfold tailWord_1043761
  simp only [CollatzResearch.WordTrace]
  refine ⟨38069091171639632031891137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25379394114426421354594091 38069091171639632031891137)
  ·
    refine ⟨28551818378729724023918353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38069091171639632031891137 28551818378729724023918353)
    ·
      refine ⟨21413863784047293017938765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28551818378729724023918353 21413863784047293017938765)
      ·
        refine ⟨8030198919017734881727037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21413863784047293017938765 8030198919017734881727037)
        ·
          refine ⟨3011324594631650580647639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8030198919017734881727037 3011324594631650580647639)
          ·
            refine ⟨4516986891947475870971459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011324594631650580647639 4516986891947475870971459)
            ·
              refine ⟨6775480337921213806457189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4516986891947475870971459 6775480337921213806457189)
              ·
                refine ⟨1270402563360227588710723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6775480337921213806457189 1270402563360227588710723)
                ·
                  refine ⟨1905603845040341383066085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270402563360227588710723 1905603845040341383066085)
                  ·
                    refine ⟨357300720945064009324891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1905603845040341383066085 357300720945064009324891)
                    ·
                      rfl

theorem cell22_1043761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_1043761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043761 prefixEnd_1043761 := by exact prefixLift 1043761
  have htrace : WordTrace (prefixWord ++ tailWord_1043761) baseStart_1043761 baseEnd_1043761 := by
    simpa [prefixWord, tailWord_1043761, baseEnd_1043761] using wordTrace_append hprefix tailTrace_1043761
  have hstable : (prefixWord ++ tailWord_1043761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043761).length < 2 ^ (prefixWord ++ tailWord_1043761).sum := by decide
  have hdescent : baseEnd_1043761 < baseStart_1043761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043793 : List Nat := [1, 2, 2, 1, 4, 1, 5, 2, 4]
def baseStart_1043793 : Nat := 118140960795 + 1043793 * 2 ^ 59
def prefixEnd_1043793 : Nat := 4983230072969 + 3 ^ 40 * 1043793 * 2
def baseEnd_1043793 : Nat := 119103891733008864174931

theorem tailTrace_1043793 : CollatzResearch.WordTrace tailWord_1043793 prefixEnd_1043793 119103891733008864174931 := by
  unfold tailWord_1043793
  simp only [CollatzResearch.WordTrace]
  refine ⟨38070258307523701497056033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25380172205015800998037355 38070258307523701497056033)
  ·
    refine ⟨28552693730642776122792025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38070258307523701497056033 28552693730642776122792025)
    ·
      refine ⟨21414520297982082092094019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28552693730642776122792025 21414520297982082092094019)
      ·
        refine ⟨32121780446973123138141029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21414520297982082092094019 32121780446973123138141029)
        ·
          refine ⟨6022833833807460588401443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32121780446973123138141029 6022833833807460588401443)
          ·
            refine ⟨9034250750711190882602165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022833833807460588401443 9034250750711190882602165)
            ·
              refine ⟨846961007879174145243953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9034250750711190882602165 846961007879174145243953)
              ·
                refine ⟨635220755909380608932965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846961007879174145243953 635220755909380608932965)
                ·
                  refine ⟨119103891733008864174931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635220755909380608932965 119103891733008864174931)
                  ·
                    rfl

theorem cell22_1043793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 4].length) (baseStart_1043793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043793 prefixEnd_1043793 := by exact prefixLift 1043793
  have htrace : WordTrace (prefixWord ++ tailWord_1043793) baseStart_1043793 baseEnd_1043793 := by
    simpa [prefixWord, tailWord_1043793, baseEnd_1043793] using wordTrace_append hprefix tailTrace_1043793
  have hstable : (prefixWord ++ tailWord_1043793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043793).length < 2 ^ (prefixWord ++ tailWord_1043793).sum := by decide
  have hdescent : baseEnd_1043793 < baseStart_1043793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043808 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 2, 3]
def baseStart_1043808 : Nat := 118140960795 + 1043808 * 2 ^ 59
def prefixEnd_1043808 : Nat := 4983230072969 + 3 ^ 40 * 1043808 * 2
def baseEnd_1043808 : Nat := 357316810005571553399747

theorem tailTrace_1043808 : CollatzResearch.WordTrace tailWord_1043808 prefixEnd_1043808 357316810005571553399747 := by
  unfold tailWord_1043808
  simp only [CollatzResearch.WordTrace]
  refine ⟨19035402701234679529426039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25380536934979572705901385 19035402701234679529426039)
  ·
    refine ⟨28553104051852019294139059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19035402701234679529426039 28553104051852019294139059)
    ·
      refine ⟨42829656077778028941208589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28553104051852019294139059 42829656077778028941208589)
      ·
        refine ⟨16061121029166760852953221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42829656077778028941208589 16061121029166760852953221)
        ·
          refine ⟨3011460192968767659928729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16061121029166760852953221 3011460192968767659928729)
          ·
            refine ⟨2258595144726575744946547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3011460192968767659928729 2258595144726575744946547)
            ·
              refine ⟨3387892717089863617419821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258595144726575744946547 3387892717089863617419821)
              ·
                refine ⟨1270459768908698856532433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3387892717089863617419821 1270459768908698856532433)
                ·
                  refine ⟨952844826681524142399325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1270459768908698856532433 952844826681524142399325)
                  ·
                    refine ⟨357316810005571553399747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 952844826681524142399325 357316810005571553399747)
                    ·
                      rfl

theorem cell22_1043808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_1043808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043808 prefixEnd_1043808 := by exact prefixLift 1043808
  have htrace : WordTrace (prefixWord ++ tailWord_1043808) baseStart_1043808 baseEnd_1043808 := by
    simpa [prefixWord, tailWord_1043808, baseEnd_1043808] using wordTrace_append hprefix tailTrace_1043808
  have hstable : (prefixWord ++ tailWord_1043808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043808).length < 2 ^ (prefixWord ++ tailWord_1043808).sum := by decide
  have hdescent : baseEnd_1043808 < baseStart_1043808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043838 : List Nat := [4, 2, 3, 2, 1, 10]
def baseStart_1043838 : Nat := 118140960795 + 1043838 * 2 ^ 59
def prefixEnd_1043838 : Nat := 4983230072969 + 3 ^ 40 * 1043838 * 2
def baseEnd_1043838 : Nat := 4411445427390882409255

theorem tailTrace_1043838 : CollatzResearch.WordTrace tailWord_1043838 prefixEnd_1043838 4411445427390882409255 := by
  unfold tailWord_1043838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4758987449045084272805521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25381266394907116121629445 4758987449045084272805521)
  ·
    refine ⟨3569240586783813204604141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4758987449045084272805521 3569240586783813204604141)
    ·
      refine ⟨1338465220043929951726553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3569240586783813204604141 1338465220043929951726553)
      ·
        refine ⟨1003848915032947463794915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1338465220043929951726553 1003848915032947463794915)
        ·
          refine ⟨1505773372549421195692373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003848915032947463794915 1505773372549421195692373)
          ·
            refine ⟨4411445427390882409255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1505773372549421195692373 4411445427390882409255)
            ·
              rfl

theorem cell22_1043838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 10].length) (baseStart_1043838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043838 prefixEnd_1043838 := by exact prefixLift 1043838
  have htrace : WordTrace (prefixWord ++ tailWord_1043838) baseStart_1043838 baseEnd_1043838 := by
    simpa [prefixWord, tailWord_1043838, baseEnd_1043838] using wordTrace_append hprefix tailTrace_1043838
  have hstable : (prefixWord ++ tailWord_1043838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043838).length < 2 ^ (prefixWord ++ tailWord_1043838).sum := by decide
  have hdescent : baseEnd_1043838 < baseStart_1043838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043842 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1043842 : Nat := 118140960795 + 1043842 * 2 ^ 59
def prefixEnd_1043842 : Nat := 4983230072969 + 3 ^ 40 * 1043842 * 2
def baseEnd_1043842 : Nat := 357328448900406798049643

theorem tailTrace_1043842 : CollatzResearch.WordTrace tailWord_1043842 prefixEnd_1043842 357328448900406798049643 := by
  unfold tailWord_1043842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9518011371086545716397445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25381363656230788577059853 9518011371086545716397445)
  ·
    refine ⟨1784627132078727321824521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9518011371086545716397445 1784627132078727321824521)
    ·
      refine ⟨1338470349059045491368391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1784627132078727321824521 1338470349059045491368391)
      ·
        refine ⟨2007705523588568237052587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338470349059045491368391 2007705523588568237052587)
        ·
          refine ⟨3011558285382852355578881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007705523588568237052587 3011558285382852355578881)
          ·
            refine ⟨2258668714037139266684161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3011558285382852355578881 2258668714037139266684161)
            ·
              refine ⟨1694001535527854450013121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258668714037139266684161 1694001535527854450013121)
              ·
                refine ⟨1270501151645890837509841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694001535527854450013121 1270501151645890837509841)
                ·
                  refine ⟨952875863734418128132381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1270501151645890837509841 952875863734418128132381)
                  ·
                    refine ⟨357328448900406798049643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 952875863734418128132381 357328448900406798049643)
                    ·
                      rfl

theorem cell22_1043842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1043842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043842 prefixEnd_1043842 := by exact prefixLift 1043842
  have htrace : WordTrace (prefixWord ++ tailWord_1043842) baseStart_1043842 baseEnd_1043842 := by
    simpa [prefixWord, tailWord_1043842, baseEnd_1043842] using wordTrace_append hprefix tailTrace_1043842
  have hstable : (prefixWord ++ tailWord_1043842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043842).length < 2 ^ (prefixWord ++ tailWord_1043842).sum := by decide
  have hdescent : baseEnd_1043842 < baseStart_1043842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043866 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_1043866 : Nat := 118140960795 + 1043866 * 2 ^ 59
def prefixEnd_1043866 : Nat := 4983230072969 + 3 ^ 40 * 1043866 * 2
def baseEnd_1043866 : Nat := 119112221530292911816523

theorem tailTrace_1043866 : CollatzResearch.WordTrace tailWord_1043866 prefixEnd_1043866 119112221530292911816523 := by
  unfold tailWord_1043866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9518230209064808741115863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25381947224172823309642301 9518230209064808741115863)
  ·
    refine ⟨14277345313597213111673795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9518230209064808741115863 14277345313597213111673795)
    ·
      refine ⟨21416017970395819667510693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14277345313597213111673795 21416017970395819667510693)
      ·
        refine ⟨4015503369449216187658255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21416017970395819667510693 4015503369449216187658255)
        ·
          refine ⟨6023255054173824281487383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015503369449216187658255 6023255054173824281487383)
          ·
            refine ⟨9034882581260736422231075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6023255054173824281487383 9034882581260736422231075)
            ·
              refine ⟨13552323871891104633346613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9034882581260736422231075 13552323871891104633346613)
              ·
                refine ⟨1270530362989791059376245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13552323871891104633346613 1270530362989791059376245)
                ·
                  refine ⟨119112221530292911816523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1270530362989791059376245 119112221530292911816523)
                  ·
                    rfl

theorem cell22_1043866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_1043866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043866 prefixEnd_1043866 := by exact prefixLift 1043866
  have htrace : WordTrace (prefixWord ++ tailWord_1043866) baseStart_1043866 baseEnd_1043866 := by
    simpa [prefixWord, tailWord_1043866, baseEnd_1043866] using wordTrace_append hprefix tailTrace_1043866
  have hstable : (prefixWord ++ tailWord_1043866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043866).length < 2 ^ (prefixWord ++ tailWord_1043866).sum := by decide
  have hdescent : baseEnd_1043866 < baseStart_1043866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043900 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 5]
def baseStart_1043900 : Nat := 118140960795 + 1043900 * 2 ^ 59
def prefixEnd_1043900 : Nat := 4983230072969 + 3 ^ 40 * 1043900 * 2
def baseEnd_1043900 : Nat := 119116101161904660033155

theorem tailTrace_1043900 : CollatzResearch.WordTrace tailWord_1043900 prefixEnd_1043900 119116101161904660033155 := by
  unfold tailWord_1043900
  simp only [CollatzResearch.WordTrace]
  refine ⟨19037080459068029385600577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25382773945424039180800769 19037080459068029385600577)
  ·
    refine ⟨14277810344301022039200433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19037080459068029385600577 14277810344301022039200433)
    ·
      refine ⟨10708357758225766529400325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14277810344301022039200433 10708357758225766529400325)
      ·
        refine ⟨2007817079667331224262561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10708357758225766529400325 2007817079667331224262561)
        ·
          refine ⟨1505862809750498418196921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2007817079667331224262561 1505862809750498418196921)
          ·
            refine ⟨1129397107312873813647691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505862809750498418196921 1129397107312873813647691)
            ·
              refine ⟨1694095660969310720471537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129397107312873813647691 1694095660969310720471537)
              ·
                refine ⟨1270571745726983040353653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694095660969310720471537 1270571745726983040353653)
                ·
                  refine ⟨119116101161904660033155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1270571745726983040353653 119116101161904660033155)
                  ·
                    rfl

theorem cell22_1043900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_1043900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043900 prefixEnd_1043900 := by exact prefixLift 1043900
  have htrace : WordTrace (prefixWord ++ tailWord_1043900) baseStart_1043900 baseEnd_1043900 := by
    simpa [prefixWord, tailWord_1043900, baseEnd_1043900] using wordTrace_append hprefix tailTrace_1043900
  have hstable : (prefixWord ++ tailWord_1043900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043900).length < 2 ^ (prefixWord ++ tailWord_1043900).sum := by decide
  have hdescent : baseEnd_1043900 < baseStart_1043900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043909 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_1043909 : Nat := 118140960795 + 1043909 * 2 ^ 59
def prefixEnd_1043909 : Nat := 4983230072969 + 3 ^ 40 * 1043909 * 2
def baseEnd_1043909 : Nat := 357351384369640956624437

theorem tailTrace_1043909 : CollatzResearch.WordTrace tailWord_1043909 prefixEnd_1043909 357351384369640956624437 := by
  unfold tailWord_1043909
  simp only [CollatzResearch.WordTrace]
  refine ⟨38074489175103453308278781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25382992783402302205519187 38074489175103453308278781)
  ·
    refine ⟨14277933440663794990604543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38074489175103453308278781 14277933440663794990604543)
    ·
      refine ⟨21416900160995692485906815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14277933440663794990604543 21416900160995692485906815)
      ·
        refine ⟨32125350241493538728860223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21416900160995692485906815 32125350241493538728860223)
        ·
          refine ⟨48188025362240308093290335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32125350241493538728860223 48188025362240308093290335)
          ·
            refine ⟨72282038043360462139935503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48188025362240308093290335 72282038043360462139935503)
            ·
              refine ⟨108423057065040693209903255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72282038043360462139935503 108423057065040693209903255)
              ·
                refine ⟨162634585597561039814854883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108423057065040693209903255 162634585597561039814854883)
                ·
                  refine ⟨243951878396341559722282325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162634585597561039814854883 243951878396341559722282325)
                  ·
                    refine ⟨357351384369640956624437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 243951878396341559722282325 357351384369640956624437)
                    ·
                      rfl

theorem cell22_1043909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_1043909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043909 prefixEnd_1043909 := by exact prefixLift 1043909
  have htrace : WordTrace (prefixWord ++ tailWord_1043909) baseStart_1043909 baseEnd_1043909 := by
    simpa [prefixWord, tailWord_1043909, baseEnd_1043909] using wordTrace_append hprefix tailTrace_1043909
  have hstable : (prefixWord ++ tailWord_1043909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043909).length < 2 ^ (prefixWord ++ tailWord_1043909).sum := by decide
  have hdescent : baseEnd_1043909 < baseStart_1043909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043911 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 6]
def baseStart_1043911 : Nat := 118140960795 + 1043911 * 2 ^ 59
def prefixEnd_1043911 : Nat := 4983230072969 + 3 ^ 40 * 1043911 * 2
def baseEnd_1043911 : Nat := 119117356336837872691477

theorem tailTrace_1043911 : CollatzResearch.WordTrace tailWord_1043911 prefixEnd_1043911 119117356336837872691477 := by
  unfold tailWord_1043911
  simp only [CollatzResearch.WordTrace]
  refine ⟨38074562121096207649851587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25383041414064138433234391 38074562121096207649851587)
  ·
    refine ⟨57111843181644311474777381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38074562121096207649851587 57111843181644311474777381)
    ·
      refine ⟨10708470596558308401520759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57111843181644311474777381 10708470596558308401520759)
      ·
        refine ⟨16062705894837462602281139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10708470596558308401520759 16062705894837462602281139)
        ·
          refine ⟨24094058842256193903421709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16062705894837462602281139 24094058842256193903421709)
          ·
            refine ⟨9035272065846072713783141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24094058842256193903421709 9035272065846072713783141)
            ·
              refine ⟨1694113512346138633834339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9035272065846072713783141 1694113512346138633834339)
              ·
                refine ⟨2541170268519207950751509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694113512346138633834339 2541170268519207950751509)
                ·
                  refine ⟨119117356336837872691477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2541170268519207950751509 119117356336837872691477)
                  ·
                    rfl

theorem cell22_1043911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 6].length) (baseStart_1043911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043911 prefixEnd_1043911 := by exact prefixLift 1043911
  have htrace : WordTrace (prefixWord ++ tailWord_1043911) baseStart_1043911 baseEnd_1043911 := by
    simpa [prefixWord, tailWord_1043911, baseEnd_1043911] using wordTrace_append hprefix tailTrace_1043911
  have hstable : (prefixWord ++ tailWord_1043911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043911).length < 2 ^ (prefixWord ++ tailWord_1043911).sum := by decide
  have hdescent : baseEnd_1043911 < baseStart_1043911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043943 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 4, 3]
def baseStart_1043943 : Nat := 118140960795 + 1043943 * 2 ^ 59
def prefixEnd_1043943 : Nat := 4983230072969 + 3 ^ 40 * 1043943 * 2
def baseEnd_1043943 : Nat := 357363023264476201274333

theorem tailTrace_1043943 : CollatzResearch.WordTrace tailWord_1043943 prefixEnd_1043943 357363023264476201274333 := by
  unfold tailWord_1043943
  simp only [CollatzResearch.WordTrace]
  refine ⟨38075729256980277115016483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25383819504653518076677655 38075729256980277115016483)
  ·
    refine ⟨57113593885470415672524725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38075729256980277115016483 57113593885470415672524725)
    ·
      refine ⟨5354399426762851469299193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57113593885470415672524725 5354399426762851469299193)
      ·
        refine ⟨4015799570072138601974395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5354399426762851469299193 4015799570072138601974395)
        ·
          refine ⟨6023699355108207902961593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015799570072138601974395 6023699355108207902961593)
          ·
            refine ⟨4517774516331155927221195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6023699355108207902961593 4517774516331155927221195)
            ·
              refine ⟨6776661774496733890831793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517774516331155927221195 6776661774496733890831793)
              ·
                refine ⟨5082496330872550418123845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6776661774496733890831793 5082496330872550418123845)
                ·
                  refine ⟨952968062038603203398221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5082496330872550418123845 952968062038603203398221)
                  ·
                    refine ⟨357363023264476201274333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 952968062038603203398221 357363023264476201274333)
                    ·
                      rfl

theorem cell22_1043943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_1043943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043943 prefixEnd_1043943 := by exact prefixLift 1043943
  have htrace : WordTrace (prefixWord ++ tailWord_1043943) baseStart_1043943 baseEnd_1043943 := by
    simpa [prefixWord, tailWord_1043943, baseEnd_1043943] using wordTrace_append hprefix tailTrace_1043943
  have hstable : (prefixWord ++ tailWord_1043943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043943).length < 2 ^ (prefixWord ++ tailWord_1043943).sum := by decide
  have hdescent : baseEnd_1043943 < baseStart_1043943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043958 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1043958 : Nat := 118140960795 + 1043958 * 2 ^ 59
def prefixEnd_1043958 : Nat := 4983230072969 + 3 ^ 40 * 1043958 * 2
def baseEnd_1043958 : Nat := 357368158071021162149287

theorem tailTrace_1043958 : CollatzResearch.WordTrace tailWord_1043958 prefixEnd_1043958 357368158071021162149287 := by
  unfold tailWord_1043958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379767271995370917300783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25384184234617289784541685 2379767271995370917300783)
  ·
    refine ⟨3569650907993056375951175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2379767271995370917300783 3569650907993056375951175)
    ·
      refine ⟨5354476361989584563926763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3569650907993056375951175 5354476361989584563926763)
      ·
        refine ⟨8031714542984376845890145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354476361989584563926763 8031714542984376845890145)
        ·
          refine ⟨6023785907238282634417609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8031714542984376845890145 6023785907238282634417609)
          ·
            refine ⟨4517839430428711975813207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6023785907238282634417609 4517839430428711975813207)
            ·
              refine ⟨6776759145643067963719811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517839430428711975813207 6776759145643067963719811)
              ·
                refine ⟨10165138718464601945579717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776759145643067963719811 10165138718464601945579717)
                ·
                  refine ⟨1905963509712112864796197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10165138718464601945579717 1905963509712112864796197)
                  ·
                    refine ⟨357368158071021162149287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1905963509712112864796197 357368158071021162149287)
                    ·
                      rfl

theorem cell22_1043958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1043958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043958 prefixEnd_1043958 := by exact prefixLift 1043958
  have htrace : WordTrace (prefixWord ++ tailWord_1043958) baseStart_1043958 baseEnd_1043958 := by
    simpa [prefixWord, tailWord_1043958, baseEnd_1043958] using wordTrace_append hprefix tailTrace_1043958
  have hstable : (prefixWord ++ tailWord_1043958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043958).length < 2 ^ (prefixWord ++ tailWord_1043958).sum := by decide
  have hdescent : baseEnd_1043958 < baseStart_1043958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043981 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1043981 : Nat := 118140960795 + 1043981 * 2 ^ 59
def prefixEnd_1043981 : Nat := 4983230072969 + 3 ^ 40 * 1043981 * 2
def baseEnd_1043981 : Nat := 357376031441056768824217

theorem tailTrace_1043981 : CollatzResearch.WordTrace tailWord_1043981 prefixEnd_1043981 357376031441056768824217 := by
  unfold tailWord_1043981
  simp only [CollatzResearch.WordTrace]
  refine ⟨38077115230842609604899797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25384743487228406403266531 38077115230842609604899797)
  ·
    refine ⟨892432388222873662614839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 38077115230842609604899797 892432388222873662614839)
    ·
      refine ⟨1338648582334310493922259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 892432388222873662614839 1338648582334310493922259)
      ·
        refine ⟨2007972873501465740883389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338648582334310493922259 2007972873501465740883389)
        ·
          refine ⟨752989827563049652831271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2007972873501465740883389 752989827563049652831271)
          ·
            refine ⟨1129484741344574479246907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752989827563049652831271 1129484741344574479246907)
            ·
              refine ⟨1694227112016861718870361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129484741344574479246907 1694227112016861718870361)
              ·
                refine ⟨1270670334012646289152771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694227112016861718870361 1270670334012646289152771)
                ·
                  refine ⟨1906005501018969433729157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270670334012646289152771 1906005501018969433729157)
                  ·
                    refine ⟨357376031441056768824217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1906005501018969433729157 357376031441056768824217)
                    ·
                      rfl

theorem cell22_1043981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1043981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1043981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1043981 prefixEnd_1043981 := by exact prefixLift 1043981
  have htrace : WordTrace (prefixWord ++ tailWord_1043981) baseStart_1043981 baseEnd_1043981 := by
    simpa [prefixWord, tailWord_1043981, baseEnd_1043981] using wordTrace_append hprefix tailTrace_1043981
  have hstable : (prefixWord ++ tailWord_1043981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043981).length < 2 ^ (prefixWord ++ tailWord_1043981).sum := by decide
  have hdescent : baseEnd_1043981 < baseStart_1043981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044005 : List Nat := [1, 3, 1, 2, 2, 1, 1, 7, 1, 3]
def baseStart_1044005 : Nat := 118140960795 + 1044005 * 2 ^ 59
def prefixEnd_1044005 : Nat := 4983230072969 + 3 ^ 40 * 1044005 * 2
def baseEnd_1044005 : Nat := 357384247131528706224143

theorem tailTrace_1044005 : CollatzResearch.WordTrace tailWord_1044005 prefixEnd_1044005 357384247131528706224143 := by
  unfold tailWord_1044005
  simp only [CollatzResearch.WordTrace]
  refine ⟨38077990582755661703773469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25385327055170441135848979 38077990582755661703773469)
  ·
    refine ⟨14279246468533373138915051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38077990582755661703773469 14279246468533373138915051)
    ·
      refine ⟨21418869702800059708372577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14279246468533373138915051 21418869702800059708372577)
      ·
        refine ⟨16064152277100044781279433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21418869702800059708372577 16064152277100044781279433)
        ·
          refine ⟨12048114207825033585959575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16064152277100044781279433 12048114207825033585959575)
          ·
            refine ⟨18072171311737550378939363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12048114207825033585959575 18072171311737550378939363)
            ·
              refine ⟨27108256967606325568409045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18072171311737550378939363 27108256967606325568409045)
              ·
                refine ⟨635349772678273255509587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27108256967606325568409045 635349772678273255509587)
                ·
                  refine ⟨953024659017409883264381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635349772678273255509587 953024659017409883264381)
                  ·
                    refine ⟨357384247131528706224143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 953024659017409883264381 357384247131528706224143)
                    ·
                      rfl

theorem cell22_1044005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_1044005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044005 prefixEnd_1044005 := by exact prefixLift 1044005
  have htrace : WordTrace (prefixWord ++ tailWord_1044005) baseStart_1044005 baseEnd_1044005 := by
    simpa [prefixWord, tailWord_1044005, baseEnd_1044005] using wordTrace_append hprefix tailTrace_1044005
  have hstable : (prefixWord ++ tailWord_1044005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044005).length < 2 ^ (prefixWord ++ tailWord_1044005).sum := by decide
  have hdescent : baseEnd_1044005 < baseStart_1044005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044016 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_1044016 : Nat := 118140960795 + 1044016 * 2 ^ 59
def prefixEnd_1044016 : Nat := 4983230072969 + 3 ^ 40 * 1044016 * 2
def baseEnd_1044016 : Nat := 357388012656328344199109

theorem tailTrace_1044016 : CollatzResearch.WordTrace tailWord_1044016 prefixEnd_1044016 357388012656328344199109 := by
  unfold tailWord_1044016
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039195892857905291211951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25385594523810540388282601 19039195892857905291211951)
  ·
    refine ⟨28558793839286857936817927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19039195892857905291211951 28558793839286857936817927)
    ·
      refine ⟨42838190758930286905226891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28558793839286857936817927 42838190758930286905226891)
      ·
        refine ⟨64257286138395430357840337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42838190758930286905226891 64257286138395430357840337)
        ·
          refine ⟨48192964603796572768380253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64257286138395430357840337 48192964603796572768380253)
          ·
            refine ⟨18072361726423714788142595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48192964603796572768380253 18072361726423714788142595)
            ·
              refine ⟨27108542589635572182213893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18072361726423714788142595 27108542589635572182213893)
              ·
                refine ⟨5082851735556669784165105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27108542589635572182213893 5082851735556669784165105)
                ·
                  refine ⟨3812138801667502338123829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5082851735556669784165105 3812138801667502338123829)
                  ·
                    refine ⟨357388012656328344199109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3812138801667502338123829 357388012656328344199109)
                    ·
                      rfl

theorem cell22_1044016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_1044016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044016 prefixEnd_1044016 := by exact prefixLift 1044016
  have htrace : WordTrace (prefixWord ++ tailWord_1044016) baseStart_1044016 baseEnd_1044016 := by
    simpa [prefixWord, tailWord_1044016, baseEnd_1044016] using wordTrace_append hprefix tailTrace_1044016
  have hstable : (prefixWord ++ tailWord_1044016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044016).length < 2 ^ (prefixWord ++ tailWord_1044016).sum := by decide
  have hdescent : baseEnd_1044016 < baseStart_1044016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044033 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1044033 : Nat := 118140960795 + 1044033 * 2 ^ 59
def prefixEnd_1044033 : Nat := 4983230072969 + 3 ^ 40 * 1044033 * 2
def baseEnd_1044033 : Nat := 357393832103745966524057

theorem tailTrace_1044033 : CollatzResearch.WordTrace tailWord_1044033 prefixEnd_1044033 357393832103745966524057 := by
  unfold tailWord_1044033
  simp only [CollatzResearch.WordTrace]
  refine ⟨38079011826654222485792753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25386007884436148323861835 38079011826654222485792753)
  ·
    refine ⟨28559258869990666864344565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38079011826654222485792753 28559258869990666864344565)
    ·
      refine ⟨2677430519061625018532303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28559258869990666864344565 2677430519061625018532303)
      ·
        refine ⟨4016145778592437527798455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677430519061625018532303 4016145778592437527798455)
        ·
          refine ⟨6024218667888656291697683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016145778592437527798455 6024218667888656291697683)
          ·
            refine ⟨9036328001832984437546525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024218667888656291697683 9036328001832984437546525)
            ·
              refine ⟨3388623000687369164079947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9036328001832984437546525 3388623000687369164079947)
              ·
                refine ⟨5082934501031053746119921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388623000687369164079947 5082934501031053746119921)
                ·
                  refine ⟨3812200875773290309589941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5082934501031053746119921 3812200875773290309589941)
                  ·
                    refine ⟨357393832103745966524057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3812200875773290309589941 357393832103745966524057)
                    ·
                      rfl

theorem cell22_1044033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1044033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044033 prefixEnd_1044033 := by exact prefixLift 1044033
  have htrace : WordTrace (prefixWord ++ tailWord_1044033) baseStart_1044033 baseEnd_1044033 := by
    simpa [prefixWord, tailWord_1044033, baseEnd_1044033] using wordTrace_append hprefix tailTrace_1044033
  have hstable : (prefixWord ++ tailWord_1044033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044033).length < 2 ^ (prefixWord ++ tailWord_1044033).sum := by decide
  have hdescent : baseEnd_1044033 < baseStart_1044033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044048 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_1044048 : Nat := 118140960795 + 1044048 * 2 ^ 59
def prefixEnd_1044048 : Nat := 4983230072969 + 3 ^ 40 * 1044048 * 2
def baseEnd_1044048 : Nat := 357398966910290927399011

theorem tailTrace_1044048 : CollatzResearch.WordTrace tailWord_1044048 prefixEnd_1044048 357398966910290927399011 := by
  unfold tailWord_1044048
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039779460799940023794399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25386372614399920031725865 19039779460799940023794399)
  ·
    refine ⟨28559669191199910035691599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19039779460799940023794399 28559669191199910035691599)
    ·
      refine ⟨42839503786799865053537399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28559669191199910035691599 42839503786799865053537399)
      ·
        refine ⟨64259255680199797580306099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42839503786799865053537399 64259255680199797580306099)
        ·
          refine ⟨96388883520299696370459149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64259255680199797580306099 96388883520299696370459149)
          ·
            refine ⟨36145831320112386138922181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96388883520299696370459149 36145831320112386138922181)
            ·
              refine ⟨6777343372521072401047909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36145831320112386138922181 6777343372521072401047909)
              ·
                refine ⟨1270751882347701075196483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6777343372521072401047909 1270751882347701075196483)
                ·
                  refine ⟨1906127823521551612794725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270751882347701075196483 1906127823521551612794725)
                  ·
                    refine ⟨357398966910290927399011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1906127823521551612794725 357398966910290927399011)
                    ·
                      rfl

theorem cell22_1044048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_1044048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044048 prefixEnd_1044048 := by exact prefixLift 1044048
  have htrace : WordTrace (prefixWord ++ tailWord_1044048) baseStart_1044048 baseEnd_1044048 := by
    simpa [prefixWord, tailWord_1044048, baseEnd_1044048] using wordTrace_append hprefix tailTrace_1044048
  have hstable : (prefixWord ++ tailWord_1044048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044048).length < 2 ^ (prefixWord ++ tailWord_1044048).sum := by decide
  have hdescent : baseEnd_1044048 < baseStart_1044048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044080 : List Nat := [2, 1, 1, 1, 6, 1, 2, 4, 4]
def baseStart_1044080 : Nat := 118140960795 + 1044080 * 2 ^ 59
def prefixEnd_1044080 : Nat := 4983230072969 + 3 ^ 40 * 1044080 * 2
def baseEnd_1044080 : Nat := 119136640388084503532971

theorem tailTrace_1044080 : CollatzResearch.WordTrace tailWord_1044080 prefixEnd_1044080 119136640388084503532971 := by
  unfold tailWord_1044080
  simp only [CollatzResearch.WordTrace]
  refine ⟨19040363028741974756376847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25387150704989299675169129 19040363028741974756376847)
  ·
    refine ⟨28560544543112962134565271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19040363028741974756376847 28560544543112962134565271)
    ·
      refine ⟨42840816814669443201847907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28560544543112962134565271 42840816814669443201847907)
      ·
        refine ⟨64261225222004164802771861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42840816814669443201847907 64261225222004164802771861)
        ·
          refine ⟨3012244932281445225129931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64261225222004164802771861 3012244932281445225129931)
          ·
            refine ⟨4518367398422167837694897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012244932281445225129931 4518367398422167837694897)
            ·
              refine ⟨3388775548816625878271173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4518367398422167837694897 3388775548816625878271173)
              ·
                refine ⟨635395415403117352175845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3388775548816625878271173 635395415403117352175845)
                ·
                  refine ⟨119136640388084503532971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635395415403117352175845 119136640388084503532971)
                  ·
                    rfl

theorem cell22_1044080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 4].length) (baseStart_1044080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044080 prefixEnd_1044080 := by exact prefixLift 1044080
  have htrace : WordTrace (prefixWord ++ tailWord_1044080) baseStart_1044080 baseEnd_1044080 := by
    simpa [prefixWord, tailWord_1044080, baseEnd_1044080] using wordTrace_append hprefix tailTrace_1044080
  have hstable : (prefixWord ++ tailWord_1044080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044080).length < 2 ^ (prefixWord ++ tailWord_1044080).sum := by decide
  have hdescent : baseEnd_1044080 < baseStart_1044080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044091 : List Nat := [1, 1, 1, 1, 1, 4, 4, 9]
def baseStart_1044091 : Nat := 118140960795 + 1044091 * 2 ^ 59
def prefixEnd_1044091 : Nat := 4983230072969 + 3 ^ 40 * 1044091 * 2
def baseEnd_1044091 : Nat := 39712631854339238730431

theorem tailTrace_1044091 : CollatzResearch.WordTrace tailWord_1044091 prefixEnd_1044091 39712631854339238730431 := by
  unfold tailWord_1044091
  simp only [CollatzResearch.WordTrace]
  refine ⟨38081127260444098391404127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25387418173629398927602751 38081127260444098391404127)
  ·
    refine ⟨57121690890666147587106191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38081127260444098391404127 57121690890666147587106191)
    ·
      refine ⟨85682536335999221380659287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57121690890666147587106191 85682536335999221380659287)
      ·
        refine ⟨128523804503998832070988931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85682536335999221380659287 128523804503998832070988931)
        ·
          refine ⟨192785706755998248106483397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128523804503998832070988931 192785706755998248106483397)
          ·
            refine ⟨36147320016749671519965637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192785706755998248106483397 36147320016749671519965637)
            ·
              refine ⟨6777622503140563409993557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36147320016749671519965637 6777622503140563409993557)
              ·
                refine ⟨39712631854339238730431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6777622503140563409993557 39712631854339238730431)
                ·
                  rfl

theorem cell22_1044091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 9].length) (baseStart_1044091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044091 prefixEnd_1044091 := by exact prefixLift 1044091
  have htrace : WordTrace (prefixWord ++ tailWord_1044091) baseStart_1044091 baseEnd_1044091 := by
    simpa [prefixWord, tailWord_1044091, baseEnd_1044091] using wordTrace_append hprefix tailTrace_1044091
  have hstable : (prefixWord ++ tailWord_1044091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044091).length < 2 ^ (prefixWord ++ tailWord_1044091).sum := by decide
  have hdescent : baseEnd_1044091 < baseStart_1044091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044093 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1044093 : Nat := 118140960795 + 1044093 * 2 ^ 59
def prefixEnd_1044093 : Nat := 4983230072969 + 3 ^ 40 * 1044093 * 2
def baseEnd_1044093 : Nat := 357414371329925810023873

theorem tailTrace_1044093 : CollatzResearch.WordTrace tailWord_1044093 prefixEnd_1044093 357414371329925810023873 := by
  unfold tailWord_1044093
  simp only [CollatzResearch.WordTrace]
  refine ⟨38081200206436852732976933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25387466804291235155317955 38081200206436852732976933)
  ·
    refine ⟨7140225038706909887433175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38081200206436852732976933 7140225038706909887433175)
    ·
      refine ⟨10710337558060364831149763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7140225038706909887433175 10710337558060364831149763)
      ·
        refine ⟨16065506337090547246724645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10710337558060364831149763 16065506337090547246724645)
        ·
          refine ⟨3012282438204477608760871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16065506337090547246724645 3012282438204477608760871)
          ·
            refine ⟨4518423657306716413141307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012282438204477608760871 4518423657306716413141307)
            ·
              refine ⟨6777635485960074619711961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518423657306716413141307 6777635485960074619711961)
              ·
                refine ⟨5083226614470055964783971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6777635485960074619711961 5083226614470055964783971)
                ·
                  refine ⟨7624839921705083947175957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083226614470055964783971 7624839921705083947175957)
                  ·
                    refine ⟨357414371329925810023873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7624839921705083947175957 357414371329925810023873)
                    ·
                      rfl

theorem cell22_1044093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1044093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044093 prefixEnd_1044093 := by exact prefixLift 1044093
  have htrace : WordTrace (prefixWord ++ tailWord_1044093) baseStart_1044093 baseEnd_1044093 := by
    simpa [prefixWord, tailWord_1044093, baseEnd_1044093] using wordTrace_append hprefix tailTrace_1044093
  have hstable : (prefixWord ++ tailWord_1044093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044093).length < 2 ^ (prefixWord ++ tailWord_1044093).sum := by decide
  have hdescent : baseEnd_1044093 < baseStart_1044093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044114 : List Nat := [3, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_1044114 : Nat := 118140960795 + 1044114 * 2 ^ 59
def prefixEnd_1044114 : Nat := 4983230072969 + 3 ^ 40 * 1044114 * 2
def baseEnd_1044114 : Nat := 119140520019696251749603

theorem tailTrace_1044114 : CollatzResearch.WordTrace tailWord_1044114 prefixEnd_1044114 119140520019696251749603 := by
  unfold tailWord_1044114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520491534840193329872849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25387977426240515546327597 9520491534840193329872849)
  ·
    refine ⟨7140368651130144997404637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9520491534840193329872849 7140368651130144997404637)
    ·
      refine ⟨2677638244173804374026739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7140368651130144997404637 2677638244173804374026739)
      ·
        refine ⟨4016457366260706561040109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677638244173804374026739 4016457366260706561040109)
        ·
          refine ⟨1506171512347764960390041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4016457366260706561040109 1506171512347764960390041)
          ·
            refine ⟨1129628634260823720292531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506171512347764960390041 1129628634260823720292531)
            ·
              refine ⟨1694442951391235580438797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129628634260823720292531 1694442951391235580438797)
              ·
                refine ⟨635416106771713342664549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1694442951391235580438797 635416106771713342664549)
                ·
                  refine ⟨119140520019696251749603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635416106771713342664549 119140520019696251749603)
                  ·
                    rfl

theorem cell22_1044114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_1044114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044114 prefixEnd_1044114 := by exact prefixLift 1044114
  have htrace : WordTrace (prefixWord ++ tailWord_1044114) baseStart_1044114 baseEnd_1044114 := by
    simpa [prefixWord, tailWord_1044114, baseEnd_1044114] using wordTrace_append hprefix tailTrace_1044114
  have hstable : (prefixWord ++ tailWord_1044114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044114).length < 2 ^ (prefixWord ++ tailWord_1044114).sum := by decide
  have hdescent : baseEnd_1044114 < baseStart_1044114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044127 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 2, 4]
def baseStart_1044127 : Nat := 118140960795 + 1044127 * 2 ^ 59
def prefixEnd_1044127 : Nat := 4983230072969 + 3 ^ 40 * 1044127 * 2
def baseEnd_1044127 : Nat := 357426010224761054673769

theorem tailTrace_1044127 : CollatzResearch.WordTrace tailWord_1044127 prefixEnd_1044127 357426010224761054673769 := by
  unfold tailWord_1044127
  simp only [CollatzResearch.WordTrace]
  refine ⟨38082440288313676539714635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25388293525542451026476423 38082440288313676539714635)
  ·
    refine ⟨57123660432470514809571953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38082440288313676539714635 57123660432470514809571953)
    ·
      refine ⟨42842745324352886107178965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57123660432470514809571953 42842745324352886107178965)
      ·
        refine ⟨1004126843539520768137007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 42842745324352886107178965 1004126843539520768137007)
        ·
          refine ⟨1506190265309281152205511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004126843539520768137007 1506190265309281152205511)
          ·
            refine ⟨2259285397963921728308267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506190265309281152205511 2259285397963921728308267)
            ·
              refine ⟨3388928096945882592462401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259285397963921728308267 3388928096945882592462401)
              ·
                refine ⟨2541696072709411944346801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388928096945882592462401 2541696072709411944346801)
                ·
                  refine ⟨1906272054532058958260101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2541696072709411944346801 1906272054532058958260101)
                  ·
                    refine ⟨357426010224761054673769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1906272054532058958260101 357426010224761054673769)
                    ·
                      rfl

theorem cell22_1044127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_1044127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044127 prefixEnd_1044127 := by exact prefixLift 1044127
  have htrace : WordTrace (prefixWord ++ tailWord_1044127) baseStart_1044127 baseEnd_1044127 := by
    simpa [prefixWord, tailWord_1044127, baseEnd_1044127] using wordTrace_append hprefix tailTrace_1044127
  have hstable : (prefixWord ++ tailWord_1044127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044127).length < 2 ^ (prefixWord ++ tailWord_1044127).sum := by decide
  have hdescent : baseEnd_1044127 < baseStart_1044127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044142 : List Nat := [4, 1, 4, 1, 2, 1, 2, 7]
def baseStart_1044142 : Nat := 118140960795 + 1044142 * 2 ^ 59
def prefixEnd_1044142 : Nat := 4983230072969 + 3 ^ 40 * 1044142 * 2
def baseEnd_1044142 : Nat := 39714571670145112838747

theorem tailTrace_1044142 : CollatzResearch.WordTrace tailWord_1044142 prefixEnd_1044142 39714571670145112838747 := by
  unfold tailWord_1044142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4760373422907416762688835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25388658255506222734340453 4760373422907416762688835)
  ·
    refine ⟨7140560134361125144033253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4760373422907416762688835 7140560134361125144033253)
    ·
      refine ⟨1338855025192710964506235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7140560134361125144033253 1338855025192710964506235)
      ·
        refine ⟨2008282537789066446759353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338855025192710964506235 2008282537789066446759353)
        ·
          refine ⟨1506211903341799835069515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2008282537789066446759353 1506211903341799835069515)
          ·
            refine ⟨2259317855012699752604273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506211903341799835069515 2259317855012699752604273)
            ·
              refine ⟨1694488391259524814453205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2259317855012699752604273 1694488391259524814453205)
              ·
                refine ⟨39714571670145112838747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1694488391259524814453205 39714571670145112838747)
                ·
                  rfl

theorem cell22_1044142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_1044142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044142 prefixEnd_1044142 := by exact prefixLift 1044142
  have htrace : WordTrace (prefixWord ++ tailWord_1044142) baseStart_1044142 baseEnd_1044142 := by
    simpa [prefixWord, tailWord_1044142, baseEnd_1044142] using wordTrace_append hprefix tailTrace_1044142
  have hstable : (prefixWord ++ tailWord_1044142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044142).length < 2 ^ (prefixWord ++ tailWord_1044142).sum := by decide
  have hdescent : baseEnd_1044142 < baseStart_1044142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044200 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1044200 : Nat := 118140960795 + 1044200 * 2 ^ 59
def prefixEnd_1044200 : Nat := 4983230072969 + 3 ^ 40 * 1044200 * 2
def baseEnd_1044200 : Nat := 357450999616613197598545

theorem tailTrace_1044200 : CollatzResearch.WordTrace tailWord_1044200 prefixEnd_1044200 357450999616613197598545 := by
  unfold tailWord_1044200
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042551408524605003561027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25390068544699473338081369 19042551408524605003561027)
  ·
    refine ⟨28563827112786907505341541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19042551408524605003561027 28563827112786907505341541)
    ·
      refine ⟨5355717583647545157251539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28563827112786907505341541 5355717583647545157251539)
      ·
        refine ⟨8033576375471317735877309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5355717583647545157251539 8033576375471317735877309)
        ·
          refine ⟨3012591140801744150953991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8033576375471317735877309 3012591140801744150953991)
          ·
            refine ⟨4518886711202616226430987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012591140801744150953991 4518886711202616226430987)
            ·
              refine ⟨6778330066803924339646481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518886711202616226430987 6778330066803924339646481)
              ·
                refine ⟨5083747550102943254734861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6778330066803924339646481 5083747550102943254734861)
                ·
                  refine ⟨1906405331288603720525573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5083747550102943254734861 1906405331288603720525573)
                  ·
                    refine ⟨357450999616613197598545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1906405331288603720525573 357450999616613197598545)
                    ·
                      rfl

theorem cell22_1044200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1044200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044200 prefixEnd_1044200 := by exact prefixLift 1044200
  have htrace : WordTrace (prefixWord ++ tailWord_1044200) baseStart_1044200 baseEnd_1044200 := by
    simpa [prefixWord, tailWord_1044200, baseEnd_1044200] using wordTrace_append hprefix tailTrace_1044200
  have hstable : (prefixWord ++ tailWord_1044200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044200).length < 2 ^ (prefixWord ++ tailWord_1044200).sum := by decide
  have hdescent : baseEnd_1044200 < baseStart_1044200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044232 : List Nat := [2, 1, 3, 2, 2, 1, 4, 3, 4]
def baseStart_1044232 : Nat := 118140960795 + 1044232 * 2 ^ 59
def prefixEnd_1044232 : Nat := 4983230072969 + 3 ^ 40 * 1044232 * 2
def baseEnd_1044232 : Nat := 119153984623525260266149

theorem tailTrace_1044232 : CollatzResearch.WordTrace tailWord_1044232 prefixEnd_1044232 119153984623525260266149 := by
  unfold tailWord_1044232
  simp only [CollatzResearch.WordTrace]
  refine ⟨19043134976466639736143475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25390846635288852981524633 19043134976466639736143475)
  ·
    refine ⟨28564702464699959604215213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19043134976466639736143475 28564702464699959604215213)
    ·
      refine ⟨10711763424262484851580705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28564702464699959604215213 10711763424262484851580705)
      ·
        refine ⟨8033822568196863638685529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10711763424262484851580705 8033822568196863638685529)
        ·
          refine ⟨6025366926147647729014147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8033822568196863638685529 6025366926147647729014147)
          ·
            refine ⟨9038050389221471593521221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6025366926147647729014147 9038050389221471593521221)
            ·
              refine ⟨1694634447979025923785229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9038050389221471593521221 1694634447979025923785229)
              ·
                refine ⟨635487917992134721419461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1694634447979025923785229 635487917992134721419461)
                ·
                  refine ⟨119153984623525260266149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635487917992134721419461 119153984623525260266149)
                  ·
                    rfl

theorem cell22_1044232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 4].length) (baseStart_1044232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044232 prefixEnd_1044232 := by exact prefixLift 1044232
  have htrace : WordTrace (prefixWord ++ tailWord_1044232) baseStart_1044232 baseEnd_1044232 := by
    simpa [prefixWord, tailWord_1044232, baseEnd_1044232] using wordTrace_append hprefix tailTrace_1044232
  have hstable : (prefixWord ++ tailWord_1044232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044232).length < 2 ^ (prefixWord ++ tailWord_1044232).sum := by decide
  have hdescent : baseEnd_1044232 < baseStart_1044232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044234 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 1, 4]
def baseStart_1044234 : Nat := 118140960795 + 1044234 * 2 ^ 59
def prefixEnd_1044234 : Nat := 4983230072969 + 3 ^ 40 * 1044234 * 2
def baseEnd_1044234 : Nat := 357462638511448442248441

theorem tailTrace_1044234 : CollatzResearch.WordTrace tailWord_1044234 prefixEnd_1044234 357462638511448442248441 := by
  unfold tailWord_1044234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9521585724731508453464939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25390895265950689209239837 9521585724731508453464939)
  ·
    refine ⟨14282378587097262680197409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9521585724731508453464939 14282378587097262680197409)
    ·
      refine ⟨10711783940322947010148057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14282378587097262680197409 10711783940322947010148057)
      ·
        refine ⟨8033837955242210257611043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10711783940322947010148057 8033837955242210257611043)
        ·
          refine ⟨12050756932863315386416565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8033837955242210257611043 12050756932863315386416565)
          ·
            refine ⟨1129758462455935817476553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12050756932863315386416565 1129758462455935817476553)
            ·
              refine ⟨847318846841951863107415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129758462455935817476553 847318846841951863107415)
              ·
                refine ⟨1270978270262927794661123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847318846841951863107415 1270978270262927794661123)
                ·
                  refine ⟨1906467405394391691991685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270978270262927794661123 1906467405394391691991685)
                  ·
                    refine ⟨357462638511448442248441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1906467405394391691991685 357462638511448442248441)
                    ·
                      rfl

theorem cell22_1044234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_1044234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044234 prefixEnd_1044234 := by exact prefixLift 1044234
  have htrace : WordTrace (prefixWord ++ tailWord_1044234) baseStart_1044234 baseEnd_1044234 := by
    simpa [prefixWord, tailWord_1044234, baseEnd_1044234] using wordTrace_append hprefix tailTrace_1044234
  have hstable : (prefixWord ++ tailWord_1044234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044234).length < 2 ^ (prefixWord ++ tailWord_1044234).sum := by decide
  have hdescent : baseEnd_1044234 < baseStart_1044234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044247 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 4, 3]
def baseStart_1044247 : Nat := 118140960795 + 1044247 * 2 ^ 59
def prefixEnd_1044247 : Nat := 4983230072969 + 3 ^ 40 * 1044247 * 2
def baseEnd_1044247 : Nat := 357467088677120741673401

theorem tailTrace_1044247 : CollatzResearch.WordTrace tailWord_1044247 prefixEnd_1044247 357467088677120741673401 := by
  unfold tailWord_1044247
  simp only [CollatzResearch.WordTrace]
  refine ⟨38086817047878937034082995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25391211365252624689388663 38086817047878937034082995)
  ·
    refine ⟨57130225571818405551124493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38086817047878937034082995 57130225571818405551124493)
    ·
      refine ⟨21423834589431902081671685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57130225571818405551124493 21423834589431902081671685)
      ·
        refine ⟨4016968985518481640313441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21423834589431902081671685 4016968985518481640313441)
        ·
          refine ⟨3012726739138861230235081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4016968985518481640313441 3012726739138861230235081)
          ·
            refine ⟨2259545054354145922676311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012726739138861230235081 2259545054354145922676311)
            ·
              refine ⟨3389317581531218884014467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259545054354145922676311 3389317581531218884014467)
              ·
                refine ⟨5083976372296828326021701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389317581531218884014467 5083976372296828326021701)
                ·
                  refine ⟨953245569805655311129069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5083976372296828326021701 953245569805655311129069)
                  ·
                    refine ⟨357467088677120741673401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 953245569805655311129069 357467088677120741673401)
                    ·
                      rfl

theorem cell22_1044247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_1044247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044247 prefixEnd_1044247 := by exact prefixLift 1044247
  have htrace : WordTrace (prefixWord ++ tailWord_1044247) baseStart_1044247 baseEnd_1044247 := by
    simpa [prefixWord, tailWord_1044247, baseEnd_1044247] using wordTrace_append hprefix tailTrace_1044247
  have hstable : (prefixWord ++ tailWord_1044247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044247).length < 2 ^ (prefixWord ++ tailWord_1044247).sum := by decide
  have hdescent : baseEnd_1044247 < baseStart_1044247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044294 : List Nat := [6, 1, 1, 2, 1, 3, 8]
def baseStart_1044294 : Nat := 118140960795 + 1044294 * 2 ^ 59
def prefixEnd_1044294 : Nat := 4983230072969 + 3 ^ 40 * 1044294 * 2
def baseEnd_1044294 : Nat := 13240117693986232805491

theorem tailTrace_1044294 : CollatzResearch.WordTrace tailWord_1044294 prefixEnd_1044294 13240117693986232805491 := by
  unfold tailWord_1044294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190266602459645751907623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25392354185805776040695957 1190266602459645751907623)
  ·
    refine ⟨1785399903689468627861435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1190266602459645751907623 1785399903689468627861435)
    ·
      refine ⟨2678099855534202941792153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785399903689468627861435 2678099855534202941792153)
      ·
        refine ⟨2008574891650652206344115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2678099855534202941792153 2008574891650652206344115)
        ·
          refine ⟨3012862337475978309516173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008574891650652206344115 3012862337475978309516173)
          ·
            refine ⟨1129823376553491866068565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3012862337475978309516173 1129823376553491866068565)
            ·
              refine ⟨13240117693986232805491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1129823376553491866068565 13240117693986232805491)
              ·
                rfl

theorem cell22_1044294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 8].length) (baseStart_1044294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044294 prefixEnd_1044294 := by exact prefixLift 1044294
  have htrace : WordTrace (prefixWord ++ tailWord_1044294) baseStart_1044294 baseEnd_1044294 := by
    simpa [prefixWord, tailWord_1044294, baseEnd_1044294] using wordTrace_append hprefix tailTrace_1044294
  have hstable : (prefixWord ++ tailWord_1044294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044294).length < 2 ^ (prefixWord ++ tailWord_1044294).sum := by decide
  have hdescent : baseEnd_1044294 < baseStart_1044294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044305 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 7]
def baseStart_1044305 : Nat := 118140960795 + 1044305 * 2 ^ 59
def prefixEnd_1044305 : Nat := 4983230072969 + 3 ^ 40 * 1044305 * 2
def baseEnd_1044305 : Nat := 119162314420809307907741

theorem tailTrace_1044305 : CollatzResearch.WordTrace tailWord_1044305 prefixEnd_1044305 119162314420809307907741 := by
  unfold tailWord_1044305
  simp only [CollatzResearch.WordTrace]
  refine ⟨38088932481668812939694369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25392621654445875293129579 38088932481668812939694369)
  ·
    refine ⟨28566699361251609704770777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38088932481668812939694369 28566699361251609704770777)
    ·
      refine ⟨21425024520938707278578083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28566699361251609704770777 21425024520938707278578083)
      ·
        refine ⟨32137536781408060917867125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21425024520938707278578083 32137536781408060917867125)
        ·
          refine ⟨3012894073257005711050043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32137536781408060917867125 3012894073257005711050043)
          ·
            refine ⟨4519341109885508566575065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012894073257005711050043 4519341109885508566575065)
            ·
              refine ⟨3389505832414131424931299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4519341109885508566575065 3389505832414131424931299)
              ·
                refine ⟨5084258748621197137396949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389505832414131424931299 5084258748621197137396949)
                ·
                  refine ⟨119162314420809307907741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5084258748621197137396949 119162314420809307907741)
                  ·
                    rfl

theorem cell22_1044305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_1044305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044305 prefixEnd_1044305 := by exact prefixLift 1044305
  have htrace : WordTrace (prefixWord ++ tailWord_1044305) baseStart_1044305 baseEnd_1044305 := by
    simpa [prefixWord, tailWord_1044305, baseEnd_1044305] using wordTrace_append hprefix tailTrace_1044305
  have hstable : (prefixWord ++ tailWord_1044305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044305).length < 2 ^ (prefixWord ++ tailWord_1044305).sum := by decide
  have hdescent : baseEnd_1044305 < baseStart_1044305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044309 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_1044309 : Nat := 118140960795 + 1044309 * 2 ^ 59
def prefixEnd_1044309 : Nat := 4983230072969 + 3 ^ 40 * 1044309 * 2
def baseEnd_1044309 : Nat := 357488312544173246623211

theorem tailTrace_1044309 : CollatzResearch.WordTrace tailWord_1044309 prefixEnd_1044309 357488312544173246623211 := by
  unfold tailWord_1044309
  simp only [CollatzResearch.WordTrace]
  refine ⟨38089078373654321622839981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25392718915769547748559987 38089078373654321622839981)
  ·
    refine ⟨14283404390120370608564993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38089078373654321622839981 14283404390120370608564993)
    ·
      refine ⟨10712553292590277956423745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14283404390120370608564993 10712553292590277956423745)
      ·
        refine ⟨8034414969442708467317809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10712553292590277956423745 8034414969442708467317809)
        ·
          refine ⟨6025811227082031350488357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8034414969442708467317809 6025811227082031350488357)
          ·
            refine ⟨1129839605077880878216567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6025811227082031350488357 1129839605077880878216567)
            ·
              refine ⟨1694759407616821317324851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129839605077880878216567 1694759407616821317324851)
              ·
                refine ⟨2542139111425231975987277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694759407616821317324851 2542139111425231975987277)
                ·
                  refine ⟨953302166784461990995229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2542139111425231975987277 953302166784461990995229)
                  ·
                    refine ⟨357488312544173246623211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 953302166784461990995229 357488312544173246623211)
                    ·
                      rfl

theorem cell22_1044309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_1044309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044309 prefixEnd_1044309 := by exact prefixLift 1044309
  have htrace : WordTrace (prefixWord ++ tailWord_1044309) baseStart_1044309 baseEnd_1044309 := by
    simpa [prefixWord, tailWord_1044309, baseEnd_1044309] using wordTrace_append hprefix tailTrace_1044309
  have hstable : (prefixWord ++ tailWord_1044309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044309).length < 2 ^ (prefixWord ++ tailWord_1044309).sum := by decide
  have hdescent : baseEnd_1044309 < baseStart_1044309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044360 : List Nat := [2, 1, 3, 3, 4, 1, 2, 2, 1, 3]
def baseStart_1044360 : Nat := 118140960795 + 1044360 * 2 ^ 59
def prefixEnd_1044360 : Nat := 4983230072969 + 3 ^ 40 * 1044360 * 2
def baseEnd_1044360 : Nat := 357505770886426113598055

theorem tailTrace_1044360 : CollatzResearch.WordTrace tailWord_1044360 prefixEnd_1044360 357505770886426113598055 := by
  unfold tailWord_1044360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19045469248234778666473267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25393958997646371555297689 19045469248234778666473267)
  ·
    refine ⟨28568203872352167999709901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19045469248234778666473267 28568203872352167999709901)
    ·
      refine ⟨10713076452132062999891213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28568203872352167999709901 10713076452132062999891213)
      ·
        refine ⟨4017403669549523624959205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10713076452132062999891213 4017403669549523624959205)
        ·
          refine ⟨753263188040535679679851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4017403669549523624959205 753263188040535679679851)
          ·
            refine ⟨1129894782060803519519777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753263188040535679679851 1129894782060803519519777)
            ·
              refine ⟨847421086545602639639833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129894782060803519519777 847421086545602639639833)
              ·
                refine ⟨635565814909201979729875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847421086545602639639833 635565814909201979729875)
                ·
                  refine ⟨953348722363802969594813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635565814909201979729875 953348722363802969594813)
                  ·
                    refine ⟨357505770886426113598055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 953348722363802969594813 357505770886426113598055)
                    ·
                      rfl

theorem cell22_1044360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_1044360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044360 prefixEnd_1044360 := by exact prefixLift 1044360
  have htrace : WordTrace (prefixWord ++ tailWord_1044360) baseStart_1044360 baseEnd_1044360 := by
    simpa [prefixWord, tailWord_1044360, baseEnd_1044360] using wordTrace_append hprefix tailTrace_1044360
  have hstable : (prefixWord ++ tailWord_1044360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044360).length < 2 ^ (prefixWord ++ tailWord_1044360).sum := by decide
  have hdescent : baseEnd_1044360 < baseStart_1044360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044478 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1044478 : Nat := 118140960795 + 1044478 * 2 ^ 59
def prefixEnd_1044478 : Nat := 4983230072969 + 3 ^ 40 * 1044478 * 2
def baseEnd_1044478 : Nat := 357546164697913139147693

theorem tailTrace_1044478 : CollatzResearch.WordTrace tailWord_1044478 prefixEnd_1044478 357546164697913139147693 := by
  unfold tailWord_1044478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4761905288755257935717761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25396828206694708990494725 4761905288755257935717761)
  ·
    refine ⟨3571428966566443451788321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4761905288755257935717761 3571428966566443451788321)
    ·
      refine ⟨2678571724924832588841241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3571428966566443451788321 2678571724924832588841241)
      ·
        refine ⟨2008928793693624441630931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2678571724924832588841241 2008928793693624441630931)
        ·
          refine ⟨3013393190540436662446397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008928793693624441630931 3013393190540436662446397)
          ·
            refine ⟨1130022446452663748417399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3013393190540436662446397 1130022446452663748417399)
            ·
              refine ⟨1695033669678995622626099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130022446452663748417399 1695033669678995622626099)
              ·
                refine ⟨2542550504518493433939149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695033669678995622626099 2542550504518493433939149)
                ·
                  refine ⟨953456439194435037727181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2542550504518493433939149 953456439194435037727181)
                  ·
                    refine ⟨357546164697913139147693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 953456439194435037727181 357546164697913139147693)
                    ·
                      rfl

theorem cell22_1044478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1044478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044478 prefixEnd_1044478 := by exact prefixLift 1044478
  have htrace : WordTrace (prefixWord ++ tailWord_1044478) baseStart_1044478 baseEnd_1044478 := by
    simpa [prefixWord, tailWord_1044478, baseEnd_1044478] using wordTrace_append hprefix tailTrace_1044478
  have hstable : (prefixWord ++ tailWord_1044478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044478).length < 2 ^ (prefixWord ++ tailWord_1044478).sum := by decide
  have hdescent : baseEnd_1044478 < baseStart_1044478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044517 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1044517 : Nat := 118140960795 + 1044517 * 2 ^ 59
def prefixEnd_1044517 : Nat := 4983230072969 + 3 ^ 40 * 1044517 * 2
def baseEnd_1044517 : Nat := 357559515194930037422573

theorem tailTrace_1044517 : CollatzResearch.WordTrace tailWord_1044517 prefixEnd_1044517 357559515194930037422573 := by
  unfold tailWord_1044517
  simp only [CollatzResearch.WordTrace]
  refine ⟨38096664756900773146411805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25397776504600515430941203 38096664756900773146411805)
  ·
    refine ⟨14286249283837789929904427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38096664756900773146411805 14286249283837789929904427)
    ·
      refine ⟨21429373925756684894856641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14286249283837789929904427 21429373925756684894856641)
      ·
        refine ⟨16072030444317513671142481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21429373925756684894856641 16072030444317513671142481)
        ·
          refine ⟨12054022833238135253356861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16072030444317513671142481 12054022833238135253356861)
          ·
            refine ⟨4520258562464300720008823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12054022833238135253356861 4520258562464300720008823)
            ·
              refine ⟨6780387843696451080013235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520258562464300720008823 6780387843696451080013235)
              ·
                refine ⟨10170581765544676620019853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6780387843696451080013235 10170581765544676620019853)
                ·
                  refine ⟨3813968162079253732507445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10170581765544676620019853 3813968162079253732507445)
                  ·
                    refine ⟨357559515194930037422573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3813968162079253732507445 357559515194930037422573)
                    ·
                      rfl

theorem cell22_1044517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1044517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044517 prefixEnd_1044517 := by exact prefixLift 1044517
  have htrace : WordTrace (prefixWord ++ tailWord_1044517) baseStart_1044517 baseEnd_1044517 := by
    simpa [prefixWord, tailWord_1044517, baseEnd_1044517] using wordTrace_append hprefix tailTrace_1044517
  have hstable : (prefixWord ++ tailWord_1044517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044517).length < 2 ^ (prefixWord ++ tailWord_1044517).sum := by decide
  have hdescent : baseEnd_1044517 < baseStart_1044517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044534 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1044534 : Nat := 118140960795 + 1044534 * 2 ^ 59
def prefixEnd_1044534 : Nat := 4983230072969 + 3 ^ 40 * 1044534 * 2
def baseEnd_1044534 : Nat := 357565334642347659747521

theorem tailTrace_1044534 : CollatzResearch.WordTrace tailWord_1044534 prefixEnd_1044534 357565334642347659747521 := by
  unfold tailWord_1044534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2381080299864949065611291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25398189865226123366520437 2381080299864949065611291)
  ·
    refine ⟨3571620449797423598416937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2381080299864949065611291 3571620449797423598416937)
    ·
      refine ⟨2678715337348067698812703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3571620449797423598416937 2678715337348067698812703)
      ·
        refine ⟨4018073006022101548219055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678715337348067698812703 4018073006022101548219055)
        ·
          refine ⟨6027109509033152322328583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018073006022101548219055 6027109509033152322328583)
          ·
            refine ⟨9040664263549728483492875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027109509033152322328583 9040664263549728483492875)
            ·
              refine ⟨13560996395324592725239313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040664263549728483492875 13560996395324592725239313)
              ·
                refine ⟨10170747296493444543929485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13560996395324592725239313 10170747296493444543929485)
                ·
                  refine ⟨3814030236185041703973557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10170747296493444543929485 3814030236185041703973557)
                  ·
                    refine ⟨357565334642347659747521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3814030236185041703973557 357565334642347659747521)
                    ·
                      rfl

theorem cell22_1044534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1044534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044534 prefixEnd_1044534 := by exact prefixLift 1044534
  have htrace : WordTrace (prefixWord ++ tailWord_1044534) baseStart_1044534 baseEnd_1044534 := by
    simpa [prefixWord, tailWord_1044534, baseEnd_1044534] using wordTrace_append hprefix tailTrace_1044534
  have hstable : (prefixWord ++ tailWord_1044534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044534).length < 2 ^ (prefixWord ++ tailWord_1044534).sum := by decide
  have hdescent : baseEnd_1044534 < baseStart_1044534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044536 : List Nat := [2, 1, 2, 1, 6, 1, 1, 4, 4]
def baseStart_1044536 : Nat := 118140960795 + 1044536 * 2 ^ 59
def prefixEnd_1044536 : Nat := 4983230072969 + 3 ^ 40 * 1044536 * 2
def baseEnd_1044536 : Nat := 119188673094406773732505

theorem tailTrace_1044536 : CollatzResearch.WordTrace tailWord_1044536 prefixEnd_1044536 119188673094406773732505 := by
  unfold tailWord_1044536
  simp only [CollatzResearch.WordTrace]
  refine ⟨19048678871915969695676731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25398238495887959594235641 19048678871915969695676731)
  ·
    refine ⟨28573018307873954543515097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19048678871915969695676731 28573018307873954543515097)
    ·
      refine ⟨21429763730905465907636323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28573018307873954543515097 21429763730905465907636323)
      ·
        refine ⟨32144645596358198861454485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21429763730905465907636323 32144645596358198861454485)
        ·
          refine ⟨1506780262329290571630679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32144645596358198861454485 1506780262329290571630679)
          ·
            refine ⟨2260170393493935857446019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506780262329290571630679 2260170393493935857446019)
            ·
              refine ⟨3390255590240903786169029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260170393493935857446019 3390255590240903786169029)
              ·
                refine ⟨635672923170169459906693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3390255590240903786169029 635672923170169459906693)
                ·
                  refine ⟨119188673094406773732505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635672923170169459906693 119188673094406773732505)
                  ·
                    rfl

theorem cell22_1044536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 4].length) (baseStart_1044536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044536 prefixEnd_1044536 := by exact prefixLift 1044536
  have htrace : WordTrace (prefixWord ++ tailWord_1044536) baseStart_1044536 baseEnd_1044536 := by
    simpa [prefixWord, tailWord_1044536, baseEnd_1044536] using wordTrace_append hprefix tailTrace_1044536
  have hstable : (prefixWord ++ tailWord_1044536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044536).length < 2 ^ (prefixWord ++ tailWord_1044536).sum := by decide
  have hdescent : baseEnd_1044536 < baseStart_1044536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044647 : List Nat := [1, 1, 6, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1044647 : Nat := 118140960795 + 1044647 * 2 ^ 59
def prefixEnd_1044647 : Nat := 4983230072969 + 3 ^ 40 * 1044647 * 2
def baseEnd_1044647 : Nat := 357604016851653031672175

theorem tailTrace_1044647 : CollatzResearch.WordTrace tailWord_1044647 prefixEnd_1044647 357604016851653031672175 := by
  unfold tailWord_1044647
  simp only [CollatzResearch.WordTrace]
  refine ⟨38101406246429805348644195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25400937497619870232429463 38101406246429805348644195)
  ·
    refine ⟨57152109369644708022966293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38101406246429805348644195 57152109369644708022966293)
    ·
      refine ⟨2679005126702095688576545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57152109369644708022966293 2679005126702095688576545)
      ·
        refine ⟨2009253845026571766432409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2679005126702095688576545 2009253845026571766432409)
        ·
          refine ⟨1506940383769928824824307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009253845026571766432409 1506940383769928824824307)
          ·
            refine ⟨2260410575654893237236461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506940383769928824824307 2260410575654893237236461)
            ·
              refine ⟨847653965870584963963673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2260410575654893237236461 847653965870584963963673)
              ·
                refine ⟨635740474402938722972755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847653965870584963963673 635740474402938722972755)
                ·
                  refine ⟨953610711604408084459133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635740474402938722972755 953610711604408084459133)
                  ·
                    refine ⟨357604016851653031672175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 953610711604408084459133 357604016851653031672175)
                    ·
                      rfl

theorem cell22_1044647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1044647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044647 prefixEnd_1044647 := by exact prefixLift 1044647
  have htrace : WordTrace (prefixWord ++ tailWord_1044647) baseStart_1044647 baseEnd_1044647 := by
    simpa [prefixWord, tailWord_1044647, baseEnd_1044647] using wordTrace_append hprefix tailTrace_1044647
  have hstable : (prefixWord ++ tailWord_1044647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044647).length < 2 ^ (prefixWord ++ tailWord_1044647).sum := by decide
  have hdescent : baseEnd_1044647 < baseStart_1044647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044669 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_1044669 : Nat := 118140960795 + 1044669 * 2 ^ 59
def prefixEnd_1044669 : Nat := 4983230072969 + 3 ^ 40 * 1044669 * 2
def baseEnd_1044669 : Nat := 357611547901252307622107

theorem tailTrace_1044669 : CollatzResearch.WordTrace tailWord_1044669 prefixEnd_1044669 357611547901252307622107 := by
  unfold tailWord_1044669
  simp only [CollatzResearch.WordTrace]
  refine ⟨38102208652350103105945061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25401472434900068737296707 38102208652350103105945061)
  ·
    refine ⟨7144164122315644332364699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38102208652350103105945061 7144164122315644332364699)
    ·
      refine ⟨10716246183473466498547049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7144164122315644332364699 10716246183473466498547049)
      ·
        refine ⟨8037184637605099873910287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10716246183473466498547049 8037184637605099873910287)
        ·
          refine ⟨12055776956407649810865431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037184637605099873910287 12055776956407649810865431)
          ·
            refine ⟨18083665434611474716298147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055776956407649810865431 18083665434611474716298147)
            ·
              refine ⟨27125498151917212074447221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18083665434611474716298147 27125498151917212074447221)
              ·
                refine ⟨2543015451742238631979427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27125498151917212074447221 2543015451742238631979427)
                ·
                  refine ⟨3814523177613357947969141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543015451742238631979427 3814523177613357947969141)
                  ·
                    refine ⟨357611547901252307622107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3814523177613357947969141 357611547901252307622107)
                    ·
                      rfl

theorem cell22_1044669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_1044669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044669 prefixEnd_1044669 := by exact prefixLift 1044669
  have htrace : WordTrace (prefixWord ++ tailWord_1044669) baseStart_1044669 baseEnd_1044669 := by
    simpa [prefixWord, tailWord_1044669, baseEnd_1044669] using wordTrace_append hprefix tailTrace_1044669
  have hstable : (prefixWord ++ tailWord_1044669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044669).length < 2 ^ (prefixWord ++ tailWord_1044669).sum := by decide
  have hdescent : baseEnd_1044669 < baseStart_1044669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044673 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1044673 : Nat := 118140960795 + 1044673 * 2 ^ 59
def prefixEnd_1044673 : Nat := 4983230072969 + 3 ^ 40 * 1044673 * 2
def baseEnd_1044673 : Nat := 357612917182997630522095

theorem tailTrace_1044673 : CollatzResearch.WordTrace tailWord_1044673 prefixEnd_1044673 357612917182997630522095 := by
  unfold tailWord_1044673
  simp only [CollatzResearch.WordTrace]
  refine ⟨38102354544335611789090673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25401569696223741192727115 38102354544335611789090673)
  ·
    refine ⟨28576765908251708841818005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38102354544335611789090673 28576765908251708841818005)
    ·
      refine ⟨1339535901949298851960219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28576765908251708841818005 1339535901949298851960219)
      ·
        refine ⟨2009303852923948277940329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339535901949298851960219 2009303852923948277940329)
        ·
          refine ⟨1506977889692961208455247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009303852923948277940329 1506977889692961208455247)
          ·
            refine ⟨2260466834539441812682871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506977889692961208455247 2260466834539441812682871)
            ·
              refine ⟨3390700251809162719024307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260466834539441812682871 3390700251809162719024307)
              ·
                refine ⟨5086050377713744078536461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390700251809162719024307 5086050377713744078536461)
                ·
                  refine ⟨1907268891642654029451173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5086050377713744078536461 1907268891642654029451173)
                  ·
                    refine ⟨357612917182997630522095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1907268891642654029451173 357612917182997630522095)
                    ·
                      rfl

theorem cell22_1044673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1044673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044673 prefixEnd_1044673 := by exact prefixLift 1044673
  have htrace : WordTrace (prefixWord ++ tailWord_1044673) baseStart_1044673 baseEnd_1044673 := by
    simpa [prefixWord, tailWord_1044673, baseEnd_1044673] using wordTrace_append hprefix tailTrace_1044673
  have hstable : (prefixWord ++ tailWord_1044673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044673).length < 2 ^ (prefixWord ++ tailWord_1044673).sum := by decide
  have hdescent : baseEnd_1044673 < baseStart_1044673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044686 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_1044686 : Nat := 118140960795 + 1044686 * 2 ^ 59
def prefixEnd_1044686 : Nat := 4983230072969 + 3 ^ 40 * 1044686 * 2
def baseEnd_1044686 : Nat := 357617367348669929947055

theorem tailTrace_1044686 : CollatzResearch.WordTrace tailWord_1044686 prefixEnd_1044686 357617367348669929947055 := by
  unfold tailWord_1044686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762853586661064376164239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25401885795525676672875941 4762853586661064376164239)
  ·
    refine ⟨7144280379991596564246359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4762853586661064376164239 7144280379991596564246359)
    ·
      refine ⟨10716420569987394846369539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7144280379991596564246359 10716420569987394846369539)
      ·
        refine ⟨16074630854981092269554309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10716420569987394846369539 16074630854981092269554309)
        ·
          refine ⟨3013993285308954800541433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16074630854981092269554309 3013993285308954800541433)
          ·
            refine ⟨2260494963981716100406075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3013993285308954800541433 2260494963981716100406075)
            ·
              refine ⟨3390742445972574150609113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260494963981716100406075 3390742445972574150609113)
              ·
                refine ⟨2543056834479430612956835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390742445972574150609113 2543056834479430612956835)
                ·
                  refine ⟨3814585251719145919435253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543056834479430612956835 3814585251719145919435253)
                  ·
                    refine ⟨357617367348669929947055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3814585251719145919435253 357617367348669929947055)
                    ·
                      rfl

theorem cell22_1044686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_1044686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044686 prefixEnd_1044686 := by exact prefixLift 1044686
  have htrace : WordTrace (prefixWord ++ tailWord_1044686) baseStart_1044686 baseEnd_1044686 := by
    simpa [prefixWord, tailWord_1044686, baseEnd_1044686] using wordTrace_append hprefix tailTrace_1044686
  have hstable : (prefixWord ++ tailWord_1044686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044686).length < 2 ^ (prefixWord ++ tailWord_1044686).sum := by decide
  have hdescent : baseEnd_1044686 < baseStart_1044686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044765 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1044765 : Nat := 118140960795 + 1044765 * 2 ^ 59
def prefixEnd_1044765 : Nat := 4983230072969 + 3 ^ 40 * 1044765 * 2
def baseEnd_1044765 : Nat := 357644410663140057221813

theorem tailTrace_1044765 : CollatzResearch.WordTrace tailWord_1044765 prefixEnd_1044765 357644410663140057221813 := by
  unfold tailWord_1044765
  simp only [CollatzResearch.WordTrace]
  refine ⟨38105710060002311501439749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25403806706668207667626499 38105710060002311501439749)
  ·
    refine ⟨7144820636250433406519953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38105710060002311501439749 7144820636250433406519953)
    ·
      refine ⟨5358615477187825054889965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7144820636250433406519953 5358615477187825054889965)
      ·
        refine ⟨2009480803945434395583737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5358615477187825054889965 2009480803945434395583737)
        ·
          refine ⟨1507110602959075796687803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009480803945434395583737 1507110602959075796687803)
          ·
            refine ⟨2260665904438613695031705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507110602959075796687803 2260665904438613695031705)
            ·
              refine ⟨1695499428328960271273779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260665904438613695031705 1695499428328960271273779)
              ·
                refine ⟨2543249142493440406910669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695499428328960271273779 2543249142493440406910669)
                ·
                  refine ⟨953718428435040152591501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2543249142493440406910669 953718428435040152591501)
                  ·
                    refine ⟨357644410663140057221813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 953718428435040152591501 357644410663140057221813)
                    ·
                      rfl

theorem cell22_1044765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1044765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044765 prefixEnd_1044765 := by exact prefixLift 1044765
  have htrace : WordTrace (prefixWord ++ tailWord_1044765) baseStart_1044765 baseEnd_1044765 := by
    simpa [prefixWord, tailWord_1044765, baseEnd_1044765] using wordTrace_append hprefix tailTrace_1044765
  have hstable : (prefixWord ++ tailWord_1044765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044765).length < 2 ^ (prefixWord ++ tailWord_1044765).sum := by decide
  have hdescent : baseEnd_1044765 < baseStart_1044765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044819 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 3, 6]
def baseStart_1044819 : Nat := 118140960795 + 1044819 * 2 ^ 59
def prefixEnd_1044819 : Nat := 4983230072969 + 3 ^ 40 * 1044819 * 2
def baseEnd_1044819 : Nat := 357662895966701916371647

theorem tailTrace_1044819 : CollatzResearch.WordTrace tailWord_1044819 prefixEnd_1044819 357662895966701916371647 := by
  unfold tailWord_1044819
  simp only [CollatzResearch.WordTrace]
  refine ⟨38107679601806678723905511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25405119734537785815937007 38107679601806678723905511)
  ·
    refine ⟨57161519402710018085858267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38107679601806678723905511 57161519402710018085858267)
    ·
      refine ⟨85742279104065027128787401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57161519402710018085858267 85742279104065027128787401)
      ·
        refine ⟨64306709328048770346590551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85742279104065027128787401 64306709328048770346590551)
        ·
          refine ⟨96460063992073155519885827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64306709328048770346590551 96460063992073155519885827)
          ·
            refine ⟨144690095988109733279828741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96460063992073155519885827 144690095988109733279828741)
            ·
              refine ⟨27129392997770574989967889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144690095988109733279828741 27129392997770574989967889)
              ·
                refine ⟨20347044748327931242475917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27129392997770574989967889 20347044748327931242475917)
                ·
                  refine ⟨7630141780622974215928469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20347044748327931242475917 7630141780622974215928469)
                  ·
                    refine ⟨357662895966701916371647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7630141780622974215928469 357662895966701916371647)
                    ·
                      rfl

theorem cell22_1044819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_1044819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044819 prefixEnd_1044819 := by exact prefixLift 1044819
  have htrace : WordTrace (prefixWord ++ tailWord_1044819) baseStart_1044819 baseEnd_1044819 := by
    simpa [prefixWord, tailWord_1044819, baseEnd_1044819] using wordTrace_append hprefix tailTrace_1044819
  have hstable : (prefixWord ++ tailWord_1044819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044819).length < 2 ^ (prefixWord ++ tailWord_1044819).sum := by decide
  have hdescent : baseEnd_1044819 < baseStart_1044819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044836 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_1044836 : Nat := 118140960795 + 1044836 * 2 ^ 59
def prefixEnd_1044836 : Nat := 4983230072969 + 3 ^ 40 * 1044836 * 2
def baseEnd_1044836 : Nat := 357668715414119538696595

theorem tailTrace_1044836 : CollatzResearch.WordTrace tailWord_1044836 prefixEnd_1044836 357668715414119538696595 := by
  unfold tailWord_1044836
  simp only [CollatzResearch.WordTrace]
  refine ⟨19054149821372545313637181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25405533095163393751516241 19054149821372545313637181)
  ·
    refine ⟨7145306183014704492613943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19054149821372545313637181 7145306183014704492613943)
    ·
      refine ⟨10717959274522056738920915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7145306183014704492613943 10717959274522056738920915)
      ·
        refine ⟨16076938911783085108381373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10717959274522056738920915 16076938911783085108381373)
        ·
          refine ⟨6028852091918656915643015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16076938911783085108381373 6028852091918656915643015)
          ·
            refine ⟨9043278137877985373464523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028852091918656915643015 9043278137877985373464523)
            ·
              refine ⟨13564917206816978060196785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9043278137877985373464523 13564917206816978060196785)
              ·
                refine ⟨10173687905112733545147589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13564917206816978060196785 10173687905112733545147589)
                ·
                  refine ⟨1907566482208637539715173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10173687905112733545147589 1907566482208637539715173)
                  ·
                    refine ⟨357668715414119538696595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1907566482208637539715173 357668715414119538696595)
                    ·
                      rfl

theorem cell22_1044836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_1044836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044836 prefixEnd_1044836 := by exact prefixLift 1044836
  have htrace : WordTrace (prefixWord ++ tailWord_1044836) baseStart_1044836 baseEnd_1044836 := by
    simpa [prefixWord, tailWord_1044836, baseEnd_1044836] using wordTrace_append hprefix tailTrace_1044836
  have hstable : (prefixWord ++ tailWord_1044836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044836).length < 2 ^ (prefixWord ++ tailWord_1044836).sum := by decide
  have hdescent : baseEnd_1044836 < baseStart_1044836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044853 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1044853 : Nat := 118140960795 + 1044853 * 2 ^ 59
def prefixEnd_1044853 : Nat := 4983230072969 + 3 ^ 40 * 1044853 * 2
def baseEnd_1044853 : Nat := 357674534861537161021543

theorem tailTrace_1044853 : CollatzResearch.WordTrace tailWord_1044853 prefixEnd_1044853 357674534861537161021543 := by
  unfold tailWord_1044853
  simp only [CollatzResearch.WordTrace]
  refine ⟨38108919683683502530643213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25405946455789001687095475 38108919683683502530643213)
  ·
    refine ⟨14290844881381313448991205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38108919683683502530643213 14290844881381313448991205)
    ·
      refine ⟨2679533415258996271685851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14290844881381313448991205 2679533415258996271685851)
      ·
        refine ⟨4019300122888494407528777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679533415258996271685851 4019300122888494407528777)
        ·
          refine ⟨3014475092166370805646583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4019300122888494407528777 3014475092166370805646583)
          ·
            refine ⟨4521712638249556208469875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014475092166370805646583 4521712638249556208469875)
            ·
              refine ⟨6782568957374334312704813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521712638249556208469875 6782568957374334312704813)
              ·
                refine ⟨2543463359015375367264305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6782568957374334312704813 2543463359015375367264305)
                ·
                  refine ⟨1907597519261531525448229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543463359015375367264305 1907597519261531525448229)
                  ·
                    refine ⟨357674534861537161021543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1907597519261531525448229 357674534861537161021543)
                    ·
                      rfl

theorem cell22_1044853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1044853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044853 prefixEnd_1044853 := by exact prefixLift 1044853
  have htrace : WordTrace (prefixWord ++ tailWord_1044853) baseStart_1044853 baseEnd_1044853 := by
    simpa [prefixWord, tailWord_1044853, baseEnd_1044853] using wordTrace_append hprefix tailTrace_1044853
  have hstable : (prefixWord ++ tailWord_1044853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044853).length < 2 ^ (prefixWord ++ tailWord_1044853).sum := by decide
  have hdescent : baseEnd_1044853 < baseStart_1044853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044874 : List Nat := [3, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_1044874 : Nat := 118140960795 + 1044874 * 2 ^ 59
def prefixEnd_1044874 : Nat := 4983230072969 + 3 ^ 40 * 1044874 * 2
def baseEnd_1044874 : Nat := 119227241196900035415493

theorem tailTrace_1044874 : CollatzResearch.WordTrace tailWord_1044874 prefixEnd_1044874 119227241196900035415493 := by
  unfold tailWord_1044874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9527421404151855779289419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25406457077738282078105117 9527421404151855779289419)
  ·
    refine ⟨14291132106227783668934129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9527421404151855779289419 14291132106227783668934129)
    ·
      refine ⟨10718349079670837751700597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14291132106227783668934129 10718349079670837751700597)
      ·
        refine ⟨1004845226219141039221931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10718349079670837751700597 1004845226219141039221931)
        ·
          refine ⟨1507267839328711558832897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004845226219141039221931 1507267839328711558832897)
          ·
            refine ⟨1130450879496533669124673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507267839328711558832897 1130450879496533669124673)
            ·
              refine ⟨847838159622400251843505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130450879496533669124673 847838159622400251843505)
              ·
                refine ⟨635878619716800188882629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847838159622400251843505 635878619716800188882629)
                ·
                  refine ⟨119227241196900035415493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635878619716800188882629 119227241196900035415493)
                  ·
                    rfl

theorem cell22_1044874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_1044874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044874 prefixEnd_1044874 := by exact prefixLift 1044874
  have htrace : WordTrace (prefixWord ++ tailWord_1044874) baseStart_1044874 baseEnd_1044874 := by
    simpa [prefixWord, tailWord_1044874, baseEnd_1044874] using wordTrace_append hprefix tailTrace_1044874
  have hstable : (prefixWord ++ tailWord_1044874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044874).length < 2 ^ (prefixWord ++ tailWord_1044874).sum := by decide
  have hdescent : baseEnd_1044874 < baseStart_1044874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044971 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 1, 6]
def baseStart_1044971 : Nat := 118140960795 + 1044971 * 2 ^ 59
def prefixEnd_1044971 : Nat := 4983230072969 + 3 ^ 40 * 1044971 * 2
def baseEnd_1044971 : Nat := 357714928673024186571181

theorem tailTrace_1044971 : CollatzResearch.WordTrace tailWord_1044971 prefixEnd_1044971 357714928673024186571181 := by
  unfold tailWord_1044971
  simp only [CollatzResearch.WordTrace]
  refine ⟨38113223497256008683438767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25408815664837339122292511 38113223497256008683438767)
  ·
    refine ⟨57169835245884013025158151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38113223497256008683438767 57169835245884013025158151)
    ·
      refine ⟨85754752868826019537737227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57169835245884013025158151 85754752868826019537737227)
      ·
        refine ⟨128632129303239029306605841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85754752868826019537737227 128632129303239029306605841)
        ·
          refine ⟨96474096977429271979954381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128632129303239029306605841 96474096977429271979954381)
          ·
            refine ⟨36177786366535976992482893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96474096977429271979954381 36177786366535976992482893)
            ·
              refine ⟨13566669887450991372181085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36177786366535976992482893 13566669887450991372181085)
              ·
                refine ⟨5087501207794121764567907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13566669887450991372181085 5087501207794121764567907)
                ·
                  refine ⟨7631251811691182646851861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5087501207794121764567907 7631251811691182646851861)
                  ·
                    refine ⟨357714928673024186571181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7631251811691182646851861 357714928673024186571181)
                    ·
                      rfl

theorem cell22_1044971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_1044971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1044971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1044971 prefixEnd_1044971 := by exact prefixLift 1044971
  have htrace : WordTrace (prefixWord ++ tailWord_1044971) baseStart_1044971 baseEnd_1044971 := by
    simpa [prefixWord, tailWord_1044971, baseEnd_1044971] using wordTrace_append hprefix tailTrace_1044971
  have hstable : (prefixWord ++ tailWord_1044971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044971).length < 2 ^ (prefixWord ++ tailWord_1044971).sum := by decide
  have hdescent : baseEnd_1044971 < baseStart_1044971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045001 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_1045001 : Nat := 118140960795 + 1045001 * 2 ^ 59
def prefixEnd_1045001 : Nat := 4983230072969 + 3 ^ 40 * 1045001 * 2
def baseEnd_1045001 : Nat := 357725198286114108321089

theorem tailTrace_1045001 : CollatzResearch.WordTrace tailWord_1045001 prefixEnd_1045001 357725198286114108321089 := by
  unfold tailWord_1045001
  simp only [CollatzResearch.WordTrace]
  refine ⟨38114317687147323807030857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25409545124764882538020571 38114317687147323807030857)
  ·
    refine ⟨28585738265360492855273143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38114317687147323807030857 28585738265360492855273143)
    ·
      refine ⟨42878607398040739282909715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28585738265360492855273143 42878607398040739282909715)
      ·
        refine ⟨64317911097061108924364573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42878607398040739282909715 64317911097061108924364573)
        ·
          refine ⟨24119216661397915846636715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64317911097061108924364573 24119216661397915846636715)
          ·
            refine ⟨36178824992096873769955073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24119216661397915846636715 36178824992096873769955073)
            ·
              refine ⟨27134118744072655327466305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36178824992096873769955073 27134118744072655327466305)
              ·
                refine ⟨20350589058054491495599729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27134118744072655327466305 20350589058054491495599729)
                ·
                  refine ⟨15262941793540868621699797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20350589058054491495599729 15262941793540868621699797)
                  ·
                    refine ⟨357725198286114108321089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15262941793540868621699797 357725198286114108321089)
                    ·
                      rfl

theorem cell22_1045001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_1045001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045001 prefixEnd_1045001 := by exact prefixLift 1045001
  have htrace : WordTrace (prefixWord ++ tailWord_1045001) baseStart_1045001 baseEnd_1045001 := by
    simpa [prefixWord, tailWord_1045001, baseEnd_1045001] using wordTrace_append hprefix tailTrace_1045001
  have hstable : (prefixWord ++ tailWord_1045001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045001).length < 2 ^ (prefixWord ++ tailWord_1045001).sum := by decide
  have hdescent : baseEnd_1045001 < baseStart_1045001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045003 : List Nat := [1, 1, 1, 1, 7, 2, 2, 7]
def baseStart_1045003 : Nat := 118140960795 + 1045003 * 2 ^ 59
def prefixEnd_1045003 : Nat := 4983230072969 + 3 ^ 40 * 1045003 * 2
def baseEnd_1045003 : Nat := 39747320325220752196787

theorem tailTrace_1045003 : CollatzResearch.WordTrace tailWord_1045003 prefixEnd_1045003 39747320325220752196787 := by
  unfold tailWord_1045003
  simp only [CollatzResearch.WordTrace]
  refine ⟨38114390633140078148603663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25409593755426718765735775 38114390633140078148603663)
  ·
    refine ⟨57171585949710117222905495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38114390633140078148603663 57171585949710117222905495)
    ·
      refine ⟨85757378924565175834358243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57171585949710117222905495 85757378924565175834358243)
      ·
        refine ⟨128636068386847763751537365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85757378924565175834358243 128636068386847763751537365)
        ·
          refine ⟨3014907852816744462926657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 128636068386847763751537365 3014907852816744462926657)
          ·
            refine ⟨2261180889612558347194993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3014907852816744462926657 2261180889612558347194993)
            ·
              refine ⟨1695885667209418760396245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2261180889612558347194993 1695885667209418760396245)
              ·
                refine ⟨39747320325220752196787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1695885667209418760396245 39747320325220752196787)
                ·
                  rfl

theorem cell22_1045003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 7].length) (baseStart_1045003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045003 prefixEnd_1045003 := by exact prefixLift 1045003
  have htrace : WordTrace (prefixWord ++ tailWord_1045003) baseStart_1045003 baseEnd_1045003 := by
    simpa [prefixWord, tailWord_1045003, baseEnd_1045003] using wordTrace_append hprefix tailTrace_1045003
  have hstable : (prefixWord ++ tailWord_1045003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045003).length < 2 ^ (prefixWord ++ tailWord_1045003).sum := by decide
  have hdescent : baseEnd_1045003 < baseStart_1045003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045037 : List Nat := [1, 5, 4, 1, 1, 10]
def baseStart_1045037 : Nat := 118140960795 + 1045037 * 2 ^ 59
def prefixEnd_1045037 : Nat := 4983230072969 + 3 ^ 40 * 1045037 * 2
def baseEnd_1045037 : Nat := 4416512615084222400259

theorem tailTrace_1045037 : CollatzResearch.WordTrace tailWord_1045037 prefixEnd_1045037 4416512615084222400259 := by
  unfold tailWord_1045037
  simp only [CollatzResearch.WordTrace]
  refine ⟨38115630715016901955341365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25410420476677934636894243 38115630715016901955341365)
  ·
    refine ⟨3573340379532834558313253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38115630715016901955341365 3573340379532834558313253)
    ·
      refine ⟨670001321162406479683735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3573340379532834558313253 670001321162406479683735)
      ·
        refine ⟨1005001981743609719525603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670001321162406479683735 1005001981743609719525603)
        ·
          refine ⟨1507502972615414579288405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005001981743609719525603 1507502972615414579288405)
          ·
            refine ⟨4416512615084222400259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1507502972615414579288405 4416512615084222400259)
            ·
              rfl

theorem cell22_1045037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 10].length) (baseStart_1045037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045037 prefixEnd_1045037 := by exact prefixLift 1045037
  have htrace : WordTrace (prefixWord ++ tailWord_1045037) baseStart_1045037 baseEnd_1045037 := by
    simpa [prefixWord, tailWord_1045037, baseEnd_1045037] using wordTrace_append hprefix tailTrace_1045037
  have hstable : (prefixWord ++ tailWord_1045037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045037).length < 2 ^ (prefixWord ++ tailWord_1045037).sum := by decide
  have hdescent : baseEnd_1045037 < baseStart_1045037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045054 : List Nat := [4, 2, 1, 4, 2, 1, 1, 7]
def baseStart_1045054 : Nat := 118140960795 + 1045054 * 2 ^ 59
def prefixEnd_1045054 : Nat := 4983230072969 + 3 ^ 40 * 1045054 * 2
def baseEnd_1045054 : Nat := 39749260141026626305103

theorem tailTrace_1045054 : CollatzResearch.WordTrace tailWord_1045054 prefixEnd_1045054 39749260141026626305103 := by
  unfold tailWord_1045054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764531344494414232338777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25410833837303542572473477 4764531344494414232338777)
  ·
    refine ⟨3573398508370810674254083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4764531344494414232338777 3573398508370810674254083)
    ·
      refine ⟨5360097762556216011381125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3573398508370810674254083 5360097762556216011381125)
      ·
        refine ⟨1005018330479290502133961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5360097762556216011381125 1005018330479290502133961)
        ·
          refine ⟨753763747859467876600471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005018330479290502133961 753763747859467876600471)
          ·
            refine ⟨1130645621789201814900707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753763747859467876600471 1130645621789201814900707)
            ·
              refine ⟨1695968432683802722351061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130645621789201814900707 1695968432683802722351061)
              ·
                refine ⟨39749260141026626305103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1695968432683802722351061 39749260141026626305103)
                ·
                  rfl

theorem cell22_1045054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_1045054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045054 prefixEnd_1045054 := by exact prefixLift 1045054
  have htrace : WordTrace (prefixWord ++ tailWord_1045054) baseStart_1045054 baseEnd_1045054 := by
    simpa [prefixWord, tailWord_1045054, baseEnd_1045054] using wordTrace_append hprefix tailTrace_1045054
  have hstable : (prefixWord ++ tailWord_1045054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045054).length < 2 ^ (prefixWord ++ tailWord_1045054).sum := by decide
  have hdescent : baseEnd_1045054 < baseStart_1045054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045063 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1045063 : Nat := 118140960795 + 1045063 * 2 ^ 59
def prefixEnd_1045063 : Nat := 4983230072969 + 3 ^ 40 * 1045063 * 2
def baseEnd_1045063 : Nat := 357746422153166613270899

theorem tailTrace_1045063 : CollatzResearch.WordTrace tailWord_1045063 prefixEnd_1045063 357746422153166613270899 := by
  unfold tailWord_1045063
  simp only [CollatzResearch.WordTrace]
  refine ⟨38116579012922708395787843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25411052675281805597191895 38116579012922708395787843)
  ·
    refine ⟨57174868519384062593681765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38116579012922708395787843 57174868519384062593681765)
    ·
      refine ⟨10720287847384511736315331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57174868519384062593681765 10720287847384511736315331)
      ·
        refine ⟨16080431771076767604472997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10720287847384511736315331 16080431771076767604472997)
        ·
          refine ⟨3015080957076893925838687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16080431771076767604472997 3015080957076893925838687)
          ·
            refine ⟨4522621435615340888758031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015080957076893925838687 4522621435615340888758031)
            ·
              refine ⟨6783932153423011333137047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522621435615340888758031 6783932153423011333137047)
              ·
                refine ⟨10175898230134516999705571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6783932153423011333137047 10175898230134516999705571)
                ·
                  refine ⟨15263847345201775499558357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10175898230134516999705571 15263847345201775499558357)
                  ·
                    refine ⟨357746422153166613270899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15263847345201775499558357 357746422153166613270899)
                    ·
                      rfl

theorem cell22_1045063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1045063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045063 prefixEnd_1045063 := by exact prefixLift 1045063
  have htrace : WordTrace (prefixWord ++ tailWord_1045063) baseStart_1045063 baseEnd_1045063 := by
    simpa [prefixWord, tailWord_1045063, baseEnd_1045063] using wordTrace_append hprefix tailTrace_1045063
  have hstable : (prefixWord ++ tailWord_1045063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045063).length < 2 ^ (prefixWord ++ tailWord_1045063).sum := by decide
  have hdescent : baseEnd_1045063 < baseStart_1045063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045123 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 1, 6]
def baseStart_1045123 : Nat := 118140960795 + 1045123 * 2 ^ 59
def prefixEnd_1045123 : Nat := 4983230072969 + 3 ^ 40 * 1045123 * 2
def baseEnd_1045123 : Nat := 357766961379346456770715

theorem tailTrace_1045123 : CollatzResearch.WordTrace tailWord_1045123 prefixEnd_1045123 357766961379346456770715 := by
  unfold tailWord_1045123
  simp only [CollatzResearch.WordTrace]
  refine ⟨38118767392705338642972023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25412511595136892428648015 38118767392705338642972023)
  ·
    refine ⟨57178151089058007964458035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38118767392705338642972023 57178151089058007964458035)
    ·
      refine ⟨85767226633587011946687053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57178151089058007964458035 85767226633587011946687053)
      ·
        refine ⟨32162709987595129480007645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85767226633587011946687053 32162709987595129480007645)
        ·
          refine ⟨12061016245348173555002867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32162709987595129480007645 12061016245348173555002867)
          ·
            refine ⟨18091524368022260332504301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12061016245348173555002867 18091524368022260332504301)
            ·
              refine ⟨6784321638008347624689113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18091524368022260332504301 6784321638008347624689113)
              ·
                refine ⟨5088241228506260718516835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6784321638008347624689113 5088241228506260718516835)
                ·
                  refine ⟨7632361842759391077775253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5088241228506260718516835 7632361842759391077775253)
                  ·
                    refine ⟨357766961379346456770715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7632361842759391077775253 357766961379346456770715)
                    ·
                      rfl

theorem cell22_1045123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_1045123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045123 prefixEnd_1045123 := by exact prefixLift 1045123
  have htrace : WordTrace (prefixWord ++ tailWord_1045123) baseStart_1045123 baseEnd_1045123 := by
    simpa [prefixWord, tailWord_1045123, baseEnd_1045123] using wordTrace_append hprefix tailTrace_1045123
  have hstable : (prefixWord ++ tailWord_1045123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045123).length < 2 ^ (prefixWord ++ tailWord_1045123).sum := by decide
  have hdescent : baseEnd_1045123 < baseStart_1045123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045125 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_1045125 : Nat := 118140960795 + 1045125 * 2 ^ 59
def prefixEnd_1045125 : Nat := 4983230072969 + 3 ^ 40 * 1045125 * 2
def baseEnd_1045125 : Nat := 357767646020219118220709

theorem tailTrace_1045125 : CollatzResearch.WordTrace tailWord_1045125 prefixEnd_1045125 357767646020219118220709 := by
  unfold tailWord_1045125
  simp only [CollatzResearch.WordTrace]
  refine ⟨38118840338698092984544829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25412560225798728656363219 38118840338698092984544829)
  ·
    refine ⟨14294565127011784869204311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38118840338698092984544829 14294565127011784869204311)
    ·
      refine ⟨21441847690517677303806467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14294565127011784869204311 21441847690517677303806467)
      ·
        refine ⟨32162771535776515955709701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21441847690517677303806467 32162771535776515955709701)
        ·
          refine ⟨6030519662958096741695569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32162771535776515955709701 6030519662958096741695569)
          ·
            refine ⟨4522889747218572556271677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6030519662958096741695569 4522889747218572556271677)
            ·
              refine ⟨1696083655206964708601879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4522889747218572556271677 1696083655206964708601879)
              ·
                refine ⟨2544125482810447062902819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696083655206964708601879 2544125482810447062902819)
                ·
                  refine ⟨3816188224215670594354229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544125482810447062902819 3816188224215670594354229)
                  ·
                    refine ⟨357767646020219118220709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3816188224215670594354229 357767646020219118220709)
                    ·
                      rfl

theorem cell22_1045125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_1045125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045125 prefixEnd_1045125 := by exact prefixLift 1045125
  have htrace : WordTrace (prefixWord ++ tailWord_1045125) baseStart_1045125 baseEnd_1045125 := by
    simpa [prefixWord, tailWord_1045125, baseEnd_1045125] using wordTrace_append hprefix tailTrace_1045125
  have hstable : (prefixWord ++ tailWord_1045125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045125).length < 2 ^ (prefixWord ++ tailWord_1045125).sum := by decide
  have hdescent : baseEnd_1045125 < baseStart_1045125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045168 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_1045168 : Nat := 118140960795 + 1045168 * 2 ^ 59
def prefixEnd_1045168 : Nat := 4983230072969 + 3 ^ 40 * 1045168 * 2
def baseEnd_1045168 : Nat := 357782365798981339395577

theorem tailTrace_1045168 : CollatzResearch.WordTrace tailWord_1045168 prefixEnd_1045168 357782365798981339395577 := by
  unfold tailWord_1045168
  simp only [CollatzResearch.WordTrace]
  refine ⟨19060204338771155664180079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25413605785028207552240105 19060204338771155664180079)
  ·
    refine ⟨28590306508156733496270119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19060204338771155664180079 28590306508156733496270119)
    ·
      refine ⟨42885459762235100244405179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28590306508156733496270119 42885459762235100244405179)
      ·
        refine ⟨64328189643352650366607769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42885459762235100244405179 64328189643352650366607769)
        ·
          refine ⟨48246142232514487774955827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64328189643352650366607769 48246142232514487774955827)
          ·
            refine ⟨72369213348771731662433741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48246142232514487774955827 72369213348771731662433741)
            ·
              refine ⟨27138455005789399373412653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72369213348771731662433741 27138455005789399373412653)
              ·
                refine ⟨10176920627171024765029745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27138455005789399373412653 10176920627171024765029745)
                ·
                  refine ⟨7632690470378268573772309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10176920627171024765029745 7632690470378268573772309)
                  ·
                    refine ⟨357782365798981339395577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7632690470378268573772309 357782365798981339395577)
                    ·
                      rfl

theorem cell22_1045168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_1045168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045168 prefixEnd_1045168 := by exact prefixLift 1045168
  have htrace : WordTrace (prefixWord ++ tailWord_1045168) baseStart_1045168 baseEnd_1045168 := by
    simpa [prefixWord, tailWord_1045168, baseEnd_1045168] using wordTrace_append hprefix tailTrace_1045168
  have hstable : (prefixWord ++ tailWord_1045168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045168).length < 2 ^ (prefixWord ++ tailWord_1045168).sum := by decide
  have hdescent : baseEnd_1045168 < baseStart_1045168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045217 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 5]
def baseStart_1045217 : Nat := 118140960795 + 1045217 * 2 ^ 59
def prefixEnd_1045217 : Nat := 4983230072969 + 3 ^ 40 * 1045217 * 2
def baseEnd_1045217 : Nat := 119266379833453848306809

theorem tailTrace_1045217 : CollatzResearch.WordTrace tailWord_1045217 prefixEnd_1045217 119266379833453848306809 := by
  unfold tailWord_1045217
  simp only [CollatzResearch.WordTrace]
  refine ⟨38122195854364792696893905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25414797236243195131262603 38122195854364792696893905)
  ·
    refine ⟨28591646890773594522670429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38122195854364792696893905 28591646890773594522670429)
    ·
      refine ⟨10721867584040097946001411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28591646890773594522670429 10721867584040097946001411)
      ·
        refine ⟨16082801376060146919002117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10721867584040097946001411 16082801376060146919002117)
        ·
          refine ⟨3015525258011277547312897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16082801376060146919002117 3015525258011277547312897)
          ·
            refine ⟨2261643943508458160484673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3015525258011277547312897 2261643943508458160484673)
            ·
              refine ⟨1696232957631343620363505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2261643943508458160484673 1696232957631343620363505)
              ·
                refine ⟨1272174718223507715272629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696232957631343620363505 1272174718223507715272629)
                ·
                  refine ⟨119266379833453848306809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1272174718223507715272629 119266379833453848306809)
                  ·
                    rfl

theorem cell22_1045217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_1045217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045217 prefixEnd_1045217 := by exact prefixLift 1045217
  have htrace : WordTrace (prefixWord ++ tailWord_1045217) baseStart_1045217 baseEnd_1045217 := by
    simpa [prefixWord, tailWord_1045217, baseEnd_1045217] using wordTrace_append hprefix tailTrace_1045217
  have hstable : (prefixWord ++ tailWord_1045217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045217).length < 2 ^ (prefixWord ++ tailWord_1045217).sum := by decide
  have hdescent : baseEnd_1045217 < baseStart_1045217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045221 : List Nat := [1, 3, 1, 4, 1, 2, 4, 2, 1, 3]
def baseStart_1045221 : Nat := 118140960795 + 1045221 * 2 ^ 59
def prefixEnd_1045221 : Nat := 4983230072969 + 3 ^ 40 * 1045221 * 2
def baseEnd_1045221 : Nat := 357800508782106867820415

theorem tailTrace_1045221 : CollatzResearch.WordTrace tailWord_1045221 prefixEnd_1045221 357800508782106867820415 := by
  unfold tailWord_1045221
  simp only [CollatzResearch.WordTrace]
  refine ⟨38122341746350301380039517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25414894497566867586693011 38122341746350301380039517)
  ·
    refine ⟨14295878154881363017514819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38122341746350301380039517 14295878154881363017514819)
    ·
      refine ⟨21443817232322044526272229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14295878154881363017514819 21443817232322044526272229)
      ·
        refine ⟨4020715731060383348676043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21443817232322044526272229 4020715731060383348676043)
        ·
          refine ⟨6031073596590575023014065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020715731060383348676043 6031073596590575023014065)
          ·
            refine ⟨4523305197442931267260549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6031073596590575023014065 4523305197442931267260549)
            ·
              refine ⟨848119724520549612611353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4523305197442931267260549 848119724520549612611353)
              ·
                refine ⟨636089793390412209458515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848119724520549612611353 636089793390412209458515)
                ·
                  refine ⟨954134690085618314187773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636089793390412209458515 954134690085618314187773)
                  ·
                    refine ⟨357800508782106867820415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 954134690085618314187773 357800508782106867820415)
                    ·
                      rfl

theorem cell22_1045221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_1045221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045221 prefixEnd_1045221 := by exact prefixLift 1045221
  have htrace : WordTrace (prefixWord ++ tailWord_1045221) baseStart_1045221 baseEnd_1045221 := by
    simpa [prefixWord, tailWord_1045221, baseEnd_1045221] using wordTrace_append hprefix tailTrace_1045221
  have hstable : (prefixWord ++ tailWord_1045221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045221).length < 2 ^ (prefixWord ++ tailWord_1045221).sum := by decide
  have hdescent : baseEnd_1045221 < baseStart_1045221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045245 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 6]
def baseStart_1045245 : Nat := 118140960795 + 1045245 * 2 ^ 59
def prefixEnd_1045245 : Nat := 4983230072969 + 3 ^ 40 * 1045245 * 2
def baseEnd_1045245 : Nat := 119269574824192935073447

theorem tailTrace_1045245 : CollatzResearch.WordTrace tailWord_1045245 prefixEnd_1045245 119269574824192935073447 := by
  unfold tailWord_1045245
  simp only [CollatzResearch.WordTrace]
  refine ⟨38123217098263353478913189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25415478065508902319275459 38123217098263353478913189)
  ·
    refine ⟨7148103205924378777296223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38123217098263353478913189 7148103205924378777296223)
    ·
      refine ⟨10722154808886568165944335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7148103205924378777296223 10722154808886568165944335)
      ·
        refine ⟨16083232213329852248916503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10722154808886568165944335 16083232213329852248916503)
        ·
          refine ⟨24124848319994778373374755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16083232213329852248916503 24124848319994778373374755)
          ·
            refine ⟨36187272479992167560062133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24124848319994778373374755 36187272479992167560062133)
            ·
              refine ⟨3392556794999265708755825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36187272479992167560062133 3392556794999265708755825)
              ·
                refine ⟨2544417596249449281566869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3392556794999265708755825 2544417596249449281566869)
                ·
                  refine ⟨119269574824192935073447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2544417596249449281566869 119269574824192935073447)
                  ·
                    rfl

theorem cell22_1045245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_1045245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045245 prefixEnd_1045245 := by exact prefixLift 1045245
  have htrace : WordTrace (prefixWord ++ tailWord_1045245) baseStart_1045245 baseEnd_1045245 := by
    simpa [prefixWord, tailWord_1045245, baseEnd_1045245] using wordTrace_append hprefix tailTrace_1045245
  have hstable : (prefixWord ++ tailWord_1045245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045245).length < 2 ^ (prefixWord ++ tailWord_1045245).sum := by decide
  have hdescent : baseEnd_1045245 < baseStart_1045245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045294 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1045294 : Nat := 118140960795 + 1045294 * 2 ^ 59
def prefixEnd_1045294 : Nat := 4983230072969 + 3 ^ 40 * 1045294 * 2
def baseEnd_1045294 : Nat := 357825498173959010745191

theorem tailTrace_1045294 : CollatzResearch.WordTrace tailWord_1045294 prefixEnd_1045294 357825498173959010745191 := by
  unfold tailWord_1045294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4765625534385729355930867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25416669516723889898297957 4765625534385729355930867)
  ·
    refine ⟨7148438301578594033896301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4765625534385729355930867 7148438301578594033896301)
    ·
      refine ⟨2680664363091972762711113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7148438301578594033896301 2680664363091972762711113)
      ·
        refine ⟨2010498272318979572033335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2680664363091972762711113 2010498272318979572033335)
        ·
          refine ⟨3015747408478469358050003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010498272318979572033335 3015747408478469358050003)
          ·
            refine ⟨4523621112717704037075005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015747408478469358050003 4523621112717704037075005)
            ·
              refine ⟨1696357917269139013903127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4523621112717704037075005 1696357917269139013903127)
              ·
                refine ⟨2544536875903708520854691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696357917269139013903127 2544536875903708520854691)
                ·
                  refine ⟨3816805313855562781282037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544536875903708520854691 3816805313855562781282037)
                  ·
                    refine ⟨357825498173959010745191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3816805313855562781282037 357825498173959010745191)
                    ·
                      rfl

theorem cell22_1045294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1045294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045294 prefixEnd_1045294 := by exact prefixLift 1045294
  have htrace : WordTrace (prefixWord ++ tailWord_1045294) baseStart_1045294 baseEnd_1045294 := by
    simpa [prefixWord, tailWord_1045294, baseEnd_1045294] using wordTrace_append hprefix tailTrace_1045294
  have hstable : (prefixWord ++ tailWord_1045294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045294).length < 2 ^ (prefixWord ++ tailWord_1045294).sum := by decide
  have hdescent : baseEnd_1045294 < baseStart_1045294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045313 : List Nat := [1, 2, 5, 3, 1, 2, 1, 3, 4]
def baseStart_1045313 : Nat := 118140960795 + 1045313 * 2 ^ 59
def prefixEnd_1045313 : Nat := 4983230072969 + 3 ^ 40 * 1045313 * 2
def baseEnd_1045313 : Nat := 119277334087416431506711

theorem tailTrace_1045313 : CollatzResearch.WordTrace tailWord_1045313 prefixEnd_1045313 119277334087416431506711 := by
  unfold tailWord_1045313
  simp only [CollatzResearch.WordTrace]
  refine ⟨38125697262017001092388593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25417131508011334061592395 38125697262017001092388593)
  ·
    refine ⟨28594272946512750819291445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38125697262017001092388593 28594272946512750819291445)
    ·
      refine ⟨2680713088735570389308573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28594272946512750819291445 2680713088735570389308573)
      ·
        refine ⟨1005267408275838895990715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2680713088735570389308573 1005267408275838895990715)
        ·
          refine ⟨1507901112413758343986073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005267408275838895990715 1507901112413758343986073)
          ·
            refine ⟨1130925834310318757989555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507901112413758343986073 1130925834310318757989555)
            ·
              refine ⟨1696388751465478136984333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130925834310318757989555 1696388751465478136984333)
              ·
                refine ⟨636145781799554301369125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1696388751465478136984333 636145781799554301369125)
                ·
                  refine ⟨119277334087416431506711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636145781799554301369125 119277334087416431506711)
                  ·
                    rfl

theorem cell22_1045313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 4].length) (baseStart_1045313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045313 prefixEnd_1045313 := by exact prefixLift 1045313
  have htrace : WordTrace (prefixWord ++ tailWord_1045313) baseStart_1045313 baseEnd_1045313 := by
    simpa [prefixWord, tailWord_1045313, baseEnd_1045313] using wordTrace_append hprefix tailTrace_1045313
  have hstable : (prefixWord ++ tailWord_1045313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045313).length < 2 ^ (prefixWord ++ tailWord_1045313).sum := by decide
  have hdescent : baseEnd_1045313 < baseStart_1045313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045427 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 2, 4]
def baseStart_1045427 : Nat := 118140960795 + 1045427 * 2 ^ 59
def prefixEnd_1045427 : Nat := 4983230072969 + 3 ^ 40 * 1045427 * 2
def baseEnd_1045427 : Nat := 357871026791990997169783

theorem tailTrace_1045427 : CollatzResearch.WordTrace tailWord_1045427 prefixEnd_1045427 357871026791990997169783 := by
  unfold tailWord_1045427
  simp only [CollatzResearch.WordTrace]
  refine ⟨38129855183603998562038535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25419903455735999041359023 38129855183603998562038535)
  ·
    refine ⟨57194782775405997843057803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38129855183603998562038535 57194782775405997843057803)
    ·
      refine ⟨85792174163108996764586705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57194782775405997843057803 85792174163108996764586705)
      ·
        refine ⟨64344130622331747573440029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85792174163108996764586705 64344130622331747573440029)
        ·
          refine ⟨24129048983374405340040011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64344130622331747573440029 24129048983374405340040011)
          ·
            refine ⟨36193573475061608010060017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24129048983374405340040011 36193573475061608010060017)
            ·
              refine ⟨27145180106296206007545013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36193573475061608010060017 27145180106296206007545013)
              ·
                refine ⟨2544860634965269313207345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27145180106296206007545013 2544860634965269313207345)
                ·
                  refine ⟨1908645476223951984905509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2544860634965269313207345 1908645476223951984905509)
                  ·
                    refine ⟨357871026791990997169783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1908645476223951984905509 357871026791990997169783)
                    ·
                      rfl

theorem cell22_1045427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 4].length) (baseStart_1045427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045427 prefixEnd_1045427 := by exact prefixLift 1045427
  have htrace : WordTrace (prefixWord ++ tailWord_1045427) baseStart_1045427 baseEnd_1045427 := by
    simpa [prefixWord, tailWord_1045427, baseEnd_1045427] using wordTrace_append hprefix tailTrace_1045427
  have hstable : (prefixWord ++ tailWord_1045427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045427).length < 2 ^ (prefixWord ++ tailWord_1045427).sum := by decide
  have hdescent : baseEnd_1045427 < baseStart_1045427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045429 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1045429 : Nat := 118140960795 + 1045429 * 2 ^ 59
def prefixEnd_1045429 : Nat := 4983230072969 + 3 ^ 40 * 1045429 * 2
def baseEnd_1045429 : Nat := 357871711432863658619777

theorem tailTrace_1045429 : CollatzResearch.WordTrace tailWord_1045429 prefixEnd_1045429 357871711432863658619777 := by
  unfold tailWord_1045429
  simp only [CollatzResearch.WordTrace]
  refine ⟨38129928129596752903611341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25419952086397835269074227 38129928129596752903611341)
  ·
    refine ⟨14298723048598782338854253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38129928129596752903611341 14298723048598782338854253)
    ·
      refine ⟨5362021143224543377070345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14298723048598782338854253 5362021143224543377070345)
      ·
        refine ⟨4021515857418407532802759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5362021143224543377070345 4021515857418407532802759)
        ·
          refine ⟨6032273786127611299204139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021515857418407532802759 6032273786127611299204139)
          ·
            refine ⟨9048410679191416948806209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032273786127611299204139 9048410679191416948806209)
            ·
              refine ⟨6786308009393562711604657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9048410679191416948806209 6786308009393562711604657)
              ·
                refine ⟨5089731007045172033703493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6786308009393562711604657 5089731007045172033703493)
                ·
                  refine ⟨954324563820969756319405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5089731007045172033703493 954324563820969756319405)
                  ·
                    refine ⟨357871711432863658619777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 954324563820969756319405 357871711432863658619777)
                    ·
                      rfl

theorem cell22_1045429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1045429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045429 prefixEnd_1045429 := by exact prefixLift 1045429
  have htrace : WordTrace (prefixWord ++ tailWord_1045429) baseStart_1045429 baseEnd_1045429 := by
    simpa [prefixWord, tailWord_1045429, baseEnd_1045429] using wordTrace_append hprefix tailTrace_1045429
  have hstable : (prefixWord ++ tailWord_1045429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045429).length < 2 ^ (prefixWord ++ tailWord_1045429).sum := by decide
  have hdescent : baseEnd_1045429 < baseStart_1045429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045487 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 7]
def baseStart_1045487 : Nat := 118140960795 + 1045487 * 2 ^ 59
def prefixEnd_1045487 : Nat := 4983230072969 + 3 ^ 40 * 1045487 * 2
def baseEnd_1045487 : Nat := 119297188672723613556533

theorem tailTrace_1045487 : CollatzResearch.WordTrace tailWord_1045487 prefixEnd_1045487 119297188672723613556533 := by
  unfold tailWord_1045487
  simp only [CollatzResearch.WordTrace]
  refine ⟨38132043563386628809222715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25421362375591085872815143 38132043563386628809222715)
  ·
    refine ⟨57198065345079943213834073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38132043563386628809222715 57198065345079943213834073)
    ·
      refine ⟨42898549008809957410375555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57198065345079943213834073 42898549008809957410375555)
      ·
        refine ⟨64347823513214936115563333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42898549008809957410375555 64347823513214936115563333)
        ·
          refine ⟨12065216908727800521668125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64347823513214936115563333 12065216908727800521668125)
          ·
            refine ⟨4524456340772925195625547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12065216908727800521668125 4524456340772925195625547)
            ·
              refine ⟨6786684511159387793438321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524456340772925195625547 6786684511159387793438321)
              ·
                refine ⟨5090013383369540845078741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6786684511159387793438321 5090013383369540845078741)
                ·
                  refine ⟨119297188672723613556533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5090013383369540845078741 119297188672723613556533)
                  ·
                    rfl

theorem cell22_1045487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 7].length) (baseStart_1045487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045487 prefixEnd_1045487 := by exact prefixLift 1045487
  have htrace : WordTrace (prefixWord ++ tailWord_1045487) baseStart_1045487 baseEnd_1045487 := by
    simpa [prefixWord, tailWord_1045487, baseEnd_1045487] using wordTrace_append hprefix tailTrace_1045487
  have hstable : (prefixWord ++ tailWord_1045487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045487).length < 2 ^ (prefixWord ++ tailWord_1045487).sum := by decide
  have hdescent : baseEnd_1045487 < baseStart_1045487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045493 : List Nat := [1, 3, 5, 2, 2, 1, 8]
def baseStart_1045493 : Nat := 118140960795 + 1045493 * 2 ^ 59
def prefixEnd_1045493 : Nat := 4983230072969 + 3 ^ 40 * 1045493 * 2
def baseEnd_1045493 : Nat := 13255319257066252778503

theorem tailTrace_1045493 : CollatzResearch.WordTrace tailWord_1045493 prefixEnd_1045493 13255319257066252778503 := by
  unfold tailWord_1045493
  simp only [CollatzResearch.WordTrace]
  refine ⟨38132262401364891833941133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25421508267576594555960755 38132262401364891833941133)
  ·
    refine ⟨14299598400511834437727925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38132262401364891833941133 14299598400511834437727925)
    ·
      refine ⟨1340587350047984478536993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14299598400511834437727925 1340587350047984478536993)
      ·
        refine ⟨1005440512535988358902745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1340587350047984478536993 1005440512535988358902745)
        ·
          refine ⟨754080384401991269177059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005440512535988358902745 754080384401991269177059)
          ·
            refine ⟨1131120576602986903765589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754080384401991269177059 1131120576602986903765589)
            ·
              refine ⟨13255319257066252778503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1131120576602986903765589 13255319257066252778503)
              ·
                rfl

theorem cell22_1045493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 8].length) (baseStart_1045493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045493 prefixEnd_1045493 := by exact prefixLift 1045493
  have htrace : WordTrace (prefixWord ++ tailWord_1045493) baseStart_1045493 baseEnd_1045493 := by
    simpa [prefixWord, tailWord_1045493, baseEnd_1045493] using wordTrace_append hprefix tailTrace_1045493
  have hstable : (prefixWord ++ tailWord_1045493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045493).length < 2 ^ (prefixWord ++ tailWord_1045493).sum := by decide
  have hdescent : baseEnd_1045493 < baseStart_1045493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045577 : List Nat := [1, 2, 1, 1, 2, 2, 2, 11]
def baseStart_1045577 : Nat := 118140960795 + 1045577 * 2 ^ 59
def prefixEnd_1045577 : Nat := 4983230072969 + 3 ^ 40 * 1045577 * 2
def baseEnd_1045577 : Nat := 39769152761937845102147

theorem tailTrace_1045577 : CollatzResearch.WordTrace tailWord_1045577 prefixEnd_1045577 39769152761937845102147 := by
  unfold tailWord_1045577
  simp only [CollatzResearch.WordTrace]
  refine ⟨38135326133060574179998985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25423550755373716119999323 38135326133060574179998985)
  ·
    refine ⟨28601494599795430634999239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38135326133060574179998985 28601494599795430634999239)
    ·
      refine ⟨42902241899693145952498859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28601494599795430634999239 42902241899693145952498859)
      ·
        refine ⟨64353362849539718928748289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42902241899693145952498859 64353362849539718928748289)
        ·
          refine ⟨48265022137154789196561217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64353362849539718928748289 48265022137154789196561217)
          ·
            refine ⟨36198766602866091897420913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48265022137154789196561217 36198766602866091897420913)
            ·
              refine ⟨27149074952149568923065685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36198766602866091897420913 27149074952149568923065685)
              ·
                refine ⟨39769152761937845102147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 27149074952149568923065685 39769152761937845102147)
                ·
                  rfl

theorem cell22_1045577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 11].length) (baseStart_1045577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045577 prefixEnd_1045577 := by exact prefixLift 1045577
  have htrace : WordTrace (prefixWord ++ tailWord_1045577) baseStart_1045577 baseEnd_1045577 := by
    simpa [prefixWord, tailWord_1045577, baseEnd_1045577] using wordTrace_append hprefix tailTrace_1045577
  have hstable : (prefixWord ++ tailWord_1045577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045577).length < 2 ^ (prefixWord ++ tailWord_1045577).sum := by decide
  have hdescent : baseEnd_1045577 < baseStart_1045577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045581 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1045581 : Nat := 118140960795 + 1045581 * 2 ^ 59
def prefixEnd_1045581 : Nat := 4983230072969 + 3 ^ 40 * 1045581 * 2
def baseEnd_1045581 : Nat := 357923744139185928819311

theorem tailTrace_1045581 : CollatzResearch.WordTrace tailWord_1045581 prefixEnd_1045581 357923744139185928819311 := by
  unfold tailWord_1045581
  simp only [CollatzResearch.WordTrace]
  refine ⟨38135472025046082863144597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25423648016697388575429731 38135472025046082863144597)
  ·
    refine ⟨1787600251174035134209903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38135472025046082863144597 1787600251174035134209903)
    ·
      refine ⟨2681400376761052701314855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1787600251174035134209903 2681400376761052701314855)
      ·
        refine ⟨4022100565141579051972283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681400376761052701314855 4022100565141579051972283)
        ·
          refine ⟨6033150847712368577958425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022100565141579051972283 6033150847712368577958425)
          ·
            refine ⟨4524863135784276433468819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033150847712368577958425 4524863135784276433468819)
            ·
              refine ⟨6787294703676414650203229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524863135784276433468819 6787294703676414650203229)
              ·
                refine ⟨2545235513878655493826211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6787294703676414650203229 2545235513878655493826211)
                ·
                  refine ⟨3817853270817983240739317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545235513878655493826211 3817853270817983240739317)
                  ·
                    refine ⟨357923744139185928819311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3817853270817983240739317 357923744139185928819311)
                    ·
                      rfl

theorem cell22_1045581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1045581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045581 prefixEnd_1045581 := by exact prefixLift 1045581
  have htrace : WordTrace (prefixWord ++ tailWord_1045581) baseStart_1045581 baseEnd_1045581 := by
    simpa [prefixWord, tailWord_1045581, baseEnd_1045581] using wordTrace_append hprefix tailTrace_1045581
  have hstable : (prefixWord ++ tailWord_1045581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045581).length < 2 ^ (prefixWord ++ tailWord_1045581).sum := by decide
  have hdescent : baseEnd_1045581 < baseStart_1045581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045660 : List Nat := [2, 2, 3, 2, 1, 2, 3, 3, 1, 3]
def baseStart_1045660 : Nat := 118140960795 + 1045660 * 2 ^ 59
def prefixEnd_1045660 : Nat := 4983230072969 + 3 ^ 40 * 1045660 * 2
def baseEnd_1045660 : Nat := 357950787453656056094069

theorem tailTrace_1045660 : CollatzResearch.WordTrace tailWord_1045660 prefixEnd_1045660 357950787453656056094069 := by
  unfold tailWord_1045660
  simp only [CollatzResearch.WordTrace]
  refine ⟨19069176695879939677635217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25425568927839919570180289 19069176695879939677635217)
  ·
    refine ⟨14301882521909954758226413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19069176695879939677635217 14301882521909954758226413)
    ·
      refine ⟨5363205945716233034334905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14301882521909954758226413 5363205945716233034334905)
      ·
        refine ⟨4022404459287174775751179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5363205945716233034334905 4022404459287174775751179)
        ·
          refine ⟨6033606688930762163626769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022404459287174775751179 6033606688930762163626769)
          ·
            refine ⟨4525205016698071622720077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033606688930762163626769 4525205016698071622720077)
            ·
              refine ⟨1696951881261776858520029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4525205016698071622720077 1696951881261776858520029)
              ·
                refine ⟨636356955473166321945011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1696951881261776858520029 636356955473166321945011)
                ·
                  refine ⟨954535433209749482917517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636356955473166321945011 954535433209749482917517)
                  ·
                    refine ⟨357950787453656056094069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 954535433209749482917517 357950787453656056094069)
                    ·
                      rfl

theorem cell22_1045660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_1045660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045660 prefixEnd_1045660 := by exact prefixLift 1045660
  have htrace : WordTrace (prefixWord ++ tailWord_1045660) baseStart_1045660 baseEnd_1045660 := by
    simpa [prefixWord, tailWord_1045660, baseEnd_1045660] using wordTrace_append hprefix tailTrace_1045660
  have hstable : (prefixWord ++ tailWord_1045660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045660).length < 2 ^ (prefixWord ++ tailWord_1045660).sum := by decide
  have hdescent : baseEnd_1045660 < baseStart_1045660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045677 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1045677 : Nat := 118140960795 + 1045677 * 2 ^ 59
def prefixEnd_1045677 : Nat := 4983230072969 + 3 ^ 40 * 1045677 * 2
def baseEnd_1045677 : Nat := 357956606901073678419017

theorem tailTrace_1045677 : CollatzResearch.WordTrace tailWord_1045677 prefixEnd_1045677 357956606901073678419017 := by
  unfold tailWord_1045677
  simp only [CollatzResearch.WordTrace]
  refine ⟨38138973432698291258639285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25425982288465527505759523 38138973432698291258639285)
  ·
    refine ⟨3575528759315464805497433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38138973432698291258639285 3575528759315464805497433)
    ·
      refine ⟨2681646569486598604123075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3575528759315464805497433 2681646569486598604123075)
      ·
        refine ⟨4022469854229897906184613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681646569486598604123075 4022469854229897906184613)
        ·
          refine ⟨754213097668105857409615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4022469854229897906184613 754213097668105857409615)
          ·
            refine ⟨1131319646502158786114423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754213097668105857409615 1131319646502158786114423)
            ·
              refine ⟨1696979469753238179171635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131319646502158786114423 1696979469753238179171635)
              ·
                refine ⟨2545469204629857268757453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696979469753238179171635 2545469204629857268757453)
                ·
                  refine ⟨954550951736196475784045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2545469204629857268757453 954550951736196475784045)
                  ·
                    refine ⟨357956606901073678419017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 954550951736196475784045 357956606901073678419017)
                    ·
                      rfl

theorem cell22_1045677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1045677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045677 prefixEnd_1045677 := by exact prefixLift 1045677
  have htrace : WordTrace (prefixWord ++ tailWord_1045677) baseStart_1045677 baseEnd_1045677 := by
    simpa [prefixWord, tailWord_1045677, baseEnd_1045677] using wordTrace_append hprefix tailTrace_1045677
  have hstable : (prefixWord ++ tailWord_1045677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045677).length < 2 ^ (prefixWord ++ tailWord_1045677).sum := by decide
  have hdescent : baseEnd_1045677 < baseStart_1045677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045720 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 1, 4]
def baseStart_1045720 : Nat := 118140960795 + 1045720 * 2 ^ 59
def prefixEnd_1045720 : Nat := 4983230072969 + 3 ^ 40 * 1045720 * 2
def baseEnd_1045720 : Nat := 357971326679835899593885

theorem tailTrace_1045720 : CollatzResearch.WordTrace tailWord_1045720 prefixEnd_1045720 357971326679835899593885 := by
  unfold tailWord_1045720
  simp only [CollatzResearch.WordTrace]
  refine ⟨19070270885771254801227307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25427027847695006401636409 19070270885771254801227307)
  ·
    refine ⟨28605406328656882201840961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19070270885771254801227307 28605406328656882201840961)
    ·
      refine ⟨21454054746492661651380721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28605406328656882201840961 21454054746492661651380721)
      ·
        refine ⟨16090541059869496238535541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21454054746492661651380721 16090541059869496238535541)
        ·
          refine ⟨1508488224362765272362707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16090541059869496238535541 1508488224362765272362707)
          ·
            refine ⟨2262732336544147908544061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508488224362765272362707 2262732336544147908544061)
            ·
              refine ⟨848524626204055465704023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2262732336544147908544061 848524626204055465704023)
              ·
                refine ⟨1272786939306083198556035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848524626204055465704023 1272786939306083198556035)
                ·
                  refine ⟨1909180408959124797834053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272786939306083198556035 1909180408959124797834053)
                  ·
                    refine ⟨357971326679835899593885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1909180408959124797834053 357971326679835899593885)
                    ·
                      rfl

theorem cell22_1045720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_1045720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045720 prefixEnd_1045720 := by exact prefixLift 1045720
  have htrace : WordTrace (prefixWord ++ tailWord_1045720) baseStart_1045720 baseEnd_1045720 := by
    simpa [prefixWord, tailWord_1045720, baseEnd_1045720] using wordTrace_append hprefix tailTrace_1045720
  have hstable : (prefixWord ++ tailWord_1045720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045720).length < 2 ^ (prefixWord ++ tailWord_1045720).sum := by decide
  have hdescent : baseEnd_1045720 < baseStart_1045720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045729 : List Nat := [1, 2, 3, 1, 3, 12]
def baseStart_1045729 : Nat := 118140960795 + 1045729 * 2 ^ 59
def prefixEnd_1045729 : Nat := 4983230072969 + 3 ^ 40 * 1045729 * 2
def baseEnd_1045729 : Nat := 4419437130416825631097

theorem tailTrace_1045729 : CollatzResearch.WordTrace tailWord_1045729 prefixEnd_1045729 4419437130416825631097 := by
  unfold tailWord_1045729
  simp only [CollatzResearch.WordTrace]
  refine ⟨38140870028509904139532241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25427246685673269426354827 38140870028509904139532241)
  ·
    refine ⟨28605652521382428104649181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38140870028509904139532241 28605652521382428104649181)
    ·
      refine ⟨10727119695518410539243443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28605652521382428104649181 10727119695518410539243443)
      ·
        refine ⟨16090679543277615808865165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10727119695518410539243443 16090679543277615808865165)
        ·
          refine ⟨6034004828729105928324437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16090679543277615808865165 6034004828729105928324437)
          ·
            refine ⟨4419437130416825631097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6034004828729105928324437 4419437130416825631097)
            ·
              rfl

theorem cell22_1045729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 12].length) (baseStart_1045729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045729 prefixEnd_1045729 := by exact prefixLift 1045729
  have htrace : WordTrace (prefixWord ++ tailWord_1045729) baseStart_1045729 baseEnd_1045729 := by
    simpa [prefixWord, tailWord_1045729, baseEnd_1045729] using wordTrace_append hprefix tailTrace_1045729
  have hstable : (prefixWord ++ tailWord_1045729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045729).length < 2 ^ (prefixWord ++ tailWord_1045729).sum := by decide
  have hdescent : baseEnd_1045729 < baseStart_1045729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045735 : List Nat := [1, 1, 5, 3, 2, 1, 1, 4, 4]
def baseStart_1045735 : Nat := 118140960795 + 1045735 * 2 ^ 59
def prefixEnd_1045735 : Nat := 4983230072969 + 3 ^ 40 * 1045735 * 2
def baseEnd_1045735 : Nat := 119325487162126953489613

theorem tailTrace_1045735 : CollatzResearch.WordTrace tailWord_1045735 prefixEnd_1045735 119325487162126953489613 := by
  unfold tailWord_1045735
  simp only [CollatzResearch.WordTrace]
  refine ⟨38141088866488167164250659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25427392577658778109500439 38141088866488167164250659)
  ·
    refine ⟨57211633299732250746375989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38141088866488167164250659 57211633299732250746375989)
    ·
      refine ⟨5363590621849898507472749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57211633299732250746375989 5363590621849898507472749)
      ·
        refine ⟨2011346483193711940302281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5363590621849898507472749 2011346483193711940302281)
        ·
          refine ⟨1508509862395283955226711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2011346483193711940302281 1508509862395283955226711)
          ·
            refine ⟨2262764793592925932840067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508509862395283955226711 2262764793592925932840067)
            ·
              refine ⟨3394147190389388899260101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262764793592925932840067 3394147190389388899260101)
              ·
                refine ⟨636402598198010418611269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3394147190389388899260101 636402598198010418611269)
                ·
                  refine ⟨119325487162126953489613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636402598198010418611269 119325487162126953489613)
                  ·
                    rfl

theorem cell22_1045735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 4].length) (baseStart_1045735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045735 prefixEnd_1045735 := by exact prefixLift 1045735
  have htrace : WordTrace (prefixWord ++ tailWord_1045735) baseStart_1045735 baseEnd_1045735 := by
    simpa [prefixWord, tailWord_1045735, baseEnd_1045735] using wordTrace_append hprefix tailTrace_1045735
  have hstable : (prefixWord ++ tailWord_1045735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045735).length < 2 ^ (prefixWord ++ tailWord_1045735).sum := by decide
  have hdescent : baseEnd_1045735 < baseStart_1045735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045744 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_1045744 : Nat := 118140960795 + 1045744 * 2 ^ 59
def prefixEnd_1045744 : Nat := 4983230072969 + 3 ^ 40 * 1045744 * 2
def baseEnd_1045744 : Nat := 357979542370307836993811

theorem tailTrace_1045744 : CollatzResearch.WordTrace tailWord_1045744 prefixEnd_1045744 357979542370307836993811 := by
  unfold tailWord_1045744
  simp only [CollatzResearch.WordTrace]
  refine ⟨19070708561727780850664143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25427611415637041134218857 19070708561727780850664143)
  ·
    refine ⟨28606062842591671275996215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19070708561727780850664143 28606062842591671275996215)
    ·
      refine ⟨42909094263887506913994323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28606062842591671275996215 42909094263887506913994323)
      ·
        refine ⟨64363641395831260370991485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42909094263887506913994323 64363641395831260370991485)
        ·
          refine ⟨24136365523436722639121807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64363641395831260370991485 24136365523436722639121807)
          ·
            refine ⟨36204548285155083958682711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24136365523436722639121807 36204548285155083958682711)
            ·
              refine ⟨54306822427732625938024067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36204548285155083958682711 54306822427732625938024067)
              ·
                refine ⟨81460233641598938907036101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54306822427732625938024067 81460233641598938907036101)
                ·
                  refine ⟨15273793807799801045069269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81460233641598938907036101 15273793807799801045069269)
                  ·
                    refine ⟨357979542370307836993811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15273793807799801045069269 357979542370307836993811)
                    ·
                      rfl

theorem cell22_1045744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_1045744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045744 prefixEnd_1045744 := by exact prefixLift 1045744
  have htrace : WordTrace (prefixWord ++ tailWord_1045744) baseStart_1045744 baseEnd_1045744 := by
    simpa [prefixWord, tailWord_1045744, baseEnd_1045744] using wordTrace_append hprefix tailTrace_1045744
  have hstable : (prefixWord ++ tailWord_1045744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045744).length < 2 ^ (prefixWord ++ tailWord_1045744).sum := by decide
  have hdescent : baseEnd_1045744 < baseStart_1045744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045795 : List Nat := [1, 1, 1, 4, 2, 3, 2, 4, 1, 3]
def baseStart_1045795 : Nat := 118140960795 + 1045795 * 2 ^ 59
def prefixEnd_1045795 : Nat := 4983230072969 + 3 ^ 40 * 1045795 * 2
def baseEnd_1045795 : Nat := 357997000712560703968655

theorem tailTrace_1045795 : CollatzResearch.WordTrace tailWord_1045795 prefixEnd_1045795 357997000712560703968655 := by
  unfold tailWord_1045795
  simp only [CollatzResearch.WordTrace]
  refine ⟨38143277246270797411434839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25428851497513864940956559 38143277246270797411434839)
  ·
    refine ⟨57214915869406196117152259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38143277246270797411434839 57214915869406196117152259)
    ·
      refine ⟨85822373804109294175728389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57214915869406196117152259 85822373804109294175728389)
      ·
        refine ⟨16091695088270492657949073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85822373804109294175728389 16091695088270492657949073)
        ·
          refine ⟨12068771316202869493461805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16091695088270492657949073 12068771316202869493461805)
          ·
            refine ⟨4525789243576076060048177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12068771316202869493461805 4525789243576076060048177)
            ·
              refine ⟨3394341932682057045036133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525789243576076060048177 3394341932682057045036133)
              ·
                refine ⟨636439112377885695944275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3394341932682057045036133 636439112377885695944275)
                ·
                  refine ⟨954658668566828543916413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636439112377885695944275 954658668566828543916413)
                  ·
                    refine ⟨357997000712560703968655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 954658668566828543916413 357997000712560703968655)
                    ·
                      rfl

theorem cell22_1045795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 3].length) (baseStart_1045795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045795 prefixEnd_1045795 := by exact prefixLift 1045795
  have htrace : WordTrace (prefixWord ++ tailWord_1045795) baseStart_1045795 baseEnd_1045795 := by
    simpa [prefixWord, tailWord_1045795, baseEnd_1045795] using wordTrace_append hprefix tailTrace_1045795
  have hstable : (prefixWord ++ tailWord_1045795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045795).length < 2 ^ (prefixWord ++ tailWord_1045795).sum := by decide
  have hdescent : baseEnd_1045795 < baseStart_1045795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045808 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 5]
def baseStart_1045808 : Nat := 118140960795 + 1045808 * 2 ^ 59
def prefixEnd_1045808 : Nat := 4983230072969 + 3 ^ 40 * 1045808 * 2
def baseEnd_1045808 : Nat := 119333816959411001131205

theorem tailTrace_1045808 : CollatzResearch.WordTrace tailWord_1045808 prefixEnd_1045808 119333816959411001131205 := by
  unfold tailWord_1045808
  simp only [CollatzResearch.WordTrace]
  refine ⟨19071875697611850315829039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25429167596815800421105385 19071875697611850315829039)
  ·
    refine ⟨28607813546417775473743559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19071875697611850315829039 28607813546417775473743559)
    ·
      refine ⟨42911720319626663210615339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28607813546417775473743559 42911720319626663210615339)
      ·
        refine ⟨64367580479439994815923009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42911720319626663210615339 64367580479439994815923009)
        ·
          refine ⟨48275685359579996111942257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64367580479439994815923009 48275685359579996111942257)
          ·
            refine ⟨36206764019684997083956693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48275685359579996111942257 36206764019684997083956693)
            ·
              refine ⟨848596031711367119155235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36206764019684997083956693 848596031711367119155235)
              ·
                refine ⟨1272894047567050678732853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848596031711367119155235 1272894047567050678732853)
                ·
                  refine ⟨119333816959411001131205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1272894047567050678732853 119333816959411001131205)
                  ·
                    rfl

theorem cell22_1045808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 5].length) (baseStart_1045808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045808 prefixEnd_1045808 := by exact prefixLift 1045808
  have htrace : WordTrace (prefixWord ++ tailWord_1045808) baseStart_1045808 baseEnd_1045808 := by
    simpa [prefixWord, tailWord_1045808, baseEnd_1045808] using wordTrace_append hprefix tailTrace_1045808
  have hstable : (prefixWord ++ tailWord_1045808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045808).length < 2 ^ (prefixWord ++ tailWord_1045808).sum := by decide
  have hdescent : baseEnd_1045808 < baseStart_1045808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045814 : List Nat := [5, 1, 2, 3, 2, 1, 2, 6]
def baseStart_1045814 : Nat := 118140960795 + 1045814 * 2 ^ 59
def prefixEnd_1045814 : Nat := 4983230072969 + 3 ^ 40 * 1045814 * 2
def baseEnd_1045814 : Nat := 39778167200094554193733

theorem tailTrace_1045814 : CollatzResearch.WordTrace tailWord_1045814 prefixEnd_1045814 39778167200094554193733 := by
  unfold tailWord_1045814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383998139575122728523531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25429313488801309104250997 2383998139575122728523531)
  ·
    refine ⟨3575997209362684092785297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2383998139575122728523531 3575997209362684092785297)
    ·
      refine ⟨2681997907022013069588973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3575997209362684092785297 2681997907022013069588973)
      ·
        refine ⟨1005749215133254901095865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2681997907022013069588973 1005749215133254901095865)
        ·
          refine ⟨754311911349941175821899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005749215133254901095865 754311911349941175821899)
          ·
            refine ⟨1131467867024911763732849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754311911349941175821899 1131467867024911763732849)
            ·
              refine ⟨848600900268683822799637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131467867024911763732849 848600900268683822799637)
              ·
                refine ⟨39778167200094554193733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 848600900268683822799637 39778167200094554193733)
                ·
                  rfl

theorem cell22_1045814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_1045814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045814 prefixEnd_1045814 := by exact prefixLift 1045814
  have htrace : WordTrace (prefixWord ++ tailWord_1045814) baseStart_1045814 baseEnd_1045814 := by
    simpa [prefixWord, tailWord_1045814, baseEnd_1045814] using wordTrace_append hprefix tailTrace_1045814
  have hstable : (prefixWord ++ tailWord_1045814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045814).length < 2 ^ (prefixWord ++ tailWord_1045814).sum := by decide
  have hdescent : baseEnd_1045814 < baseStart_1045814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045838 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_1045838 : Nat := 118140960795 + 1045838 * 2 ^ 59
def prefixEnd_1045838 : Nat := 4983230072969 + 3 ^ 40 * 1045838 * 2
def baseEnd_1045838 : Nat := 358011720491322925143523

theorem tailTrace_1045838 : CollatzResearch.WordTrace tailWord_1045838 prefixEnd_1045838 358011720491322925143523 := by
  unfold tailWord_1045838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4768105698139376969406271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25429897056743343836833445 4768105698139376969406271)
  ·
    refine ⟨7152158547209065454109407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4768105698139376969406271 7152158547209065454109407)
    ·
      refine ⟨10728237820813598181164111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7152158547209065454109407 10728237820813598181164111)
      ·
        refine ⟨16092356731220397271746167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10728237820813598181164111 16092356731220397271746167)
        ·
          refine ⟨24138535096830595907619251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16092356731220397271746167 24138535096830595907619251)
          ·
            refine ⟨36207802645245893861428877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24138535096830595907619251 36207802645245893861428877)
            ·
              refine ⟨13577925991967210198035829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36207802645245893861428877 13577925991967210198035829)
              ·
                refine ⟨1272930561746925956065859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13577925991967210198035829 1272930561746925956065859)
                ·
                  refine ⟨1909395842620388934098789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272930561746925956065859 1909395842620388934098789)
                  ·
                    refine ⟨358011720491322925143523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1909395842620388934098789 358011720491322925143523)
                    ·
                      rfl

theorem cell22_1045838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_1045838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045838 prefixEnd_1045838 := by exact prefixLift 1045838
  have htrace : WordTrace (prefixWord ++ tailWord_1045838) baseStart_1045838 baseEnd_1045838 := by
    simpa [prefixWord, tailWord_1045838, baseEnd_1045838] using wordTrace_append hprefix tailTrace_1045838
  have hstable : (prefixWord ++ tailWord_1045838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045838).length < 2 ^ (prefixWord ++ tailWord_1045838).sum := by decide
  have hdescent : baseEnd_1045838 < baseStart_1045838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045881 : List Nat := [1, 2, 1, 3, 2, 1, 4, 8]
def baseStart_1045881 : Nat := 118140960795 + 1045881 * 2 ^ 59
def prefixEnd_1045881 : Nat := 4983230072969 + 3 ^ 40 * 1045881 * 2
def baseEnd_1045881 : Nat := 39780715585565016257599

theorem tailTrace_1045881 : CollatzResearch.WordTrace tailWord_1045881 prefixEnd_1045881 39780715585565016257599 := by
  unfold tailWord_1045881
  simp only [CollatzResearch.WordTrace]
  refine ⟨38146413923959234099065497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25430942615972822732710331 38146413923959234099065497)
  ·
    refine ⟨28609810442969425574299123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38146413923959234099065497 28609810442969425574299123)
    ·
      refine ⟨42914715664454138361448685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28609810442969425574299123 42914715664454138361448685)
      ·
        refine ⟨16093018374170301885543257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42914715664454138361448685 16093018374170301885543257)
        ·
          refine ⟨12069763780627726414157443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16093018374170301885543257 12069763780627726414157443)
          ·
            refine ⟨18104645670941589621236165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12069763780627726414157443 18104645670941589621236165)
            ·
              refine ⟨3394621063301548053981781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18104645670941589621236165 3394621063301548053981781)
              ·
                refine ⟨39780715585565016257599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3394621063301548053981781 39780715585565016257599)
                ·
                  rfl

theorem cell22_1045881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 8].length) (baseStart_1045881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045881 prefixEnd_1045881 := by exact prefixLift 1045881
  have htrace : WordTrace (prefixWord ++ tailWord_1045881) baseStart_1045881 baseEnd_1045881 := by
    simpa [prefixWord, tailWord_1045881, baseEnd_1045881] using wordTrace_append hprefix tailTrace_1045881
  have hstable : (prefixWord ++ tailWord_1045881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045881).length < 2 ^ (prefixWord ++ tailWord_1045881).sum := by decide
  have hdescent : baseEnd_1045881 < baseStart_1045881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045883 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 2, 4]
def baseStart_1045883 : Nat := 118140960795 + 1045883 * 2 ^ 59
def prefixEnd_1045883 : Nat := 4983230072969 + 3 ^ 40 * 1045883 * 2
def baseEnd_1045883 : Nat := 358027124910957807768385

theorem tailTrace_1045883 : CollatzResearch.WordTrace tailWord_1045883 prefixEnd_1045883 358027124910957807768385 := by
  unfold tailWord_1045883
  simp only [CollatzResearch.WordTrace]
  refine ⟨38146486869951988440638303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25430991246634658960425535 38146486869951988440638303)
  ·
    refine ⟨57219730304927982660957455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38146486869951988440638303 57219730304927982660957455)
    ·
      refine ⟨85829595457391973991436183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57219730304927982660957455 85829595457391973991436183)
      ·
        refine ⟨128744393186087960987154275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85829595457391973991436183 128744393186087960987154275)
        ·
          refine ⟨193116589779131941480731413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128744393186087960987154275 193116589779131941480731413)
          ·
            refine ⟨9052340145896809756909285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193116589779131941480731413 9052340145896809756909285)
            ·
              refine ⟨1697313777355651829420491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9052340145896809756909285 1697313777355651829420491)
              ·
                refine ⟨2545970666033477744130737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697313777355651829420491 2545970666033477744130737)
                ·
                  refine ⟨1909477999525108308098053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2545970666033477744130737 1909477999525108308098053)
                  ·
                    refine ⟨358027124910957807768385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1909477999525108308098053 358027124910957807768385)
                    ·
                      rfl

theorem cell22_1045883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 4].length) (baseStart_1045883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1045883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1045883 prefixEnd_1045883 := by exact prefixLift 1045883
  have htrace : WordTrace (prefixWord ++ tailWord_1045883) baseStart_1045883 baseEnd_1045883 := by
    simpa [prefixWord, tailWord_1045883, baseEnd_1045883] using wordTrace_append hprefix tailTrace_1045883
  have hstable : (prefixWord ++ tailWord_1045883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045883).length < 2 ^ (prefixWord ++ tailWord_1045883).sum := by decide
  have hdescent : baseEnd_1045883 < baseStart_1045883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046033 : List Nat := [1, 2, 2, 1, 1, 2, 6, 7]
def baseStart_1046033 : Nat := 118140960795 + 1046033 * 2 ^ 59
def prefixEnd_1046033 : Nat := 4983230072969 + 3 ^ 40 * 1046033 * 2
def baseEnd_1046033 : Nat := 39786496997378601835325

theorem tailTrace_1046033 : CollatzResearch.WordTrace tailWord_1046033 prefixEnd_1046033 39786496997378601835325 := by
  unfold tailWord_1046033
  simp only [CollatzResearch.WordTrace]
  refine ⟨38151957819408564058598753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25434638546272376039065835 38151957819408564058598753)
  ·
    refine ⟨28613968364556423043949065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38151957819408564058598753 28613968364556423043949065)
    ·
      refine ⟨21460476273417317282961799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28613968364556423043949065 21460476273417317282961799)
      ·
        refine ⟨32190714410125975924442699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21460476273417317282961799 32190714410125975924442699)
        ·
          refine ⟨48286071615188963886664049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32190714410125975924442699 48286071615188963886664049)
          ·
            refine ⟨36214553711391722914998037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48286071615188963886664049 36214553711391722914998037)
            ·
              refine ⟨1697557205221487011640533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36214553711391722914998037 1697557205221487011640533)
              ·
                refine ⟨39786496997378601835325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1697557205221487011640533 39786496997378601835325)
                ·
                  rfl

theorem cell22_1046033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 7].length) (baseStart_1046033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046033 prefixEnd_1046033 := by exact prefixLift 1046033
  have htrace : WordTrace (prefixWord ++ tailWord_1046033) baseStart_1046033 baseEnd_1046033 := by
    simpa [prefixWord, tailWord_1046033, baseEnd_1046033] using wordTrace_append hprefix tailTrace_1046033
  have hstable : (prefixWord ++ tailWord_1046033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046033).length < 2 ^ (prefixWord ++ tailWord_1046033).sum := by decide
  have hdescent : baseEnd_1046033 < baseStart_1046033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046037 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_1046037 : Nat := 118140960795 + 1046037 * 2 ^ 59
def prefixEnd_1046037 : Nat := 4983230072969 + 3 ^ 40 * 1046037 * 2
def baseEnd_1046037 : Nat := 358079842258152739417913

theorem tailTrace_1046037 : CollatzResearch.WordTrace tailWord_1046037 prefixEnd_1046037 358079842258152739417913 := by
  unfold tailWord_1046037
  simp only [CollatzResearch.WordTrace]
  refine ⟨38152103711394072741744365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25434735807596048494496243 38152103711394072741744365)
  ·
    refine ⟨14307038891772777278154137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38152103711394072741744365 14307038891772777278154137)
    ·
      refine ⟨10730279168829582958615603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14307038891772777278154137 10730279168829582958615603)
      ·
        refine ⟨16095418753244374437923405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10730279168829582958615603 16095418753244374437923405)
        ·
          refine ⟨6035782032466640414221277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16095418753244374437923405 6035782032466640414221277)
          ·
            refine ⟨2263418262174990155332979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6035782032466640414221277 2263418262174990155332979)
            ·
              refine ⟨3395127393262485232999469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263418262174990155332979 3395127393262485232999469)
              ·
                refine ⟨1273172772473431962374801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3395127393262485232999469 1273172772473431962374801)
                ·
                  refine ⟨954879579355073971781101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1273172772473431962374801 954879579355073971781101)
                  ·
                    refine ⟨358079842258152739417913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 954879579355073971781101 358079842258152739417913)
                    ·
                      rfl

theorem cell22_1046037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_1046037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046037 prefixEnd_1046037 := by exact prefixLift 1046037
  have htrace : WordTrace (prefixWord ++ tailWord_1046037) baseStart_1046037 baseEnd_1046037 := by
    simpa [prefixWord, tailWord_1046037, baseEnd_1046037] using wordTrace_append hprefix tailTrace_1046037
  have hstable : (prefixWord ++ tailWord_1046037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046037).length < 2 ^ (prefixWord ++ tailWord_1046037).sum := by decide
  have hdescent : baseEnd_1046037 < baseStart_1046037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046189 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1046189 : Nat := 118140960795 + 1046189 * 2 ^ 59
def prefixEnd_1046189 : Nat := 4983230072969 + 3 ^ 40 * 1046189 * 2
def baseEnd_1046189 : Nat := 358131874964475009617447

theorem tailTrace_1046189 : CollatzResearch.WordTrace tailWord_1046189 prefixEnd_1046189 358131874964475009617447 := by
  unfold tailWord_1046189
  simp only [CollatzResearch.WordTrace]
  refine ⟨38157647606843402701277621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25438431737895601800851747 38157647606843402701277621)
  ·
    refine ⟨3577279463141569003244777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38157647606843402701277621 3577279463141569003244777)
    ·
      refine ⟨2682959597356176752433583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3577279463141569003244777 2682959597356176752433583)
      ·
        refine ⟨4024439396034265128650375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682959597356176752433583 4024439396034265128650375)
        ·
          refine ⟨6036659094051397692975563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024439396034265128650375 6036659094051397692975563)
          ·
            refine ⟨9054988641077096539463345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6036659094051397692975563 9054988641077096539463345)
            ·
              refine ⟨6791241480807822404597509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9054988641077096539463345 6791241480807822404597509)
              ·
                refine ⟨1273357777651466700862033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6791241480807822404597509 1273357777651466700862033)
                ·
                  refine ⟨955018333238600025646525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1273357777651466700862033 955018333238600025646525)
                  ·
                    refine ⟨358131874964475009617447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955018333238600025646525 358131874964475009617447)
                    ·
                      rfl

theorem cell22_1046189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1046189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046189 prefixEnd_1046189 := by exact prefixLift 1046189
  have htrace : WordTrace (prefixWord ++ tailWord_1046189) baseStart_1046189 baseEnd_1046189 := by
    simpa [prefixWord, tailWord_1046189, baseEnd_1046189] using wordTrace_append hprefix tailTrace_1046189
  have hstable : (prefixWord ++ tailWord_1046189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046189).length < 2 ^ (prefixWord ++ tailWord_1046189).sum := by decide
  have hdescent : baseEnd_1046189 < baseStart_1046189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046206 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_1046206 : Nat := 118140960795 + 1046206 * 2 ^ 59
def prefixEnd_1046206 : Nat := 4983230072969 + 3 ^ 40 * 1046206 * 2
def baseEnd_1046206 : Nat := 358137694411892631942395

theorem tailTrace_1046206 : CollatzResearch.WordTrace tailWord_1046206 prefixEnd_1046206 358137694411892631942395 := by
  unfold tailWord_1046206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769783455972726825580809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25438845098521209736430981 4769783455972726825580809)
  ·
    refine ⟨3577337591979545119185607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4769783455972726825580809 3577337591979545119185607)
    ·
      refine ⟨5366006387969317678778411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3577337591979545119185607 5366006387969317678778411)
      ·
        refine ⟨8049009581953976518167617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366006387969317678778411 8049009581953976518167617)
        ·
          refine ⟨6036757186465482388625713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8049009581953976518167617 6036757186465482388625713)
          ·
            refine ⟨4527567889849111791469285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6036757186465482388625713 4527567889849111791469285)
            ·
              refine ⟨848918979346708460900491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4527567889849111791469285 848918979346708460900491)
              ·
                refine ⟨1273378469020062691350737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848918979346708460900491 1273378469020062691350737)
                ·
                  refine ⟨955033851765047018513053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1273378469020062691350737 955033851765047018513053)
                  ·
                    refine ⟨358137694411892631942395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955033851765047018513053 358137694411892631942395)
                    ·
                      rfl

theorem cell22_1046206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_1046206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046206 prefixEnd_1046206 := by exact prefixLift 1046206
  have htrace : WordTrace (prefixWord ++ tailWord_1046206) baseStart_1046206 baseEnd_1046206 := by
    simpa [prefixWord, tailWord_1046206, baseEnd_1046206] using wordTrace_append hprefix tailTrace_1046206
  have hstable : (prefixWord ++ tailWord_1046206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046206).length < 2 ^ (prefixWord ++ tailWord_1046206).sum := by decide
  have hdescent : baseEnd_1046206 < baseStart_1046206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046210 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1046210 : Nat := 118140960795 + 1046210 * 2 ^ 59
def prefixEnd_1046210 : Nat := 4983230072969 + 3 ^ 40 * 1046210 * 2
def baseEnd_1046210 : Nat := 358139063693637954842383

theorem tailTrace_1046210 : CollatzResearch.WordTrace tailWord_1046210 prefixEnd_1046210 358139063693637954842383 := by
  unfold tailWord_1046210
  simp only [CollatzResearch.WordTrace]
  refine ⟨9539603384941830821948021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25438942359844882191861389 9539603384941830821948021)
  ·
    refine ⟨894337817338296639557627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9539603384941830821948021 894337817338296639557627)
    ·
      refine ⟨1341506726007444959336441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894337817338296639557627 1341506726007444959336441)
      ·
        refine ⟨1006130044505583719502331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1341506726007444959336441 1006130044505583719502331)
        ·
          refine ⟨1509195066758375579253497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006130044505583719502331 1509195066758375579253497)
          ·
            refine ⟨1131896300068781684440123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1509195066758375579253497 1131896300068781684440123)
            ·
              refine ⟨1697844450103172526660185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131896300068781684440123 1697844450103172526660185)
              ·
                refine ⟨1273383337577379394995139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1697844450103172526660185 1273383337577379394995139)
                ·
                  refine ⟨1910075006366069092492709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273383337577379394995139 1910075006366069092492709)
                  ·
                    refine ⟨358139063693637954842383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910075006366069092492709 358139063693637954842383)
                    ·
                      rfl

theorem cell22_1046210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1046210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046210 prefixEnd_1046210 := by exact prefixLift 1046210
  have htrace : WordTrace (prefixWord ++ tailWord_1046210) baseStart_1046210 baseEnd_1046210 := by
    simpa [prefixWord, tailWord_1046210, baseEnd_1046210] using wordTrace_append hprefix tailTrace_1046210
  have hstable : (prefixWord ++ tailWord_1046210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046210).length < 2 ^ (prefixWord ++ tailWord_1046210).sum := by decide
  have hdescent : baseEnd_1046210 < baseStart_1046210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046221 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1046221 : Nat := 118140960795 + 1046221 * 2 ^ 59
def prefixEnd_1046221 : Nat := 4983230072969 + 3 ^ 40 * 1046221 * 2
def baseEnd_1046221 : Nat := 358142829218437592817349

theorem tailTrace_1046221 : CollatzResearch.WordTrace tailWord_1046221 prefixEnd_1046221 358142829218437592817349 := by
  unfold tailWord_1046221
  simp only [CollatzResearch.WordTrace]
  refine ⟨38158814742727472166442517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25439209828484981444295011 38158814742727472166442517)
  ·
    refine ⟨1788694441065350257801993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38158814742727472166442517 1788694441065350257801993)
    ·
      refine ⟨1341520830799012693351495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1788694441065350257801993 1341520830799012693351495)
      ·
        refine ⟨2012281246198519040027243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1341520830799012693351495 2012281246198519040027243)
        ·
          refine ⟨3018421869297778560040865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012281246198519040027243 3018421869297778560040865)
          ·
            refine ⟨2263816401973333920030649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3018421869297778560040865 2263816401973333920030649)
            ·
              refine ⟨1697862301480000440022987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263816401973333920030649 1697862301480000440022987)
              ·
                refine ⟨2546793452220000660034481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697862301480000440022987 2546793452220000660034481)
                ·
                  refine ⟨1910095089165000495025861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546793452220000660034481 1910095089165000495025861)
                  ·
                    refine ⟨358142829218437592817349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910095089165000495025861 358142829218437592817349)
                    ·
                      rfl

theorem cell22_1046221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1046221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046221 prefixEnd_1046221 := by exact prefixLift 1046221
  have htrace : WordTrace (prefixWord ++ tailWord_1046221) baseStart_1046221 baseEnd_1046221 := by
    simpa [prefixWord, tailWord_1046221, baseEnd_1046221] using wordTrace_append hprefix tailTrace_1046221
  have hstable : (prefixWord ++ tailWord_1046221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046221).length < 2 ^ (prefixWord ++ tailWord_1046221).sum := by decide
  have hdescent : baseEnd_1046221 < baseStart_1046221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046251 : List Nat := [1, 1, 1, 1, 2, 4, 6, 2, 1, 3]
def baseStart_1046251 : Nat := 118140960795 + 1046251 * 2 ^ 59
def prefixEnd_1046251 : Nat := 4983230072969 + 3 ^ 40 * 1046251 * 2
def baseEnd_1046251 : Nat := 358153098831527514567257

theorem tailTrace_1046251 : CollatzResearch.WordTrace tailWord_1046251 prefixEnd_1046251 358153098831527514567257 := by
  unfold tailWord_1046251
  simp only [CollatzResearch.WordTrace]
  refine ⟨38159908932618787290034607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25439939288412524860023071 38159908932618787290034607)
  ·
    refine ⟨57239863398928180935051911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38159908932618787290034607 57239863398928180935051911)
    ·
      refine ⟨85859795098392271402577867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57239863398928180935051911 85859795098392271402577867)
      ·
        refine ⟨128789692647588407103866801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85859795098392271402577867 128789692647588407103866801)
        ·
          refine ⟨96592269485691305327900101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128789692647588407103866801 96592269485691305327900101)
          ·
            refine ⟨18111050528567119748981269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96592269485691305327900101 18111050528567119748981269)
            ·
              refine ⟨848955493526583738233497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18111050528567119748981269 848955493526583738233497)
              ·
                refine ⟨636716620144937803675123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848955493526583738233497 636716620144937803675123)
                ·
                  refine ⟨955074930217406705512685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636716620144937803675123 955074930217406705512685)
                  ·
                    refine ⟨358153098831527514567257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955074930217406705512685 358153098831527514567257)
                    ·
                      rfl

theorem cell22_1046251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 3].length) (baseStart_1046251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046251 prefixEnd_1046251 := by exact prefixLift 1046251
  have htrace : WordTrace (prefixWord ++ tailWord_1046251) baseStart_1046251 baseEnd_1046251 := by
    simpa [prefixWord, tailWord_1046251, baseEnd_1046251] using wordTrace_append hprefix tailTrace_1046251
  have hstable : (prefixWord ++ tailWord_1046251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046251).length < 2 ^ (prefixWord ++ tailWord_1046251).sum := by decide
  have hdescent : baseEnd_1046251 < baseStart_1046251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046262 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1046262 : Nat := 118140960795 + 1046262 * 2 ^ 59
def prefixEnd_1046262 : Nat := 4983230072969 + 3 ^ 40 * 1046262 * 2
def baseEnd_1046262 : Nat := 358156864356327152542223

theorem tailTrace_1046262 : CollatzResearch.WordTrace tailWord_1046262 prefixEnd_1046262 358156864356327152542223 := by
  unfold tailWord_1046262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385019383473683510542815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25440206757052624112456693 2385019383473683510542815)
  ·
    refine ⟨3577529075210525265814223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2385019383473683510542815 3577529075210525265814223)
    ·
      refine ⟨5366293612815787898721335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3577529075210525265814223 5366293612815787898721335)
      ·
        refine ⟨8049440419223681848082003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366293612815787898721335 8049440419223681848082003)
        ·
          refine ⟨12074160628835522772123005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049440419223681848082003 12074160628835522772123005)
          ·
            refine ⟨4527810235813321039546127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12074160628835522772123005 4527810235813321039546127)
            ·
              refine ⟨6791715353719981559319191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527810235813321039546127 6791715353719981559319191)
              ·
                refine ⟨10187573030579972338978787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6791715353719981559319191 10187573030579972338978787)
                ·
                  refine ⟨15281359545869958508468181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10187573030579972338978787 15281359545869958508468181)
                  ·
                    refine ⟨358156864356327152542223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15281359545869958508468181 358156864356327152542223)
                    ·
                      rfl

theorem cell22_1046262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1046262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046262 prefixEnd_1046262 := by exact prefixLift 1046262
  have htrace : WordTrace (prefixWord ++ tailWord_1046262) baseStart_1046262 baseEnd_1046262 := by
    simpa [prefixWord, tailWord_1046262, baseEnd_1046262] using wordTrace_append hprefix tailTrace_1046262
  have hstable : (prefixWord ++ tailWord_1046262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046262).length < 2 ^ (prefixWord ++ tailWord_1046262).sum := by decide
  have hdescent : baseEnd_1046262 < baseStart_1046262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046275 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 8]
def baseStart_1046275 : Nat := 118140960795 + 1046275 * 2 ^ 59
def prefixEnd_1046275 : Nat := 4983230072969 + 3 ^ 40 * 1046275 * 2
def baseEnd_1046275 : Nat := 119387104840666483989061

theorem tailTrace_1046275 : CollatzResearch.WordTrace tailWord_1046275 prefixEnd_1046275 119387104840666483989061 := by
  unfold tailWord_1046275
  simp only [CollatzResearch.WordTrace]
  refine ⟨38160784284531839388908279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25440522856354559592605519 38160784284531839388908279)
  ·
    refine ⟨57241176426797759083362419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38160784284531839388908279 57241176426797759083362419)
    ·
      refine ⟨85861764640196638625043629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57241176426797759083362419 85861764640196638625043629)
      ·
        refine ⟨32198161740073739484391361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85861764640196638625043629 32198161740073739484391361)
        ·
          refine ⟨24148621305055304613293521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32198161740073739484391361 24148621305055304613293521)
          ·
            refine ⟨18111465978791478459970141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24148621305055304613293521 18111465978791478459970141)
            ·
              refine ⟨6791799742046804422488803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18111465978791478459970141 6791799742046804422488803)
              ·
                refine ⟨10187699613070206633733205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6791799742046804422488803 10187699613070206633733205)
                ·
                  refine ⟨119387104840666483989061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10187699613070206633733205 119387104840666483989061)
                  ·
                    rfl

theorem cell22_1046275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 8].length) (baseStart_1046275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046275 prefixEnd_1046275 := by exact prefixLift 1046275
  have htrace : WordTrace (prefixWord ++ tailWord_1046275) baseStart_1046275 baseEnd_1046275 := by
    simpa [prefixWord, tailWord_1046275, baseEnd_1046275] using wordTrace_append hprefix tailTrace_1046275
  have hstable : (prefixWord ++ tailWord_1046275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046275).length < 2 ^ (prefixWord ++ tailWord_1046275).sum := by decide
  have hdescent : baseEnd_1046275 < baseStart_1046275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046309 : List Nat := [1, 3, 1, 2, 3, 2, 2, 4, 4]
def baseStart_1046309 : Nat := 118140960795 + 1046309 * 2 ^ 59
def prefixEnd_1046309 : Nat := 4983230072969 + 3 ^ 40 * 1046309 * 2
def baseEnd_1046309 : Nat := 119390984472278232205693

theorem tailTrace_1046309 : CollatzResearch.WordTrace tailWord_1046309 prefixEnd_1046309 119390984472278232205693 := by
  unfold tailWord_1046309
  simp only [CollatzResearch.WordTrace]
  refine ⟨38162024366408663195645981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25441349577605775463763987 38162024366408663195645981)
  ·
    refine ⟨14310759137403248698367243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38162024366408663195645981 14310759137403248698367243)
    ·
      refine ⟨21466138706104873047550865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14310759137403248698367243 21466138706104873047550865)
      ·
        refine ⟨16099604029578654785663149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21466138706104873047550865 16099604029578654785663149)
        ·
          refine ⟨6037351511091995544623681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16099604029578654785663149 6037351511091995544623681)
          ·
            refine ⟨4528013633318996658467761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6037351511091995544623681 4528013633318996658467761)
            ·
              refine ⟨3396010224989247493850821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528013633318996658467761 3396010224989247493850821)
              ·
                refine ⟨636751917185483905097029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3396010224989247493850821 636751917185483905097029)
                ·
                  refine ⟨119390984472278232205693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636751917185483905097029 119390984472278232205693)
                  ·
                    rfl

theorem cell22_1046309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_1046309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046309 prefixEnd_1046309 := by exact prefixLift 1046309
  have htrace : WordTrace (prefixWord ++ tailWord_1046309) baseStart_1046309 baseEnd_1046309 := by
    simpa [prefixWord, tailWord_1046309, baseEnd_1046309] using wordTrace_append hprefix tailTrace_1046309
  have hstable : (prefixWord ++ tailWord_1046309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046309).length < 2 ^ (prefixWord ++ tailWord_1046309).sum := by decide
  have hdescent : baseEnd_1046309 < baseStart_1046309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046322 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1046322 : Nat := 118140960795 + 1046322 * 2 ^ 59
def prefixEnd_1046322 : Nat := 4983230072969 + 3 ^ 40 * 1046322 * 2
def baseEnd_1046322 : Nat := 358177403582506996042039

theorem tailTrace_1046322 : CollatzResearch.WordTrace tailWord_1046322 prefixEnd_1046322 358177403582506996042039 := by
  unfold tailWord_1046322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9540624628840391603967305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25441665676907710943912813 9540624628840391603967305)
  ·
    refine ⟨7155468471630293702975479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9540624628840391603967305 7155468471630293702975479)
    ·
      refine ⟨10733202707445440554463219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7155468471630293702975479 10733202707445440554463219)
      ·
        refine ⟨16099804061168160831694829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733202707445440554463219 16099804061168160831694829)
        ·
          refine ⟨6037426522938060311885561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16099804061168160831694829 6037426522938060311885561)
          ·
            refine ⟨4528069892203545233914171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6037426522938060311885561 4528069892203545233914171)
            ·
              refine ⟨6792104838305317850871257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528069892203545233914171 6792104838305317850871257)
              ·
                refine ⟨5094078628728988388153443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792104838305317850871257 5094078628728988388153443)
                ·
                  refine ⟨7641117943093482582230165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094078628728988388153443 7641117943093482582230165)
                  ·
                    refine ⟨358177403582506996042039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7641117943093482582230165 358177403582506996042039)
                    ·
                      rfl

theorem cell22_1046322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1046322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046322 prefixEnd_1046322 := by exact prefixLift 1046322
  have htrace : WordTrace (prefixWord ++ tailWord_1046322) baseStart_1046322 baseEnd_1046322 := by
    simpa [prefixWord, tailWord_1046322, baseEnd_1046322] using wordTrace_append hprefix tailTrace_1046322
  have hstable : (prefixWord ++ tailWord_1046322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046322).length < 2 ^ (prefixWord ++ tailWord_1046322).sum := by decide
  have hdescent : baseEnd_1046322 < baseStart_1046322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046397 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1046397 : Nat := 118140960795 + 1046397 * 2 ^ 59
def prefixEnd_1046397 : Nat := 4983230072969 + 3 ^ 40 * 1046397 * 2
def baseEnd_1046397 : Nat := 358203077615231800416809

theorem tailTrace_1046397 : CollatzResearch.WordTrace tailWord_1046397 prefixEnd_1046397 358203077615231800416809 := by
  unfold tailWord_1046397
  simp only [CollatzResearch.WordTrace]
  refine ⟨38165233990089854224849445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25443489326726569483232963 38165233990089854224849445)
  ·
    refine ⟨7155981373141847667159271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38165233990089854224849445 7155981373141847667159271)
    ·
      refine ⟨10733972059712771500738907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7155981373141847667159271 10733972059712771500738907)
      ·
        refine ⟨16100958089569157251108361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733972059712771500738907 16100958089569157251108361)
        ·
          refine ⟨12075718567176867938331271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16100958089569157251108361 12075718567176867938331271)
          ·
            refine ⟨18113577850765301907496907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12075718567176867938331271 18113577850765301907496907)
            ·
              refine ⟨27170366776147952861245361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18113577850765301907496907 27170366776147952861245361)
              ·
                refine ⟨20377775082110964645934021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27170366776147952861245361 20377775082110964645934021)
                ·
                  refine ⟨3820832827895805871112629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20377775082110964645934021 3820832827895805871112629)
                  ·
                    refine ⟨358203077615231800416809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3820832827895805871112629 358203077615231800416809)
                    ·
                      rfl

theorem cell22_1046397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1046397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046397 prefixEnd_1046397 := by exact prefixLift 1046397
  have htrace : WordTrace (prefixWord ++ tailWord_1046397) baseStart_1046397 baseEnd_1046397 := by
    simpa [prefixWord, tailWord_1046397, baseEnd_1046397] using wordTrace_append hprefix tailTrace_1046397
  have hstable : (prefixWord ++ tailWord_1046397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046397).length < 2 ^ (prefixWord ++ tailWord_1046397).sum := by decide
  have hdescent : baseEnd_1046397 < baseStart_1046397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046420 : List Nat := [2, 4, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1046420 : Nat := 118140960795 + 1046420 * 2 ^ 59
def prefixEnd_1046420 : Nat := 4983230072969 + 3 ^ 40 * 1046420 * 2
def baseEnd_1046420 : Nat := 358210950985267407091739

theorem tailTrace_1046420 : CollatzResearch.WordTrace tailWord_1046420 prefixEnd_1046420 358210950985267407091739 := by
  unfold tailWord_1046420
  simp only [CollatzResearch.WordTrace]
  refine ⟨19083036434503264576468357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25444048579337686101957809 19083036434503264576468357)
  ·
    refine ⟨3578069331469362108087817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19083036434503264576468357 3578069331469362108087817)
    ·
      refine ⟨2683551998602021581065863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3578069331469362108087817 2683551998602021581065863)
      ·
        refine ⟨4025327997903032371598795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2683551998602021581065863 4025327997903032371598795)
        ·
          refine ⟨6037991996854548557398193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4025327997903032371598795 6037991996854548557398193)
          ·
            refine ⟨4528493997640911418048645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6037991996854548557398193 4528493997640911418048645)
            ·
              refine ⟨849092624557670890884121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4528493997640911418048645 849092624557670890884121)
              ·
                refine ⟨636819468418253168163091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849092624557670890884121 636819468418253168163091)
                ·
                  refine ⟨955229202627379752244637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636819468418253168163091 955229202627379752244637)
                  ·
                    refine ⟨358210950985267407091739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955229202627379752244637 358210950985267407091739)
                    ·
                      rfl

theorem cell22_1046420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1046420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046420 prefixEnd_1046420 := by exact prefixLift 1046420
  have htrace : WordTrace (prefixWord ++ tailWord_1046420) baseStart_1046420 baseEnd_1046420 := by
    simpa [prefixWord, tailWord_1046420, baseEnd_1046420] using wordTrace_append hprefix tailTrace_1046420
  have hstable : (prefixWord ++ tailWord_1046420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046420).length < 2 ^ (prefixWord ++ tailWord_1046420).sum := by decide
  have hdescent : baseEnd_1046420 < baseStart_1046420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046429 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1046429 : Nat := 118140960795 + 1046429 * 2 ^ 59
def prefixEnd_1046429 : Nat := 4983230072969 + 3 ^ 40 * 1046429 * 2
def baseEnd_1046429 : Nat := 358214031869194383616711

theorem tailTrace_1046429 : CollatzResearch.WordTrace tailWord_1046429 prefixEnd_1046429 358214031869194383616711 := by
  unfold tailWord_1046429
  simp only [CollatzResearch.WordTrace]
  refine ⟨38166401125973923690014341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25444267417315949126676227 38166401125973923690014341)
  ·
    refine ⟨7156200211120110691877689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38166401125973923690014341 7156200211120110691877689)
    ·
      refine ⟨5367150158340083018908267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7156200211120110691877689 5367150158340083018908267)
      ·
        refine ⟨8050725237510124528362401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5367150158340083018908267 8050725237510124528362401)
        ·
          refine ⟨6038043928132593396271801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8050725237510124528362401 6038043928132593396271801)
          ·
            refine ⟨4528532946099445047203851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6038043928132593396271801 4528532946099445047203851)
            ·
              refine ⟨6792799419149167570805777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528532946099445047203851 6792799419149167570805777)
              ·
                refine ⟨5094599564361875678104333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792799419149167570805777 5094599564361875678104333)
                ·
                  refine ⟨1910474836635703379289125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5094599564361875678104333 1910474836635703379289125)
                  ·
                    refine ⟨358214031869194383616711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910474836635703379289125 358214031869194383616711)
                    ·
                      rfl

theorem cell22_1046429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1046429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046429 prefixEnd_1046429 := by exact prefixLift 1046429
  have htrace : WordTrace (prefixWord ++ tailWord_1046429) baseStart_1046429 baseEnd_1046429 := by
    simpa [prefixWord, tailWord_1046429, baseEnd_1046429] using wordTrace_append hprefix tailTrace_1046429
  have hstable : (prefixWord ++ tailWord_1046429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046429).length < 2 ^ (prefixWord ++ tailWord_1046429).sum := by decide
  have hdescent : baseEnd_1046429 < baseStart_1046429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046461 : List Nat := [1, 4, 1, 2, 3, 1, 1, 5, 4]
def baseStart_1046461 : Nat := 118140960795 + 1046461 * 2 ^ 59
def prefixEnd_1046461 : Nat := 4983230072969 + 3 ^ 40 * 1046461 * 2
def baseEnd_1046461 : Nat := 119408328707718988938871

theorem tailTrace_1046461 : CollatzResearch.WordTrace tailWord_1046461 prefixEnd_1046461 119408328707718988938871 := by
  unfold tailWord_1046461
  simp only [CollatzResearch.WordTrace]
  refine ⟨38167568261857993155179237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25445045507905328770119491 38167568261857993155179237)
  ·
    refine ⟨7156419049098373716596107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38167568261857993155179237 7156419049098373716596107)
    ·
      refine ⟨10734628573647560574894161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7156419049098373716596107 10734628573647560574894161)
      ·
        refine ⟨8050971430235670431170621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10734628573647560574894161 8050971430235670431170621)
        ·
          refine ⟨3019114286338376411688983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8050971430235670431170621 3019114286338376411688983)
          ·
            refine ⟨4528671429507564617533475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019114286338376411688983 4528671429507564617533475)
            ·
              refine ⟨6793007144261346926300213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528671429507564617533475 6793007144261346926300213)
              ·
                refine ⟨636844419774501274340645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6793007144261346926300213 636844419774501274340645)
                ·
                  refine ⟨119408328707718988938871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636844419774501274340645 119408328707718988938871)
                  ·
                    rfl

theorem cell22_1046461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_1046461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046461 prefixEnd_1046461 := by exact prefixLift 1046461
  have htrace : WordTrace (prefixWord ++ tailWord_1046461) baseStart_1046461 baseEnd_1046461 := by
    simpa [prefixWord, tailWord_1046461, baseEnd_1046461] using wordTrace_append hprefix tailTrace_1046461
  have hstable : (prefixWord ++ tailWord_1046461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046461).length < 2 ^ (prefixWord ++ tailWord_1046461).sum := by decide
  have hdescent : baseEnd_1046461 < baseStart_1046461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046474 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_1046474 : Nat := 118140960795 + 1046474 * 2 ^ 59
def prefixEnd_1046474 : Nat := 4983230072969 + 3 ^ 40 * 1046474 * 2
def baseEnd_1046474 : Nat := 358229436288829266241573

theorem tailTrace_1046474 : CollatzResearch.WordTrace tailWord_1046474 prefixEnd_1046474 358229436288829266241573 := by
  unfold tailWord_1046474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9542010602702724093850619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25445361607207264250268317 9542010602702724093850619)
  ·
    refine ⟨14313015904054086140775929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9542010602702724093850619 14313015904054086140775929)
    ·
      refine ⟨10734761928040564605581947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14313015904054086140775929 10734761928040564605581947)
      ·
        refine ⟨16102142892060846908372921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10734761928040564605581947 16102142892060846908372921)
        ·
          refine ⟨12076607169045635181279691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16102142892060846908372921 12076607169045635181279691)
          ·
            refine ⟨18114910753568452771919537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12076607169045635181279691 18114910753568452771919537)
            ·
              refine ⟨13586183065176339578939653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18114910753568452771919537 13586183065176339578939653)
              ·
                refine ⟨2547409324720563671051185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13586183065176339578939653 2547409324720563671051185)
                ·
                  refine ⟨1910556993540422753288389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2547409324720563671051185 1910556993540422753288389)
                  ·
                    refine ⟨358229436288829266241573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910556993540422753288389 358229436288829266241573)
                    ·
                      rfl

theorem cell22_1046474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_1046474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046474 prefixEnd_1046474 := by exact prefixLift 1046474
  have htrace : WordTrace (prefixWord ++ tailWord_1046474) baseStart_1046474 baseEnd_1046474 := by
    simpa [prefixWord, tailWord_1046474, baseEnd_1046474] using wordTrace_append hprefix tailTrace_1046474
  have hstable : (prefixWord ++ tailWord_1046474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046474).length < 2 ^ (prefixWord ++ tailWord_1046474).sum := by decide
  have hdescent : baseEnd_1046474 < baseStart_1046474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046476 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_1046476 : Nat := 118140960795 + 1046476 * 2 ^ 59
def prefixEnd_1046476 : Nat := 4983230072969 + 3 ^ 40 * 1046476 * 2
def baseEnd_1046476 : Nat := 358230120929701927691567

theorem tailTrace_1046476 : CollatzResearch.WordTrace tailWord_1046476 prefixEnd_1046476 358230120929701927691567 := by
  unfold tailWord_1046476
  simp only [CollatzResearch.WordTrace]
  refine ⟨19084057678401825358487641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25445410237869100477983521 19084057678401825358487641)
  ·
    refine ⟨14313043258801369018865731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19084057678401825358487641 14313043258801369018865731)
    ·
      refine ⟨21469564888202053528298597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14313043258801369018865731 21469564888202053528298597)
      ·
        refine ⟨4025543416537885036555987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21469564888202053528298597 4025543416537885036555987)
        ·
          refine ⟨6038315124806827554833981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4025543416537885036555987 6038315124806827554833981)
          ·
            refine ⟨2264368171802560333062743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6038315124806827554833981 2264368171802560333062743)
            ·
              refine ⟨3396552257703840499594115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264368171802560333062743 3396552257703840499594115)
              ·
                refine ⟨5094828386555760749391173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396552257703840499594115 5094828386555760749391173)
                ·
                  refine ⟨955280322479205140510845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5094828386555760749391173 955280322479205140510845)
                  ·
                    refine ⟨358230120929701927691567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955280322479205140510845 358230120929701927691567)
                    ·
                      rfl

theorem cell22_1046476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_1046476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046476 prefixEnd_1046476 := by exact prefixLift 1046476
  have htrace : WordTrace (prefixWord ++ tailWord_1046476) baseStart_1046476 baseEnd_1046476 := by
    simpa [prefixWord, tailWord_1046476, baseEnd_1046476] using wordTrace_append hprefix tailTrace_1046476
  have hstable : (prefixWord ++ tailWord_1046476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046476).length < 2 ^ (prefixWord ++ tailWord_1046476).sum := by decide
  have hdescent : baseEnd_1046476 < baseStart_1046476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046493 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1046493 : Nat := 118140960795 + 1046493 * 2 ^ 59
def prefixEnd_1046493 : Nat := 4983230072969 + 3 ^ 40 * 1046493 * 2
def baseEnd_1046493 : Nat := 358235940377119550016515

theorem tailTrace_1046493 : CollatzResearch.WordTrace tailWord_1046493 prefixEnd_1046493 358235940377119550016515 := by
  unfold tailWord_1046493
  simp only [CollatzResearch.WordTrace]
  refine ⟨38168735397742062620344133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25445823598494708413562755 38168735397742062620344133)
  ·
    refine ⟨7156637887076636741314525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38168735397742062620344133 7156637887076636741314525)
    ·
      refine ⟨2683739207653738777992947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7156637887076636741314525 2683739207653738777992947)
      ·
        refine ⟨4025608811480608166989421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2683739207653738777992947 4025608811480608166989421)
        ·
          refine ⟨1509603304305228062621033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4025608811480608166989421 1509603304305228062621033)
          ·
            refine ⟨1132202478228921046965775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1509603304305228062621033 1132202478228921046965775)
            ·
              refine ⟨1698303717343381570448663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132202478228921046965775 1698303717343381570448663)
              ·
                refine ⟨2547455576015072355672995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698303717343381570448663 2547455576015072355672995)
                ·
                  refine ⟨3821183364022608533509493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547455576015072355672995 3821183364022608533509493)
                  ·
                    refine ⟨358235940377119550016515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3821183364022608533509493 358235940377119550016515)
                    ·
                      rfl

theorem cell22_1046493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1046493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046493 prefixEnd_1046493 := by exact prefixLift 1046493
  have htrace : WordTrace (prefixWord ++ tailWord_1046493) baseStart_1046493 baseEnd_1046493 := by
    simpa [prefixWord, tailWord_1046493, baseEnd_1046493] using wordTrace_append hprefix tailTrace_1046493
  have hstable : (prefixWord ++ tailWord_1046493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046493).length < 2 ^ (prefixWord ++ tailWord_1046493).sum := by decide
  have hdescent : baseEnd_1046493 < baseStart_1046493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046581 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1046581 : Nat := 118140960795 + 1046581 * 2 ^ 59
def prefixEnd_1046581 : Nat := 4983230072969 + 3 ^ 40 * 1046581 * 2
def baseEnd_1046581 : Nat := 358266064575516653816245

theorem tailTrace_1046581 : CollatzResearch.WordTrace tailWord_1046581 prefixEnd_1046581 358266064575516653816245 := by
  unfold tailWord_1046581
  simp only [CollatzResearch.WordTrace]
  refine ⟨38171945021423253649547597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25447963347615502433031731 38171945021423253649547597)
  ·
    refine ⟨14314479383033720118580349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38171945021423253649547597 14314479383033720118580349)
    ·
      refine ⟨5367929768637645044467631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14314479383033720118580349 5367929768637645044467631)
      ·
        refine ⟨8051894652956467566701447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5367929768637645044467631 8051894652956467566701447)
        ·
          refine ⟨12077841979434701350052171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051894652956467566701447 12077841979434701350052171)
          ·
            refine ⟨18116762969152052025078257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077841979434701350052171 18116762969152052025078257)
            ·
              refine ⟨13587572226864039018808693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18116762969152052025078257 13587572226864039018808693)
              ·
                refine ⟨1273834896268503658013315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13587572226864039018808693 1273834896268503658013315)
                ·
                  refine ⟨1910752344402755487019973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273834896268503658013315 1910752344402755487019973)
                  ·
                    refine ⟨358266064575516653816245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910752344402755487019973 358266064575516653816245)
                    ·
                      rfl

theorem cell22_1046581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1046581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046581 prefixEnd_1046581 := by exact prefixLift 1046581
  have htrace : WordTrace (prefixWord ++ tailWord_1046581) baseStart_1046581 baseEnd_1046581 := by
    simpa [prefixWord, tailWord_1046581, baseEnd_1046581] using wordTrace_append hprefix tailTrace_1046581
  have hstable : (prefixWord ++ tailWord_1046581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046581).length < 2 ^ (prefixWord ++ tailWord_1046581).sum := by decide
  have hdescent : baseEnd_1046581 < baseStart_1046581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046598 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1046598 : Nat := 118140960795 + 1046598 * 2 ^ 59
def prefixEnd_1046598 : Nat := 4983230072969 + 3 ^ 40 * 1046598 * 2
def baseEnd_1046598 : Nat := 358271884022934276141193

theorem tailTrace_1046598 : CollatzResearch.WordTrace tailWord_1046598 prefixEnd_1046598 358271884022934276141193 := by
  unfold tailWord_1046598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1192892658198802048528639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25448376708241110368610965 1192892658198802048528639)
  ·
    refine ⟨1789338987298203072792959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1192892658198802048528639 1789338987298203072792959)
    ·
      refine ⟨2684008480947304609189439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1789338987298203072792959 2684008480947304609189439)
      ·
        refine ⟨4026012721420956913784159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2684008480947304609189439 4026012721420956913784159)
        ·
          refine ⟨6039019082131435370676239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026012721420956913784159 6039019082131435370676239)
          ·
            refine ⟨9058528623197153056014359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6039019082131435370676239 9058528623197153056014359)
            ·
              refine ⟨13587792934795729584021539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9058528623197153056014359 13587792934795729584021539)
              ·
                refine ⟨20381689402193594376032309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13587792934795729584021539 20381689402193594376032309)
                ·
                  refine ⟨1910783381455649472753029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20381689402193594376032309 1910783381455649472753029)
                  ·
                    refine ⟨358271884022934276141193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910783381455649472753029 358271884022934276141193)
                    ·
                      rfl

theorem cell22_1046598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1046598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046598 prefixEnd_1046598 := by exact prefixLift 1046598
  have htrace : WordTrace (prefixWord ++ tailWord_1046598) baseStart_1046598 baseEnd_1046598 := by
    simpa [prefixWord, tailWord_1046598, baseEnd_1046598] using wordTrace_append hprefix tailTrace_1046598
  have hstable : (prefixWord ++ tailWord_1046598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046598).length < 2 ^ (prefixWord ++ tailWord_1046598).sum := by decide
  have hdescent : baseEnd_1046598 < baseStart_1046598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046609 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_1046609 : Nat := 118140960795 + 1046609 * 2 ^ 59
def prefixEnd_1046609 : Nat := 4983230072969 + 3 ^ 40 * 1046609 * 2
def baseEnd_1046609 : Nat := 358275649547733914116159

theorem tailTrace_1046609 : CollatzResearch.WordTrace tailWord_1046609 prefixEnd_1046609 358275649547733914116159 := by
  unfold tailWord_1046609
  simp only [CollatzResearch.WordTrace]
  refine ⟨38172966265321814431566881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25448644176881209621044587 38172966265321814431566881)
  ·
    refine ⟨28629724698991360823675161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38172966265321814431566881 28629724698991360823675161)
    ·
      refine ⟨21472293524243520617756371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28629724698991360823675161 21472293524243520617756371)
      ·
        refine ⟨32208440286365280926634557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21472293524243520617756371 32208440286365280926634557)
        ·
          refine ⟨12078165107386980347487959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32208440286365280926634557 12078165107386980347487959)
          ·
            refine ⟨18117247661080470521231939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12078165107386980347487959 18117247661080470521231939)
            ·
              refine ⟨27175871491620705781847909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18117247661080470521231939 27175871491620705781847909)
              ·
                refine ⟨5095475904678882334096483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27175871491620705781847909 5095475904678882334096483)
                ·
                  refine ⟨7643213857018323501144725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095475904678882334096483 7643213857018323501144725)
                  ·
                    refine ⟨358275649547733914116159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7643213857018323501144725 358275649547733914116159)
                    ·
                      rfl

theorem cell22_1046609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_1046609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046609 prefixEnd_1046609 := by exact prefixLift 1046609
  have htrace : WordTrace (prefixWord ++ tailWord_1046609) baseStart_1046609 baseEnd_1046609 := by
    simpa [prefixWord, tailWord_1046609, baseEnd_1046609] using wordTrace_append hprefix tailTrace_1046609
  have hstable : (prefixWord ++ tailWord_1046609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046609).length < 2 ^ (prefixWord ++ tailWord_1046609).sum := by decide
  have hdescent : baseEnd_1046609 < baseStart_1046609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046699 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 10]
def baseStart_1046699 : Nat := 118140960795 + 1046699 * 2 ^ 59
def prefixEnd_1046699 : Nat := 4983230072969 + 3 ^ 40 * 1046699 * 2
def baseEnd_1046699 : Nat := 358306458387003679365883

theorem tailTrace_1046699 : CollatzResearch.WordTrace tailWord_1046699 prefixEnd_1046699 358306458387003679365883 := by
  unfold tailWord_1046699
  simp only [CollatzResearch.WordTrace]
  refine ⟨38176248834995759802343151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25450832556663839868228767 38176248834995759802343151)
  ·
    refine ⟨57264373252493639703514727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38176248834995759802343151 57264373252493639703514727)
    ·
      refine ⟨85896559878740459555272091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57264373252493639703514727 85896559878740459555272091)
      ·
        refine ⟨128844839818110689332908137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85896559878740459555272091 128844839818110689332908137)
        ·
          refine ⟨96633629863583016999681103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128844839818110689332908137 96633629863583016999681103)
          ·
            refine ⟨144950444795374525499521655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96633629863583016999681103 144950444795374525499521655)
            ·
              refine ⟨217425667193061788249282483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144950444795374525499521655 217425667193061788249282483)
              ·
                refine ⟨326138500789592682373923725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217425667193061788249282483 326138500789592682373923725)
                ·
                  refine ⟨122301937796097255890221397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326138500789592682373923725 122301937796097255890221397)
                  ·
                    refine ⟨358306458387003679365883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 122301937796097255890221397 358306458387003679365883)
                    ·
                      rfl

theorem cell22_1046699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_1046699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046699 prefixEnd_1046699 := by exact prefixLift 1046699
  have htrace : WordTrace (prefixWord ++ tailWord_1046699) baseStart_1046699 baseEnd_1046699 := by
    simpa [prefixWord, tailWord_1046699, baseEnd_1046699] using wordTrace_append hprefix tailTrace_1046699
  have hstable : (prefixWord ++ tailWord_1046699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046699).length < 2 ^ (prefixWord ++ tailWord_1046699).sum := by decide
  have hdescent : baseEnd_1046699 < baseStart_1046699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046720 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 5]
def baseStart_1046720 : Nat := 118140960795 + 1046720 * 2 ^ 59
def prefixEnd_1046720 : Nat := 4983230072969 + 3 ^ 40 * 1046720 * 2
def baseEnd_1046720 : Nat := 119437882372055541530273

theorem tailTrace_1046720 : CollatzResearch.WordTrace tailWord_1046720 prefixEnd_1046720 119437882372055541530273 := by
  unfold tailWord_1046720
  simp only [CollatzResearch.WordTrace]
  refine ⟨19088507383959840194428807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25451343178613120259238409 19088507383959840194428807)
  ·
    refine ⟨28632761075939760291643211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19088507383959840194428807 28632761075939760291643211)
    ·
      refine ⟨42949141613909640437464817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28632761075939760291643211 42949141613909640437464817)
      ·
        refine ⟨32211856210432230328098613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42949141613909640437464817 32211856210432230328098613)
        ·
          refine ⟨3019861519728021593259245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32211856210432230328098613 3019861519728021593259245)
          ·
            refine ⟨1132448069898008097472217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3019861519728021593259245 1132448069898008097472217)
            ·
              refine ⟨849336052423506073104163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132448069898008097472217 849336052423506073104163)
              ·
                refine ⟨1274004078635259109656245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849336052423506073104163 1274004078635259109656245)
                ·
                  refine ⟨119437882372055541530273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1274004078635259109656245 119437882372055541530273)
                  ·
                    rfl

theorem cell22_1046720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 5].length) (baseStart_1046720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046720 prefixEnd_1046720 := by exact prefixLift 1046720
  have htrace : WordTrace (prefixWord ++ tailWord_1046720) baseStart_1046720 baseEnd_1046720 := by
    simpa [prefixWord, tailWord_1046720, baseEnd_1046720] using wordTrace_append hprefix tailTrace_1046720
  have hstable : (prefixWord ++ tailWord_1046720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046720).length < 2 ^ (prefixWord ++ tailWord_1046720).sum := by decide
  have hdescent : baseEnd_1046720 < baseStart_1046720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046746 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_1046746 : Nat := 118140960795 + 1046746 * 2 ^ 59
def prefixEnd_1046746 : Nat := 4983230072969 + 3 ^ 40 * 1046746 * 2
def baseEnd_1046746 : Nat := 358322547447511223440739

theorem tailTrace_1046746 : CollatzResearch.WordTrace tailWord_1046746 prefixEnd_1046746 358322547447511223440739 := by
  unfold tailWord_1046746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9544490766456371707326023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25451975377216991219536061 9544490766456371707326023)
  ·
    refine ⟨14316736149684557560989035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9544490766456371707326023 14316736149684557560989035)
    ·
      refine ⟨21475104224526836341483553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14316736149684557560989035 21475104224526836341483553)
      ·
        refine ⟨16106328168395127256112665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21475104224526836341483553 16106328168395127256112665)
        ·
          refine ⟨12079746126296345442084499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16106328168395127256112665 12079746126296345442084499)
          ·
            refine ⟨18119619189444518163126749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12079746126296345442084499 18119619189444518163126749)
            ·
              refine ⟨6794857196041694311172531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18119619189444518163126749 6794857196041694311172531)
              ·
                refine ⟨10192285794062541466758797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794857196041694311172531 10192285794062541466758797)
                ·
                  refine ⟨3822107172773453050034549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10192285794062541466758797 3822107172773453050034549)
                  ·
                    refine ⟨358322547447511223440739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3822107172773453050034549 358322547447511223440739)
                    ·
                      rfl

theorem cell22_1046746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_1046746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046746 prefixEnd_1046746 := by exact prefixLift 1046746
  have htrace : WordTrace (prefixWord ++ tailWord_1046746) baseStart_1046746 baseEnd_1046746 := by
    simpa [prefixWord, tailWord_1046746, baseEnd_1046746] using wordTrace_append hprefix tailTrace_1046746
  have hstable : (prefixWord ++ tailWord_1046746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046746).length < 2 ^ (prefixWord ++ tailWord_1046746).sum := by decide
  have hdescent : baseEnd_1046746 < baseStart_1046746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046754 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_1046754 : Nat := 118140960795 + 1046754 * 2 ^ 59
def prefixEnd_1046754 : Nat := 4983230072969 + 3 ^ 40 * 1046754 * 2
def baseEnd_1046754 : Nat := 119441762003667289746905

theorem tailTrace_1046754 : CollatzResearch.WordTrace tailWord_1046754 prefixEnd_1046754 119441762003667289746905 := by
  unfold tailWord_1046754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9544563712449126048898829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25452169899864336130396877 9544563712449126048898829)
  ·
    refine ⟨3579211392168422268337061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9544563712449126048898829 3579211392168422268337061)
    ·
      refine ⟨671102136031579175313199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3579211392168422268337061 671102136031579175313199)
      ·
        refine ⟨1006653204047368762969799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671102136031579175313199 1006653204047368762969799)
        ·
          refine ⟨1509979806071053144454699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006653204047368762969799 1509979806071053144454699)
          ·
            refine ⟨2264969709106579716682049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509979806071053144454699 2264969709106579716682049)
            ·
              refine ⟨1698727281829934787511537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2264969709106579716682049 1698727281829934787511537)
              ·
                refine ⟨1274045461372451090633653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698727281829934787511537 1274045461372451090633653)
                ·
                  refine ⟨119441762003667289746905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1274045461372451090633653 119441762003667289746905)
                  ·
                    rfl

theorem cell22_1046754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_1046754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046754 prefixEnd_1046754 := by exact prefixLift 1046754
  have htrace : WordTrace (prefixWord ++ tailWord_1046754) baseStart_1046754 baseEnd_1046754 := by
    simpa [prefixWord, tailWord_1046754, baseEnd_1046754] using wordTrace_append hprefix tailTrace_1046754
  have hstable : (prefixWord ++ tailWord_1046754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046754).length < 2 ^ (prefixWord ++ tailWord_1046754).sum := by decide
  have hdescent : baseEnd_1046754 < baseStart_1046754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046780 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_1046780 : Nat := 118140960795 + 1046780 * 2 ^ 59
def prefixEnd_1046780 : Nat := 4983230072969 + 3 ^ 40 * 1046780 * 2
def baseEnd_1046780 : Nat := 358334186342346468090635

theorem tailTrace_1046780 : CollatzResearch.WordTrace tailWord_1046780 prefixEnd_1046780 358334186342346468090635 := by
  unfold tailWord_1046780
  simp only [CollatzResearch.WordTrace]
  refine ⟨19089601573851155318020897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25452802098468207090694529 19089601573851155318020897)
  ·
    refine ⟨14317201180388366488515673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19089601573851155318020897 14317201180388366488515673)
    ·
      refine ⟨10737900885291274866386755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14317201180388366488515673 10737900885291274866386755)
      ·
        refine ⟨16106851327936912299580133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10737900885291274866386755 16106851327936912299580133)
        ·
          refine ⟨3020034623988171056171275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16106851327936912299580133 3020034623988171056171275)
          ·
            refine ⟨4530051935982256584256913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020034623988171056171275 4530051935982256584256913)
            ·
              refine ⟨3397538951986692438192685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4530051935982256584256913 3397538951986692438192685)
              ·
                refine ⟨1274077106995009664322257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3397538951986692438192685 1274077106995009664322257)
                ·
                  refine ⟨955557830246257248241693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1274077106995009664322257 955557830246257248241693)
                  ·
                    refine ⟨358334186342346468090635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955557830246257248241693 358334186342346468090635)
                    ·
                      rfl

theorem cell22_1046780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_1046780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046780 prefixEnd_1046780 := by exact prefixLift 1046780
  have htrace : WordTrace (prefixWord ++ tailWord_1046780) baseStart_1046780 baseEnd_1046780 := by
    simpa [prefixWord, tailWord_1046780, baseEnd_1046780] using wordTrace_append hprefix tailTrace_1046780
  have hstable : (prefixWord ++ tailWord_1046780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046780).length < 2 ^ (prefixWord ++ tailWord_1046780).sum := by decide
  have hdescent : baseEnd_1046780 < baseStart_1046780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046793 : List Nat := [1, 2, 1, 1, 3, 5, 3, 6]
def baseStart_1046793 : Nat := 118140960795 + 1046793 * 2 ^ 59
def prefixEnd_1046793 : Nat := 4983230072969 + 3 ^ 40 * 1046793 * 2
def baseEnd_1046793 : Nat := 39815404056446529723955

theorem tailTrace_1046793 : CollatzResearch.WordTrace tailWord_1046793 prefixEnd_1046793 39815404056446529723955 := by
  unfold tailWord_1046793
  simp only [CollatzResearch.WordTrace]
  refine ⟨38179677296655213856265033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25453118197770142570843355 38179677296655213856265033)
  ·
    refine ⟨28634757972491410392198775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38179677296655213856265033 28634757972491410392198775)
    ·
      refine ⟨42952136958737115588298163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28634757972491410392198775 42952136958737115588298163)
      ·
        refine ⟨64428205438105673382447245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42952136958737115588298163 64428205438105673382447245)
        ·
          refine ⟨24160577039289627518417717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64428205438105673382447245 24160577039289627518417717)
          ·
            refine ⟨2265054097433402579851661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24160577039289627518417717 2265054097433402579851661)
            ·
              refine ⟨849395286537525967444373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2265054097433402579851661 849395286537525967444373)
              ·
                refine ⟨39815404056446529723955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 849395286537525967444373 39815404056446529723955)
                ·
                  rfl

theorem cell22_1046793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 6].length) (baseStart_1046793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046793 prefixEnd_1046793 := by exact prefixLift 1046793
  have htrace : WordTrace (prefixWord ++ tailWord_1046793) baseStart_1046793 baseEnd_1046793 := by
    simpa [prefixWord, tailWord_1046793, baseEnd_1046793] using wordTrace_append hprefix tailTrace_1046793
  have hstable : (prefixWord ++ tailWord_1046793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046793).length < 2 ^ (prefixWord ++ tailWord_1046793).sum := by decide
  have hdescent : baseEnd_1046793 < baseStart_1046793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046808 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 5, 3]
def baseStart_1046808 : Nat := 118140960795 + 1046808 * 2 ^ 59
def prefixEnd_1046808 : Nat := 4983230072969 + 3 ^ 40 * 1046808 * 2
def baseEnd_1046808 : Nat := 358343771314563728390549

theorem tailTrace_1046808 : CollatzResearch.WordTrace tailWord_1046808 prefixEnd_1046808 358343771314563728390549 := by
  unfold tailWord_1046808
  simp only [CollatzResearch.WordTrace]
  refine ⟨19090112195800435709030539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25453482927733914278707385 19090112195800435709030539)
  ·
    refine ⟨28635168293700653563545809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19090112195800435709030539 28635168293700653563545809)
    ·
      refine ⟨21476376220275490172659357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28635168293700653563545809 21476376220275490172659357)
      ·
        refine ⟨8053641082603308814747259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21476376220275490172659357 8053641082603308814747259)
        ·
          refine ⟨12080461623904963222120889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053641082603308814747259 12080461623904963222120889)
          ·
            refine ⟨9060346217928722416590667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12080461623904963222120889 9060346217928722416590667)
            ·
              refine ⟨13590519326893083624886001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9060346217928722416590667 13590519326893083624886001)
              ·
                refine ⟨10192889495169812718664501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13590519326893083624886001 10192889495169812718664501)
                ·
                  refine ⟨955583390172169942374797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10192889495169812718664501 955583390172169942374797)
                  ·
                    refine ⟨358343771314563728390549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955583390172169942374797 358343771314563728390549)
                    ·
                      rfl

theorem cell22_1046808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_1046808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046808 prefixEnd_1046808 := by exact prefixLift 1046808
  have htrace : WordTrace (prefixWord ++ tailWord_1046808) baseStart_1046808 baseEnd_1046808 := by
    simpa [prefixWord, tailWord_1046808, baseEnd_1046808] using wordTrace_append hprefix tailTrace_1046808
  have hstable : (prefixWord ++ tailWord_1046808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046808).length < 2 ^ (prefixWord ++ tailWord_1046808).sum := by decide
  have hdescent : baseEnd_1046808 < baseStart_1046808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046814 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1046814 : Nat := 118140960795 + 1046814 * 2 ^ 59
def prefixEnd_1046814 : Nat := 4983230072969 + 3 ^ 40 * 1046814 * 2
def baseEnd_1046814 : Nat := 358345825237181712740531

theorem tailTrace_1046814 : CollatzResearch.WordTrace tailWord_1046814 prefixEnd_1046814 358345825237181712740531 := by
  unfold tailWord_1046814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4772555403697391805347437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25453628819719422961852997 4772555403697391805347437)
  ·
    refine ⟨1789708276386521927005289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4772555403697391805347437 1789708276386521927005289)
    ·
      refine ⟨1342281207289891445253967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1789708276386521927005289 1342281207289891445253967)
      ·
        refine ⟨2013421810934837167880951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342281207289891445253967 2013421810934837167880951)
        ·
          refine ⟨3020132716402255751821427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013421810934837167880951 3020132716402255751821427)
          ·
            refine ⟨4530199074603383627732141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020132716402255751821427 4530199074603383627732141)
            ·
              refine ⟨1698824652976268860399553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4530199074603383627732141 1698824652976268860399553)
              ·
                refine ⟨1274118489732201645299665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698824652976268860399553 1274118489732201645299665)
                ·
                  refine ⟨955588867299151233974749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1274118489732201645299665 955588867299151233974749)
                  ·
                    refine ⟨358345825237181712740531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955588867299151233974749 358345825237181712740531)
                    ·
                      rfl

theorem cell22_1046814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1046814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046814 prefixEnd_1046814 := by exact prefixLift 1046814
  have htrace : WordTrace (prefixWord ++ tailWord_1046814) baseStart_1046814 baseEnd_1046814 := by
    simpa [prefixWord, tailWord_1046814, baseEnd_1046814] using wordTrace_append hprefix tailTrace_1046814
  have hstable : (prefixWord ++ tailWord_1046814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046814).length < 2 ^ (prefixWord ++ tailWord_1046814).sum := by decide
  have hdescent : baseEnd_1046814 < baseStart_1046814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046876 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1046876 : Nat := 118140960795 + 1046876 * 2 ^ 59
def prefixEnd_1046876 : Nat := 4983230072969 + 3 ^ 40 * 1046876 * 2
def baseEnd_1046876 : Nat := 358367049104234217690341

theorem tailTrace_1046876 : CollatzResearch.WordTrace tailWord_1046876 prefixEnd_1046876 358367049104234217690341 := by
  unfold tailWord_1046876
  simp only [CollatzResearch.WordTrace]
  refine ⟨19091352277677259515768241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25455136370236346021024321 19091352277677259515768241)
  ·
    refine ⟨14318514208257944636826181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19091352277677259515768241 14318514208257944636826181)
    ·
      refine ⟨2684721414048364619404909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14318514208257944636826181 2684721414048364619404909)
      ·
        refine ⟨1006770530268136732276841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2684721414048364619404909 1006770530268136732276841)
        ·
          refine ⟨755077897701102549207631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006770530268136732276841 755077897701102549207631)
          ·
            refine ⟨1132616846551653823811447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755077897701102549207631 1132616846551653823811447)
            ·
              refine ⟨1698925269827480735717171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132616846551653823811447 1698925269827480735717171)
              ·
                refine ⟨2548387904741221103575757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698925269827480735717171 2548387904741221103575757)
                ·
                  refine ⟨955645464277957913840909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2548387904741221103575757 955645464277957913840909)
                  ·
                    refine ⟨358367049104234217690341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955645464277957913840909 358367049104234217690341)
                    ·
                      rfl

theorem cell22_1046876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1046876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046876 prefixEnd_1046876 := by exact prefixLift 1046876
  have htrace : WordTrace (prefixWord ++ tailWord_1046876) baseStart_1046876 baseEnd_1046876 := by
    simpa [prefixWord, tailWord_1046876, baseEnd_1046876] using wordTrace_append hprefix tailTrace_1046876
  have hstable : (prefixWord ++ tailWord_1046876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046876).length < 2 ^ (prefixWord ++ tailWord_1046876).sum := by decide
  have hdescent : baseEnd_1046876 < baseStart_1046876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046915 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 1, 5]
def baseStart_1046915 : Nat := 118140960795 + 1046915 * 2 ^ 59
def prefixEnd_1046915 : Nat := 4983230072969 + 3 ^ 40 * 1046915 * 2
def baseEnd_1046915 : Nat := 358380399601251115965221

theorem tailTrace_1046915 : CollatzResearch.WordTrace tailWord_1046915 prefixEnd_1046915 358380399601251115965221 := by
  unfold tailWord_1046915
  simp only [CollatzResearch.WordTrace]
  refine ⟨38184127002213228692206199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25456084668142152461470799 38184127002213228692206199)
  ·
    refine ⟨57276190503319843038309299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38184127002213228692206199 57276190503319843038309299)
    ·
      refine ⟨85914285754979764557463949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57276190503319843038309299 85914285754979764557463949)
      ·
        refine ⟨32217857158117411709048981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85914285754979764557463949 32217857158117411709048981)
        ·
          refine ⟨1510212054286753673861671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32217857158117411709048981 1510212054286753673861671)
          ·
            refine ⟨2265318081430130510792507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510212054286753673861671 2265318081430130510792507)
            ·
              refine ⟨3397977122145195766188761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265318081430130510792507 3397977122145195766188761)
              ·
                refine ⟨2548482841608896824641571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3397977122145195766188761 2548482841608896824641571)
                ·
                  refine ⟨3822724262413345236962357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548482841608896824641571 3822724262413345236962357)
                  ·
                    refine ⟨358380399601251115965221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3822724262413345236962357 358380399601251115965221)
                    ·
                      rfl

theorem cell22_1046915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 5].length) (baseStart_1046915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046915 prefixEnd_1046915 := by exact prefixLift 1046915
  have htrace : WordTrace (prefixWord ++ tailWord_1046915) baseStart_1046915 baseEnd_1046915 := by
    simpa [prefixWord, tailWord_1046915, baseEnd_1046915] using wordTrace_append hprefix tailTrace_1046915
  have hstable : (prefixWord ++ tailWord_1046915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046915).length < 2 ^ (prefixWord ++ tailWord_1046915).sum := by decide
  have hdescent : baseEnd_1046915 < baseStart_1046915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046964 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1046964 : Nat := 118140960795 + 1046964 * 2 ^ 59
def prefixEnd_1046964 : Nat := 4983230072969 + 3 ^ 40 * 1046964 * 2
def baseEnd_1046964 : Nat := 358397173302631321490071

theorem tailTrace_1046964 : CollatzResearch.WordTrace tailWord_1046964 prefixEnd_1046964 358397173302631321490071 := by
  unfold tailWord_1046964
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092957089517855030369973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25457276119357140040493297 19092957089517855030369973)
  ·
    refine ⟨1789964727142298909097185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19092957089517855030369973 1789964727142298909097185)
    ·
      refine ⟨1342473545356724181822889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1789964727142298909097185 1342473545356724181822889)
      ·
        refine ⟨1006855159017543136367167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1342473545356724181822889 1006855159017543136367167)
        ·
          refine ⟨1510282738526314704550751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006855159017543136367167 1510282738526314704550751)
          ·
            refine ⟨2265424107789472056826127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510282738526314704550751 2265424107789472056826127)
            ·
              refine ⟨3398136161684208085239191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265424107789472056826127 3398136161684208085239191)
              ·
                refine ⟨5097204242526312127858787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398136161684208085239191 5097204242526312127858787)
                ·
                  refine ⟨7645806363789468191788181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097204242526312127858787 7645806363789468191788181)
                  ·
                    refine ⟨358397173302631321490071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7645806363789468191788181 358397173302631321490071)
                    ·
                      rfl

theorem cell22_1046964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1046964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1046964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1046964 prefixEnd_1046964 := by exact prefixLift 1046964
  have htrace : WordTrace (prefixWord ++ tailWord_1046964) baseStart_1046964 baseEnd_1046964 := by
    simpa [prefixWord, tailWord_1046964, baseEnd_1046964] using wordTrace_append hprefix tailTrace_1046964
  have hstable : (prefixWord ++ tailWord_1046964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046964).length < 2 ^ (prefixWord ++ tailWord_1046964).sum := by decide
  have hdescent : baseEnd_1046964 < baseStart_1046964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047005 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1047005 : Nat := 118140960795 + 1047005 * 2 ^ 59
def prefixEnd_1047005 : Nat := 4983230072969 + 3 ^ 40 * 1047005 * 2
def baseEnd_1047005 : Nat := 358411208440520881214945

theorem tailTrace_1047005 : CollatzResearch.WordTrace tailWord_1047005 prefixEnd_1047005 358411208440520881214945 := by
  unfold tailWord_1047005
  simp only [CollatzResearch.WordTrace]
  refine ⟨38187409571887174062982469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25458273047924782708654979 38187409571887174062982469)
  ·
    refine ⟨7160139294728845136809213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38187409571887174062982469 7160139294728845136809213)
    ·
      refine ⟨2685052235523316926303455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7160139294728845136809213 2685052235523316926303455)
      ·
        refine ⟨4027578353284975389455183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685052235523316926303455 4027578353284975389455183)
        ·
          refine ⟨6041367529927463084182775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027578353284975389455183 6041367529927463084182775)
          ·
            refine ⟨9062051294891194626274163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041367529927463084182775 9062051294891194626274163)
            ·
              refine ⟨13593076942336791939411245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062051294891194626274163 13593076942336791939411245)
              ·
                refine ⟨5097403853376296977279217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13593076942336791939411245 5097403853376296977279217)
                ·
                  refine ⟨3823052890032222732959413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5097403853376296977279217 3823052890032222732959413)
                  ·
                    refine ⟨358411208440520881214945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3823052890032222732959413 358411208440520881214945)
                    ·
                      rfl

theorem cell22_1047005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1047005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047005 prefixEnd_1047005 := by exact prefixLift 1047005
  have htrace : WordTrace (prefixWord ++ tailWord_1047005) baseStart_1047005 baseEnd_1047005 := by
    simpa [prefixWord, tailWord_1047005, baseEnd_1047005] using wordTrace_append hprefix tailTrace_1047005
  have hstable : (prefixWord ++ tailWord_1047005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047005).length < 2 ^ (prefixWord ++ tailWord_1047005).sum := by decide
  have hdescent : baseEnd_1047005 < baseStart_1047005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047007 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 5]
def baseStart_1047007 : Nat := 118140960795 + 1047007 * 2 ^ 59
def prefixEnd_1047007 : Nat := 4983230072969 + 3 ^ 40 * 1047007 * 2
def baseEnd_1047007 : Nat := 119470631027131180888313

theorem tailTrace_1047007 : CollatzResearch.WordTrace tailWord_1047007 prefixEnd_1047007 119470631027131180888313 := by
  unfold tailWord_1047007
  simp only [CollatzResearch.WordTrace]
  refine ⟨38187482517879928404555275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25458321678586618936370183 38187482517879928404555275)
  ·
    refine ⟨57281223776819892606832913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38187482517879928404555275 57281223776819892606832913)
    ·
      refine ⟨42960917832614919455124685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57281223776819892606832913 42960917832614919455124685)
      ·
        refine ⟨16110344187230594795671757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42960917832614919455124685 16110344187230594795671757)
        ·
          refine ⟨6041379070211473048376909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16110344187230594795671757 6041379070211473048376909)
          ·
            refine ⟨2265517151329302393141341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6041379070211473048376909 2265517151329302393141341)
            ·
              refine ⟨849568931748488397428003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2265517151329302393141341 849568931748488397428003)
              ·
                refine ⟨1274353397622732596142005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849568931748488397428003 1274353397622732596142005)
                ·
                  refine ⟨119470631027131180888313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1274353397622732596142005 119470631027131180888313)
                  ·
                    rfl

theorem cell22_1047007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 5].length) (baseStart_1047007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047007 prefixEnd_1047007 := by exact prefixLift 1047007
  have htrace : WordTrace (prefixWord ++ tailWord_1047007) baseStart_1047007 baseEnd_1047007 := by
    simpa [prefixWord, tailWord_1047007, baseEnd_1047007] using wordTrace_append hprefix tailTrace_1047007
  have hstable : (prefixWord ++ tailWord_1047007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047007).length < 2 ^ (prefixWord ++ tailWord_1047007).sum := by decide
  have hdescent : baseEnd_1047007 < baseStart_1047007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047052 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 6]
def baseStart_1047052 : Nat := 118140960795 + 1047052 * 2 ^ 59
def prefixEnd_1047052 : Nat := 4983230072969 + 3 ^ 40 * 1047052 * 2
def baseEnd_1047052 : Nat := 119475765833676141763267

theorem tailTrace_1047052 : CollatzResearch.WordTrace tailWord_1047052 prefixEnd_1047052 119475765833676141763267 := by
  unfold tailWord_1047052
  simp only [CollatzResearch.WordTrace]
  refine ⟨19094561901358450544971705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25459415868477934059962273 19094561901358450544971705)
  ·
    refine ⟨14320921426018837908728779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19094561901358450544971705 14320921426018837908728779)
    ·
      refine ⟨21481382139028256863093169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14320921426018837908728779 21481382139028256863093169)
      ·
        refine ⟨16111036604271192647319877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21481382139028256863093169 16111036604271192647319877)
        ·
          refine ⟨3020819363300848621372477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16111036604271192647319877 3020819363300848621372477)
          ·
            refine ⟨1132807261237818233014679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3020819363300848621372477 1132807261237818233014679)
            ·
              refine ⟨1699210891856727349522019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132807261237818233014679 1699210891856727349522019)
              ·
                refine ⟨2548816337785091024283029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699210891856727349522019 2548816337785091024283029)
                ·
                  refine ⟨119475765833676141763267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2548816337785091024283029 119475765833676141763267)
                  ·
                    rfl

theorem cell22_1047052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_1047052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047052 prefixEnd_1047052 := by exact prefixLift 1047052
  have htrace : WordTrace (prefixWord ++ tailWord_1047052) baseStart_1047052 baseEnd_1047052 := by
    simpa [prefixWord, tailWord_1047052, baseEnd_1047052] using wordTrace_append hprefix tailTrace_1047052
  have hstable : (prefixWord ++ tailWord_1047052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047052).length < 2 ^ (prefixWord ++ tailWord_1047052).sum := by decide
  have hdescent : baseEnd_1047052 < baseStart_1047052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047082 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1047082 : Nat := 118140960795 + 1047082 * 2 ^ 59
def prefixEnd_1047082 : Nat := 4983230072969 + 3 ^ 40 * 1047082 * 2
def baseEnd_1047082 : Nat := 358437567114118347039709

theorem tailTrace_1047082 : CollatzResearch.WordTrace tailWord_1047082 prefixEnd_1047082 358437567114118347039709 := by
  unfold tailWord_1047082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9547554498152054053383875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25460145328405477475690333 9547554498152054053383875)
  ·
    refine ⟨14321331747228081080075813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9547554498152054053383875 14321331747228081080075813)
    ·
      refine ⟨2685249702605265202514215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14321331747228081080075813 2685249702605265202514215)
      ·
        refine ⟨4027874553907897803771323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685249702605265202514215 4027874553907897803771323)
        ·
          refine ⟨6041811830861846705656985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027874553907897803771323 6041811830861846705656985)
          ·
            refine ⟨4531358873146385029242739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6041811830861846705656985 4531358873146385029242739)
            ·
              refine ⟨6797038309719577543864109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4531358873146385029242739 6797038309719577543864109)
              ·
                refine ⟨2548889366144841578949041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6797038309719577543864109 2548889366144841578949041)
                ·
                  refine ⟨1911667024608631184211781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2548889366144841578949041 1911667024608631184211781)
                  ·
                    refine ⟨358437567114118347039709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1911667024608631184211781 358437567114118347039709)
                    ·
                      rfl

theorem cell22_1047082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1047082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047082 prefixEnd_1047082 := by exact prefixLift 1047082
  have htrace : WordTrace (prefixWord ++ tailWord_1047082) baseStart_1047082 baseEnd_1047082 := by
    simpa [prefixWord, tailWord_1047082, baseEnd_1047082] using wordTrace_append hprefix tailTrace_1047082
  have hstable : (prefixWord ++ tailWord_1047082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047082).length < 2 ^ (prefixWord ++ tailWord_1047082).sum := by decide
  have hdescent : baseEnd_1047082 < baseStart_1047082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047140 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1047140 : Nat := 118140960795 + 1047140 * 2 ^ 59
def prefixEnd_1047140 : Nat := 4983230072969 + 3 ^ 40 * 1047140 * 2
def baseEnd_1047140 : Nat := 358457421699425529089531

theorem tailTrace_1047140 : CollatzResearch.WordTrace tailWord_1047140 prefixEnd_1047140 358457421699425529089531 := by
  unfold tailWord_1047140
  simp only [CollatzResearch.WordTrace]
  refine ⟨19096166713199046059573437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25461555617598728079431249 19096166713199046059573437)
  ·
    refine ⟨7161062517449642272340039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19096166713199046059573437 7161062517449642272340039)
    ·
      refine ⟨10741593776174463408510059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7161062517449642272340039 10741593776174463408510059)
      ·
        refine ⟨16112390664261695112765089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10741593776174463408510059 16112390664261695112765089)
        ·
          refine ⟨12084292998196271334573817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16112390664261695112765089 12084292998196271334573817)
          ·
            refine ⟨9063219748647203500930363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12084292998196271334573817 9063219748647203500930363)
            ·
              refine ⟨13594829622970805251395545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9063219748647203500930363 13594829622970805251395545)
              ·
                refine ⟨10196122217228103938546659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13594829622970805251395545 10196122217228103938546659)
                ·
                  refine ⟨15294183325842155907819989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10196122217228103938546659 15294183325842155907819989)
                  ·
                    refine ⟨358457421699425529089531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15294183325842155907819989 358457421699425529089531)
                    ·
                      rfl

theorem cell22_1047140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1047140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047140 prefixEnd_1047140 := by exact prefixLift 1047140
  have htrace : WordTrace (prefixWord ++ tailWord_1047140) baseStart_1047140 baseEnd_1047140 := by
    simpa [prefixWord, tailWord_1047140, baseEnd_1047140] using wordTrace_append hprefix tailTrace_1047140
  have hstable : (prefixWord ++ tailWord_1047140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047140).length < 2 ^ (prefixWord ++ tailWord_1047140).sum := by decide
  have hdescent : baseEnd_1047140 < baseStart_1047140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047146 : List Nat := [3, 1, 3, 2, 1, 1, 4, 3, 1, 3]
def baseStart_1047146 : Nat := 118140960795 + 1047146 * 2 ^ 59
def prefixEnd_1047146 : Nat := 4983230072969 + 3 ^ 40 * 1047146 * 2
def baseEnd_1047146 : Nat := 358459475622043513439513

theorem tailTrace_1047146 : CollatzResearch.WordTrace tailWord_1047146 prefixEnd_1047146 358459475622043513439513 := by
  unfold tailWord_1047146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9548138066094088785966323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25461701509584236762576861 9548138066094088785966323)
  ·
    refine ⟨14322207099141133178949485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9548138066094088785966323 14322207099141133178949485)
    ·
      refine ⟨5370827662177924942106057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14322207099141133178949485 5370827662177924942106057)
      ·
        refine ⟨4028120746633443706579543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5370827662177924942106057 4028120746633443706579543)
        ·
          refine ⟨6042181119950165559869315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028120746633443706579543 6042181119950165559869315)
          ·
            refine ⟨9063271679925248339803973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042181119950165559869315 9063271679925248339803973)
            ·
              refine ⟨1699363439985984063713245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9063271679925248339803973 1699363439985984063713245)
              ·
                refine ⟨637261289994744023892467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1699363439985984063713245 637261289994744023892467)
                ·
                  refine ⟨955891934992116035838701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637261289994744023892467 955891934992116035838701)
                  ·
                    refine ⟨358459475622043513439513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955891934992116035838701 358459475622043513439513)
                    ·
                      rfl

theorem cell22_1047146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_1047146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047146 prefixEnd_1047146 := by exact prefixLift 1047146
  have htrace : WordTrace (prefixWord ++ tailWord_1047146) baseStart_1047146 baseEnd_1047146 := by
    simpa [prefixWord, tailWord_1047146, baseEnd_1047146] using wordTrace_append hprefix tailTrace_1047146
  have hstable : (prefixWord ++ tailWord_1047146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047146).length < 2 ^ (prefixWord ++ tailWord_1047146).sum := by decide
  have hdescent : baseEnd_1047146 < baseStart_1047146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047155 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 5, 4]
def baseStart_1047155 : Nat := 118140960795 + 1047155 * 2 ^ 59
def prefixEnd_1047155 : Nat := 4983230072969 + 3 ^ 40 * 1047155 * 2
def baseEnd_1047155 : Nat := 358462556505970489964485

theorem tailTrace_1047155 : CollatzResearch.WordTrace tailWord_1047155 prefixEnd_1047155 358462556505970489964485 := by
  unfold tailWord_1047155
  simp only [CollatzResearch.WordTrace]
  refine ⟨38192880521343749680942919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25461920347562499787295279 38192880521343749680942919)
  ·
    refine ⟨57289320782015624521414379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38192880521343749680942919 57289320782015624521414379)
    ·
      refine ⟨85933981173023436782121569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57289320782015624521414379 85933981173023436782121569)
      ·
        refine ⟨64450485879767577586591177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85933981173023436782121569 64450485879767577586591177)
        ·
          refine ⟨48337864409825683189943383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64450485879767577586591177 48337864409825683189943383)
          ·
            refine ⟨72506796614738524784915075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48337864409825683189943383 72506796614738524784915075)
            ·
              refine ⟨108760194922107787177372613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72506796614738524784915075 108760194922107787177372613)
              ·
                refine ⟨20392536547895210095757365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108760194922107787177372613 20392536547895210095757365)
                ·
                  refine ⟨1911800301365175946477253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20392536547895210095757365 1911800301365175946477253)
                  ·
                    refine ⟨358462556505970489964485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1911800301365175946477253 358462556505970489964485)
                    ·
                      rfl

theorem cell22_1047155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 4].length) (baseStart_1047155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047155 prefixEnd_1047155 := by exact prefixLift 1047155
  have htrace : WordTrace (prefixWord ++ tailWord_1047155) baseStart_1047155 baseEnd_1047155 := by
    simpa [prefixWord, tailWord_1047155, baseEnd_1047155] using wordTrace_append hprefix tailTrace_1047155
  have hstable : (prefixWord ++ tailWord_1047155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047155).length < 2 ^ (prefixWord ++ tailWord_1047155).sum := by decide
  have hdescent : baseEnd_1047155 < baseStart_1047155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047215 : List Nat := [1, 1, 2, 1, 2, 5, 10]
def baseStart_1047215 : Nat := 118140960795 + 1047215 * 2 ^ 59
def prefixEnd_1047215 : Nat := 4983230072969 + 3 ^ 40 * 1047215 * 2
def baseEnd_1047215 : Nat := 13277151693783345683863

theorem tailTrace_1047215 : CollatzResearch.WordTrace tailWord_1047215 prefixEnd_1047215 13277151693783345683863 := by
  unfold tailWord_1047215
  simp only [CollatzResearch.WordTrace]
  refine ⟨38195068901126379928127099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25463379267417586618751399 38195068901126379928127099)
  ·
    refine ⟨57292603351689569892190649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38195068901126379928127099 57292603351689569892190649)
    ·
      refine ⟨42969452513767177419142987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57292603351689569892190649 42969452513767177419142987)
      ·
        refine ⟨64454178770650766128714481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42969452513767177419142987 64454178770650766128714481)
        ·
          refine ⟨48340634077988074596535861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64454178770650766128714481 48340634077988074596535861)
          ·
            refine ⟨4531934444811381993425237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48340634077988074596535861 4531934444811381993425237)
            ·
              refine ⟨13277151693783345683863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4531934444811381993425237 13277151693783345683863)
              ·
                rfl

theorem cell22_1047215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 10].length) (baseStart_1047215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047215 prefixEnd_1047215 := by exact prefixLift 1047215
  have htrace : WordTrace (prefixWord ++ tailWord_1047215) baseStart_1047215 baseEnd_1047215 := by
    simpa [prefixWord, tailWord_1047215, baseEnd_1047215] using wordTrace_append hprefix tailTrace_1047215
  have hstable : (prefixWord ++ tailWord_1047215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047215).length < 2 ^ (prefixWord ++ tailWord_1047215).sum := by decide
  have hdescent : baseEnd_1047215 < baseStart_1047215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047232 : List Nat := [2, 1, 1, 2, 4, 3, 2, 7]
def baseStart_1047232 : Nat := 118140960795 + 1047232 * 2 ^ 59
def prefixEnd_1047232 : Nat := 4983230072969 + 3 ^ 40 * 1047232 * 2
def baseEnd_1047232 : Nat := 39832101686618661754361

theorem tailTrace_1047232 : CollatzResearch.WordTrace tailWord_1047232 prefixEnd_1047232 39832101686618661754361 := by
  unfold tailWord_1047232
  simp only [CollatzResearch.WordTrace]
  refine ⟨19097844471032395915747975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25463792628043194554330633 19097844471032395915747975)
  ·
    refine ⟨28646766706548593873621963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19097844471032395915747975 28646766706548593873621963)
    ·
      refine ⟨42970150059822890810432945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28646766706548593873621963 42970150059822890810432945)
      ·
        refine ⟨32227612544867168107824709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42970150059822890810432945 32227612544867168107824709)
        ·
          refine ⟨6042677352162594020217133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32227612544867168107824709 6042677352162594020217133)
          ·
            refine ⟨2266004007060972757581425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6042677352162594020217133 2266004007060972757581425)
            ·
              refine ⟨1699503005295729568186069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2266004007060972757581425 1699503005295729568186069)
              ·
                refine ⟨39832101686618661754361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1699503005295729568186069 39832101686618661754361)
                ·
                  rfl

theorem cell22_1047232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 7].length) (baseStart_1047232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047232 prefixEnd_1047232 := by exact prefixLift 1047232
  have htrace : WordTrace (prefixWord ++ tailWord_1047232) baseStart_1047232 baseEnd_1047232 := by
    simpa [prefixWord, tailWord_1047232, baseEnd_1047232] using wordTrace_append hprefix tailTrace_1047232
  have hstable : (prefixWord ++ tailWord_1047232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047232).length < 2 ^ (prefixWord ++ tailWord_1047232).sum := by decide
  have hdescent : baseEnd_1047232 < baseStart_1047232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047236 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1047236 : Nat := 118140960795 + 1047236 * 2 ^ 59
def prefixEnd_1047236 : Nat := 4983230072969 + 3 ^ 40 * 1047236 * 2
def baseEnd_1047236 : Nat := 358490284461313278689237

theorem tailTrace_1047236 : CollatzResearch.WordTrace tailWord_1047236 prefixEnd_1047236 358490284461313278689237 := by
  unfold tailWord_1047236
  simp only [CollatzResearch.WordTrace]
  refine ⟨19097917417025150257320781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25463889889366867009761041 19097917417025150257320781)
  ·
    refine ⟨7161719031384431346495293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19097917417025150257320781 7161719031384431346495293)
    ·
      refine ⟨2685644636769161754935735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7161719031384431346495293 2685644636769161754935735)
      ·
        refine ⟨4028466955153742632403603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685644636769161754935735 4028466955153742632403603)
        ·
          refine ⟨6042700432730613948605405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028466955153742632403603 6042700432730613948605405)
          ·
            refine ⟨2266012662273980230727027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6042700432730613948605405 2266012662273980230727027)
            ·
              refine ⟨3399018993410970346090541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266012662273980230727027 3399018993410970346090541)
              ·
                refine ⟨1274632122529113879783953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3399018993410970346090541 1274632122529113879783953)
                ·
                  refine ⟨955974091896835409837965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1274632122529113879783953 955974091896835409837965)
                  ·
                    refine ⟨358490284461313278689237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 955974091896835409837965 358490284461313278689237)
                    ·
                      rfl

theorem cell22_1047236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1047236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047236 prefixEnd_1047236 := by exact prefixLift 1047236
  have htrace : WordTrace (prefixWord ++ tailWord_1047236) baseStart_1047236 baseEnd_1047236 := by
    simpa [prefixWord, tailWord_1047236, baseEnd_1047236] using wordTrace_append hprefix tailTrace_1047236
  have hstable : (prefixWord ++ tailWord_1047236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047236).length < 2 ^ (prefixWord ++ tailWord_1047236).sum := by decide
  have hdescent : baseEnd_1047236 < baseStart_1047236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047281 : List Nat := [1, 2, 2, 2, 2, 2, 3, 4, 1, 3]
def baseStart_1047281 : Nat := 118140960795 + 1047281 * 2 ^ 59
def prefixEnd_1047281 : Nat := 4983230072969 + 3 ^ 40 * 1047281 * 2
def baseEnd_1047281 : Nat := 358505688880948161314099

theorem tailTrace_1047281 : CollatzResearch.WordTrace tailWord_1047281 prefixEnd_1047281 358505688880948161314099 := by
  unfold tailWord_1047281
  simp only [CollatzResearch.WordTrace]
  refine ⟨38197476118887273200029697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25464984079258182133353131 38197476118887273200029697)
  ·
    refine ⟨28648107089165454900022273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38197476118887273200029697 28648107089165454900022273)
    ·
      refine ⟨21486080316874091175016705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28648107089165454900022273 21486080316874091175016705)
      ·
        refine ⟨16114560237655568381262529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21486080316874091175016705 16114560237655568381262529)
        ·
          refine ⟨12085920178241676285946897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16114560237655568381262529 12085920178241676285946897)
          ·
            refine ⟨9064440133681257214460173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12085920178241676285946897 9064440133681257214460173)
            ·
              refine ⟨3399165050130471455422565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9064440133681257214460173 3399165050130471455422565)
              ·
                refine ⟨637343446899463397891731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3399165050130471455422565 637343446899463397891731)
                ·
                  refine ⟨956015170349195096837597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637343446899463397891731 956015170349195096837597)
                  ·
                    refine ⟨358505688880948161314099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 956015170349195096837597 358505688880948161314099)
                    ·
                      rfl

theorem cell22_1047281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_1047281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047281 prefixEnd_1047281 := by exact prefixLift 1047281
  have htrace : WordTrace (prefixWord ++ tailWord_1047281) baseStart_1047281 baseEnd_1047281 := by
    simpa [prefixWord, tailWord_1047281, baseEnd_1047281] using wordTrace_append hprefix tailTrace_1047281
  have hstable : (prefixWord ++ tailWord_1047281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047281).length < 2 ^ (prefixWord ++ tailWord_1047281).sum := by decide
  have hdescent : baseEnd_1047281 < baseStart_1047281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047292 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1047292 : Nat := 118140960795 + 1047292 * 2 ^ 59
def prefixEnd_1047292 : Nat := 4983230072969 + 3 ^ 40 * 1047292 * 2
def baseEnd_1047292 : Nat := 358509454405747799289065

theorem tailTrace_1047292 : CollatzResearch.WordTrace tailWord_1047292 prefixEnd_1047292 358509454405747799289065 := by
  unfold tailWord_1047292
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098938660923711039340065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25465251547898281385786753 19098938660923711039340065)
  ·
    refine ⟨14324203995692783279505049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19098938660923711039340065 14324203995692783279505049)
    ·
      refine ⟨10743152996769587459628787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14324203995692783279505049 10743152996769587459628787)
      ·
        refine ⟨16114729495154381189443181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10743152996769587459628787 16114729495154381189443181)
        ·
          refine ⟨6043023560682892946041193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16114729495154381189443181 6043023560682892946041193)
          ·
            refine ⟨4532267670512169709530895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6043023560682892946041193 4532267670512169709530895)
            ·
              refine ⟨6798401505768254564296343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532267670512169709530895 6798401505768254564296343)
              ·
                refine ⟨10197602258652381846444515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6798401505768254564296343 10197602258652381846444515)
                ·
                  refine ⟨15296403387978572769666773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10197602258652381846444515 15296403387978572769666773)
                  ·
                    refine ⟨358509454405747799289065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15296403387978572769666773 358509454405747799289065)
                    ·
                      rfl

theorem cell22_1047292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1047292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047292 prefixEnd_1047292 := by exact prefixLift 1047292
  have htrace : WordTrace (prefixWord ++ tailWord_1047292) baseStart_1047292 baseEnd_1047292 := by
    simpa [prefixWord, tailWord_1047292, baseEnd_1047292] using wordTrace_append hprefix tailTrace_1047292
  have hstable : (prefixWord ++ tailWord_1047292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047292).length < 2 ^ (prefixWord ++ tailWord_1047292).sum := by decide
  have hdescent : baseEnd_1047292 < baseStart_1047292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047322 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_1047322 : Nat := 118140960795 + 1047322 * 2 ^ 59
def prefixEnd_1047322 : Nat := 4983230072969 + 3 ^ 40 * 1047322 * 2
def baseEnd_1047322 : Nat := 119506574672945907012991

theorem tailTrace_1047322 : CollatzResearch.WordTrace tailWord_1047322 prefixEnd_1047322 119506574672945907012991 := by
  unfold tailWord_1047322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549742877934684300568055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25465981007825824801514813 9549742877934684300568055)
  ·
    refine ⟨14324614316902026450852083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9549742877934684300568055 14324614316902026450852083)
    ·
      refine ⟨21486921475353039676278125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14324614316902026450852083 21486921475353039676278125)
      ·
        refine ⟨8057595553257389878604297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21486921475353039676278125 8057595553257389878604297)
        ·
          refine ⟨6043196664943042408953223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8057595553257389878604297 6043196664943042408953223)
          ·
            refine ⟨9064794997414563613429835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043196664943042408953223 9064794997414563613429835)
            ·
              refine ⟨13597192496121845420144753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064794997414563613429835 13597192496121845420144753)
              ·
                refine ⟨10197894372091384065108565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13597192496121845420144753 10197894372091384065108565)
                ·
                  refine ⟨119506574672945907012991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10197894372091384065108565 119506574672945907012991)
                  ·
                    rfl

theorem cell22_1047322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_1047322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047322 prefixEnd_1047322 := by exact prefixLift 1047322
  have htrace : WordTrace (prefixWord ++ tailWord_1047322) baseStart_1047322 baseEnd_1047322 := by
    simpa [prefixWord, tailWord_1047322, baseEnd_1047322] using wordTrace_append hprefix tailTrace_1047322
  have hstable : (prefixWord ++ tailWord_1047322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047322).length < 2 ^ (prefixWord ++ tailWord_1047322).sum := by decide
  have hdescent : baseEnd_1047322 < baseStart_1047322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047352 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_1047352 : Nat := 118140960795 + 1047352 * 2 ^ 59
def prefixEnd_1047352 : Nat := 4983230072969 + 3 ^ 40 * 1047352 * 2
def baseEnd_1047352 : Nat := 358529993631927642788881

theorem tailTrace_1047352 : CollatzResearch.WordTrace tailWord_1047352 prefixEnd_1047352 358529993631927642788881 := by
  unfold tailWord_1047352
  simp only [CollatzResearch.WordTrace]
  refine ⟨19100032850815026162932155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25466710467753368217242873 19100032850815026162932155)
  ·
    refine ⟨28650049276222539244398233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19100032850815026162932155 28650049276222539244398233)
    ·
      refine ⟨21487536957166904433298675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28650049276222539244398233 21487536957166904433298675)
      ·
        refine ⟨32231305435750356649948013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21487536957166904433298675 32231305435750356649948013)
        ·
          refine ⟨12086739538406383743730505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32231305435750356649948013 12086739538406383743730505)
          ·
            refine ⟨9065054653804787807797879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12086739538406383743730505 9065054653804787807797879)
            ·
              refine ⟨13597581980707181711696819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065054653804787807797879 13597581980707181711696819)
              ·
                refine ⟨20396372971060772567545229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13597581980707181711696819 20396372971060772567545229)
                ·
                  refine ⟨7648639864147789712829461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20396372971060772567545229 7648639864147789712829461)
                  ·
                    refine ⟨358529993631927642788881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7648639864147789712829461 358529993631927642788881)
                    ·
                      rfl

theorem cell22_1047352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_1047352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047352 prefixEnd_1047352 := by exact prefixLift 1047352
  have htrace : WordTrace (prefixWord ++ tailWord_1047352) baseStart_1047352 baseEnd_1047352 := by
    simpa [prefixWord, tailWord_1047352, baseEnd_1047352] using wordTrace_append hprefix tailTrace_1047352
  have hstable : (prefixWord ++ tailWord_1047352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047352).length < 2 ^ (prefixWord ++ tailWord_1047352).sum := by decide
  have hdescent : baseEnd_1047352 < baseStart_1047352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047358 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1047358 : Nat := 118140960795 + 1047358 * 2 ^ 59
def prefixEnd_1047358 : Nat := 4983230072969 + 3 ^ 40 * 1047358 * 2
def baseEnd_1047358 : Nat := 358532047554545627138863

theorem tailTrace_1047358 : CollatzResearch.WordTrace tailWord_1047358 prefixEnd_1047358 358532047554545627138863 := by
  unfold tailWord_1047358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4775035567451039418822841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25466856359738876900388485 4775035567451039418822841)
  ·
    refine ⟨3581276675588279564117131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4775035567451039418822841 3581276675588279564117131)
    ·
      refine ⟨5371915013382419346175697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581276675588279564117131 5371915013382419346175697)
      ·
        refine ⟨4028936260036814509631773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5371915013382419346175697 4028936260036814509631773)
        ·
          refine ⟨1510851097513805441111915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4028936260036814509631773 1510851097513805441111915)
          ·
            refine ⟨2266276646270708161667873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510851097513805441111915 2266276646270708161667873)
            ·
              refine ⟨1699707484703031121250905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2266276646270708161667873 1699707484703031121250905)
              ·
                refine ⟨1274780613527273340938179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699707484703031121250905 1274780613527273340938179)
                ·
                  refine ⟨1912170920290910011407269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274780613527273340938179 1912170920290910011407269)
                  ·
                    refine ⟨358532047554545627138863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1912170920290910011407269 358532047554545627138863)
                    ·
                      rfl

theorem cell22_1047358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1047358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047358 prefixEnd_1047358 := by exact prefixLift 1047358
  have htrace : WordTrace (prefixWord ++ tailWord_1047358) baseStart_1047358 baseEnd_1047358 := by
    simpa [prefixWord, tailWord_1047358, baseEnd_1047358] using wordTrace_append hprefix tailTrace_1047358
  have hstable : (prefixWord ++ tailWord_1047358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047358).length < 2 ^ (prefixWord ++ tailWord_1047358).sum := by decide
  have hdescent : baseEnd_1047358 < baseStart_1047358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047450 : List Nat := [3, 1, 1, 4, 3, 1, 1, 4, 1, 3]
def baseStart_1047450 : Nat := 118140960795 + 1047450 * 2 ^ 59
def prefixEnd_1047450 : Nat := 4983230072969 + 3 ^ 40 * 1047450 * 2
def baseEnd_1047450 : Nat := 358563541034688053838581

theorem tailTrace_1047450 : CollatzResearch.WordTrace tailWord_1047450 prefixEnd_1047450 358563541034688053838581 := by
  unfold tailWord_1047450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550910013818753765732951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25469093370183343375287869 9550910013818753765732951)
  ·
    refine ⟨14326365020728130648599427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9550910013818753765732951 14326365020728130648599427)
    ·
      refine ⟨21489547531092195972899141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14326365020728130648599427 21489547531092195972899141)
      ·
        refine ⟨4029290162079786744918589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21489547531092195972899141 4029290162079786744918589)
        ·
          refine ⟨1510983810779920029344471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4029290162079786744918589 1510983810779920029344471)
          ·
            refine ⟨2266475716169880044016707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510983810779920029344471 2266475716169880044016707)
            ·
              refine ⟨3399713574254820066025061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266475716169880044016707 3399713574254820066025061)
              ·
                refine ⟨637446295172778762379699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3399713574254820066025061 637446295172778762379699)
                ·
                  refine ⟨956169442759168143569549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637446295172778762379699 956169442759168143569549)
                  ·
                    refine ⟨358563541034688053838581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 956169442759168143569549 358563541034688053838581)
                    ·
                      rfl

theorem cell22_1047450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_1047450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047450 prefixEnd_1047450 := by exact prefixLift 1047450
  have htrace : WordTrace (prefixWord ++ tailWord_1047450) baseStart_1047450 baseEnd_1047450 := by
    simpa [prefixWord, tailWord_1047450, baseEnd_1047450] using wordTrace_append hprefix tailTrace_1047450
  have hstable : (prefixWord ++ tailWord_1047450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047450).length < 2 ^ (prefixWord ++ tailWord_1047450).sum := by decide
  have hdescent : baseEnd_1047450 < baseStart_1047450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047459 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 3, 4]
def baseStart_1047459 : Nat := 118140960795 + 1047459 * 2 ^ 59
def prefixEnd_1047459 : Nat := 4983230072969 + 3 ^ 40 * 1047459 * 2
def baseEnd_1047459 : Nat := 358566621918615030363553

theorem tailTrace_1047459 : CollatzResearch.WordTrace tailWord_1047459 prefixEnd_1047459 358566621918615030363553 := by
  unfold tailWord_1047459
  simp only [CollatzResearch.WordTrace]
  refine ⟨38203968312242409600009431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25469312208161606400006287 38203968312242409600009431)
  ·
    refine ⟨57305952468363614400014147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38203968312242409600009431 57305952468363614400014147)
    ·
      refine ⟨85958928702545421600021221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57305952468363614400014147 85958928702545421600021221)
      ·
        refine ⟨16117299131727266550003979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85958928702545421600021221 16117299131727266550003979)
        ·
          refine ⟨24175948697590899825005969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16117299131727266550003979 24175948697590899825005969)
          ·
            refine ⟨18131961523193174868754477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24175948697590899825005969 18131961523193174868754477)
            ·
              refine ⟨6799485571197440575782929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18131961523193174868754477 6799485571197440575782929)
              ·
                refine ⟨5099614178398080431837197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799485571197440575782929 5099614178398080431837197)
                ·
                  refine ⟨1912355316899280161938949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5099614178398080431837197 1912355316899280161938949)
                  ·
                    refine ⟨358566621918615030363553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1912355316899280161938949 358566621918615030363553)
                    ·
                      rfl

theorem cell22_1047459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 4].length) (baseStart_1047459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047459 prefixEnd_1047459 := by exact prefixLift 1047459
  have htrace : WordTrace (prefixWord ++ tailWord_1047459) baseStart_1047459 baseEnd_1047459 := by
    simpa [prefixWord, tailWord_1047459, baseEnd_1047459] using wordTrace_append hprefix tailTrace_1047459
  have hstable : (prefixWord ++ tailWord_1047459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047459).length < 2 ^ (prefixWord ++ tailWord_1047459).sum := by decide
  have hdescent : baseEnd_1047459 < baseStart_1047459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047504 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_1047504 : Nat := 118140960795 + 1047504 * 2 ^ 59
def prefixEnd_1047504 : Nat := 4983230072969 + 3 ^ 40 * 1047504 * 2
def baseEnd_1047504 : Nat := 358582026338249912988415

theorem tailTrace_1047504 : CollatzResearch.WordTrace tailWord_1047504 prefixEnd_1047504 358582026338249912988415 := by
  unfold tailWord_1047504
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102804798539691142698783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25470406398052921523598377 19102804798539691142698783)
  ·
    refine ⟨28654207197809536714048175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19102804798539691142698783 28654207197809536714048175)
    ·
      refine ⟨42981310796714305071072263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28654207197809536714048175 42981310796714305071072263)
      ·
        refine ⟨64471966195071457606608395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42981310796714305071072263 64471966195071457606608395)
        ·
          refine ⟨96707949292607186409912593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64471966195071457606608395 96707949292607186409912593)
          ·
            refine ⟨72530961969455389807434445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96707949292607186409912593 72530961969455389807434445)
            ·
              refine ⟨27199110738545771177787917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72530961969455389807434445 27199110738545771177787917)
              ·
                refine ⟨10199666526954664191670469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27199110738545771177787917 10199666526954664191670469)
                ·
                  refine ⟨1912437473803999535938213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10199666526954664191670469 1912437473803999535938213)
                  ·
                    refine ⟨358582026338249912988415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1912437473803999535938213 358582026338249912988415)
                    ·
                      rfl

theorem cell22_1047504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_1047504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047504 prefixEnd_1047504 := by exact prefixLift 1047504
  have htrace : WordTrace (prefixWord ++ tailWord_1047504) baseStart_1047504 baseEnd_1047504 := by
    simpa [prefixWord, tailWord_1047504, baseEnd_1047504] using wordTrace_append hprefix tailTrace_1047504
  have hstable : (prefixWord ++ tailWord_1047504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047504).length < 2 ^ (prefixWord ++ tailWord_1047504).sum := by decide
  have hdescent : baseEnd_1047504 < baseStart_1047504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
