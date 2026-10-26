import V185TrunkScan23Chunk1212

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7186321 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_7186321 : Nat := 118140960795 + 7186321 * 2 ^ 59
def prefixEnd_7186321 : Nat := 4983230072969 + 3 ^ 40 * 7186321 * 2
def baseEnd_7186321 : Nat := 3690036810499083219738217

theorem tailTrace_7186321 : CollatzResearch.WordTrace tailWord_7186321 prefixEnd_7186321 3690036810499083219738217 := by
  unfold tailWord_7186321
  simp only [CollatzResearch.WordTrace]
  refine ⟨262106659798193817759502817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174737773198795878506335211 262106659798193817759502817)
  ·
    refine ⟨196579994848645363319627113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262106659798193817759502817 196579994848645363319627113)
    ·
      refine ⟨147434996136484022489720335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196579994848645363319627113 147434996136484022489720335)
      ·
        refine ⟨221152494204726033734580503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147434996136484022489720335 221152494204726033734580503)
        ·
          refine ⟨331728741307089050601870755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221152494204726033734580503 331728741307089050601870755)
          ·
            refine ⟨497593111960633575902806133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331728741307089050601870755 497593111960633575902806133)
            ·
              refine ⟨46649354246309397740888075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 497593111960633575902806133 46649354246309397740888075)
              ·
                refine ⟨69974031369464096611332113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46649354246309397740888075 69974031369464096611332113)
                ·
                  refine ⟨52480523527098072458499085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69974031369464096611332113 52480523527098072458499085)
                  ·
                    refine ⟨19680196322661777171937157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52480523527098072458499085 19680196322661777171937157)
                    ·
                      refine ⟨3690036810499083219738217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19680196322661777171937157 3690036810499083219738217)
                      ·
                        rfl

theorem cell23_7186321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_7186321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186321 prefixEnd_7186321 := by exact prefixLift 7186321
  have htrace : WordTrace (prefixWord ++ tailWord_7186321) baseStart_7186321 baseEnd_7186321 := by
    simpa [prefixWord, tailWord_7186321, baseEnd_7186321] using wordTrace_append hprefix tailTrace_7186321
  have hstable : (prefixWord ++ tailWord_7186321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186321).length < 2 ^ (prefixWord ++ tailWord_7186321).sum := by decide
  have hdescent : baseEnd_7186321 < baseStart_7186321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186332 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_7186332 : Nat := 118140960795 + 7186332 * 2 ^ 59
def prefixEnd_7186332 : Nat := 4983230072969 + 3 ^ 40 * 7186332 * 2
def baseEnd_7186332 : Nat := 3690042458786282676700667

theorem tailTrace_7186332 : CollatzResearch.WordTrace tailWord_7186332 prefixEnd_7186332 3690042458786282676700667 := by
  unfold tailWord_7186332
  simp only [CollatzResearch.WordTrace]
  refine ⟨131053530500576983319076625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174738040667435977758768833 131053530500576983319076625)
  ·
    refine ⟨98290147875432737489307469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131053530500576983319076625 98290147875432737489307469)
    ·
      refine ⟨36858805453287276558490301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98290147875432737489307469 36858805453287276558490301)
      ·
        refine ⟨13822052044982728709433863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36858805453287276558490301 13822052044982728709433863)
        ·
          refine ⟨20733078067474093064150795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13822052044982728709433863 20733078067474093064150795)
          ·
            refine ⟨31099617101211139596226193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20733078067474093064150795 31099617101211139596226193)
            ·
              refine ⟨23324712825908354697169645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31099617101211139596226193 23324712825908354697169645)
              ·
                refine ⟨8746767309715633011438617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23324712825908354697169645 8746767309715633011438617)
                ·
                  refine ⟨6560075482286724758578963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8746767309715633011438617 6560075482286724758578963)
                  ·
                    refine ⟨9840113223430087137868445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6560075482286724758578963 9840113223430087137868445)
                    ·
                      refine ⟨3690042458786282676700667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9840113223430087137868445 3690042458786282676700667)
                      ·
                        rfl

theorem cell23_7186332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_7186332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186332 prefixEnd_7186332 := by exact prefixLift 7186332
  have htrace : WordTrace (prefixWord ++ tailWord_7186332) baseStart_7186332 baseEnd_7186332 := by
    simpa [prefixWord, tailWord_7186332, baseEnd_7186332] using wordTrace_append hprefix tailTrace_7186332
  have hstable : (prefixWord ++ tailWord_7186332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186332).length < 2 ^ (prefixWord ++ tailWord_7186332).sum := by decide
  have hdescent : baseEnd_7186332 < baseStart_7186332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186341 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_7186341 : Nat := 118140960795 + 7186341 * 2 ^ 59
def prefixEnd_7186341 : Nat := 4983230072969 + 3 ^ 40 * 7186341 * 2
def baseEnd_7186341 : Nat := 3690047080112173141488125

theorem tailTrace_7186341 : CollatzResearch.WordTrace tailWord_7186341 prefixEnd_7186341 3690047080112173141488125 := by
  unfold tailWord_7186341
  simp only [CollatzResearch.WordTrace]
  refine ⟨262107389258121361175230877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174738259505414240783487251 262107389258121361175230877)
  ·
    refine ⟨98290270971795510440711579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262107389258121361175230877 98290270971795510440711579)
    ·
      refine ⟨147435406457693265661067369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98290270971795510440711579 147435406457693265661067369)
      ·
        refine ⟨110576554843269949245800527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147435406457693265661067369 110576554843269949245800527)
        ·
          refine ⟨165864832264904923868700791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110576554843269949245800527 165864832264904923868700791)
          ·
            refine ⟨248797248397357385803051187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165864832264904923868700791 248797248397357385803051187)
            ·
              refine ⟨373195872596036078704576781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248797248397357385803051187 373195872596036078704576781)
              ·
                refine ⟨139948452223513529514216293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373195872596036078704576781 139948452223513529514216293)
                ·
                  refine ⟨26240334791908786783915555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139948452223513529514216293 26240334791908786783915555)
                  ·
                    refine ⟨39360502187863180175873333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26240334791908786783915555 39360502187863180175873333)
                    ·
                      refine ⟨3690047080112173141488125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39360502187863180175873333 3690047080112173141488125)
                      ·
                        rfl

theorem cell23_7186341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_7186341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186341 prefixEnd_7186341 := by exact prefixLift 7186341
  have htrace : WordTrace (prefixWord ++ tailWord_7186341) baseStart_7186341 baseEnd_7186341 := by
    simpa [prefixWord, tailWord_7186341, baseEnd_7186341] using wordTrace_append hprefix tailTrace_7186341
  have hstable : (prefixWord ++ tailWord_7186341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186341).length < 2 ^ (prefixWord ++ tailWord_7186341).sum := by decide
  have hdescent : baseEnd_7186341 < baseStart_7186341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186350 : List Nat := [4, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7186350 : Nat := 118140960795 + 7186350 * 2 ^ 59
def prefixEnd_7186350 : Nat := 4983230072969 + 3 ^ 40 * 7186350 * 2
def baseEnd_7186350 : Nat := 3690051701438063606275585

theorem tailTrace_7186350 : CollatzResearch.WordTrace tailWord_7186350 prefixEnd_7186350 3690051701438063606275585 := by
  unfold tailWord_7186350
  simp only [CollatzResearch.WordTrace]
  refine ⟨32763464689386094464038563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174738478343392503808205669 32763464689386094464038563)
  ·
    refine ⟨49145197034079141696057845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32763464689386094464038563 49145197034079141696057845)
    ·
      refine ⟨4607362221944919534005423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49145197034079141696057845 4607362221944919534005423)
      ·
        refine ⟨6911043332917379301008135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4607362221944919534005423 6911043332917379301008135)
        ·
          refine ⟨10366564999376068951512203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911043332917379301008135 10366564999376068951512203)
          ·
            refine ⟨15549847499064103427268305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10366564999376068951512203 15549847499064103427268305)
            ·
              refine ⟨11662385624298077570451229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15549847499064103427268305 11662385624298077570451229)
              ·
                refine ⟨4373394609111779088919211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11662385624298077570451229 4373394609111779088919211)
                ·
                  refine ⟨6560091913667668633378817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373394609111779088919211 6560091913667668633378817)
                  ·
                    refine ⟨4920068935250751475034113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6560091913667668633378817 4920068935250751475034113)
                    ·
                      refine ⟨3690051701438063606275585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920068935250751475034113 3690051701438063606275585)
                      ·
                        rfl

theorem cell23_7186350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7186350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186350 prefixEnd_7186350 := by exact prefixLift 7186350
  have htrace : WordTrace (prefixWord ++ tailWord_7186350) baseStart_7186350 baseEnd_7186350 := by
    simpa [prefixWord, tailWord_7186350, baseEnd_7186350] using wordTrace_append hprefix tailTrace_7186350
  have hstable : (prefixWord ++ tailWord_7186350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186350).length < 2 ^ (prefixWord ++ tailWord_7186350).sum := by decide
  have hdescent : baseEnd_7186350 < baseStart_7186350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186351 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_7186351 : Nat := 118140960795 + 7186351 * 2 ^ 59
def prefixEnd_7186351 : Nat := 4983230072969 + 3 ^ 40 * 7186351 * 2
def baseEnd_7186351 : Nat := 3690052214918718102363079

theorem tailTrace_7186351 : CollatzResearch.WordTrace tailWord_7186351 prefixEnd_7186351 3690052214918718102363079 := by
  unfold tailWord_7186351
  simp only [CollatzResearch.WordTrace]
  refine ⟨262107753988085132883094907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174738502658723421922063271 262107753988085132883094907)
  ·
    refine ⟨393161630982127699324642361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262107753988085132883094907 393161630982127699324642361)
    ·
      refine ⟨294871223236595774493481771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393161630982127699324642361 294871223236595774493481771)
      ·
        refine ⟨442306834854893661740222657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294871223236595774493481771 442306834854893661740222657)
        ·
          refine ⟨331730126141170246305166993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442306834854893661740222657 331730126141170246305166993)
          ·
            refine ⟨248797594605877684728875245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331730126141170246305166993 248797594605877684728875245)
            ·
              refine ⟨93299097977204131773328217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248797594605877684728875245 93299097977204131773328217)
              ·
                refine ⟨69974323482903098829996163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93299097977204131773328217 69974323482903098829996163)
                ·
                  refine ⟨104961485224354648244994245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69974323482903098829996163 104961485224354648244994245)
                  ·
                    refine ⟨19680278479566496545936421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104961485224354648244994245 19680278479566496545936421)
                    ·
                      refine ⟨3690052214918718102363079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19680278479566496545936421 3690052214918718102363079)
                      ·
                        rfl

theorem cell23_7186351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_7186351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186351 prefixEnd_7186351 := by exact prefixLift 7186351
  have htrace : WordTrace (prefixWord ++ tailWord_7186351) baseStart_7186351 baseEnd_7186351 := by
    simpa [prefixWord, tailWord_7186351, baseEnd_7186351] using wordTrace_append hprefix tailTrace_7186351
  have hstable : (prefixWord ++ tailWord_7186351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186351).length < 2 ^ (prefixWord ++ tailWord_7186351).sum := by decide
  have hdescent : baseEnd_7186351 < baseStart_7186351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186355 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 4, 2, 2]
def baseStart_7186355 : Nat := 118140960795 + 7186355 * 2 ^ 59
def prefixEnd_7186355 : Nat := 4983230072969 + 3 ^ 40 * 7186355 * 2
def baseEnd_7186355 : Nat := 3690054268841336086713061

theorem tailTrace_7186355 : CollatzResearch.WordTrace tailWord_7186355 prefixEnd_7186355 3690054268841336086713061 := by
  unfold tailWord_7186355
  simp only [CollatzResearch.WordTrace]
  refine ⟨262107899880070641566240519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174738599920047094377493679 262107899880070641566240519)
  ·
    refine ⟨393161849820105962349360779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262107899880070641566240519 393161849820105962349360779)
    ·
      refine ⟨589742774730158943524041169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393161849820105962349360779 589742774730158943524041169)
      ·
        refine ⟨442307081047619207643030877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589742774730158943524041169 442307081047619207643030877)
        ·
          refine ⟨165865155392857202866136579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442307081047619207643030877 165865155392857202866136579)
          ·
            refine ⟨248797733089285804299204869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165865155392857202866136579 248797733089285804299204869)
            ·
              refine ⟨46649574954241088306100913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248797733089285804299204869 46649574954241088306100913)
              ·
                refine ⟨34987181215680816229575685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46649574954241088306100913 34987181215680816229575685)
                ·
                  refine ⟨6560096477940153043045441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34987181215680816229575685 6560096477940153043045441)
                  ·
                    refine ⟨4920072358455114782284081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6560096477940153043045441 4920072358455114782284081)
                    ·
                      refine ⟨3690054268841336086713061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920072358455114782284081 3690054268841336086713061)
                      ·
                        rfl

theorem cell23_7186355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 2, 2].length) (baseStart_7186355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186355 prefixEnd_7186355 := by exact prefixLift 7186355
  have htrace : WordTrace (prefixWord ++ tailWord_7186355) baseStart_7186355 baseEnd_7186355 := by
    simpa [prefixWord, tailWord_7186355, baseEnd_7186355] using wordTrace_append hprefix tailTrace_7186355
  have hstable : (prefixWord ++ tailWord_7186355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186355).length < 2 ^ (prefixWord ++ tailWord_7186355).sum := by decide
  have hdescent : baseEnd_7186355 < baseStart_7186355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186361 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 9]
def baseStart_7186361 : Nat := 118140960795 + 7186361 * 2 ^ 59
def prefixEnd_7186361 : Nat := 4983230072969 + 3 ^ 40 * 7186361 * 2
def baseEnd_7186361 : Nat := 410006372191695895915337

theorem tailTrace_7186361 : CollatzResearch.WordTrace tailWord_7186361 prefixEnd_7186361 410006372191695895915337 := by
  unfold tailWord_7186361
  simp only [CollatzResearch.WordTrace]
  refine ⟨262108118718048904590958937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174738745812032603060639291 262108118718048904590958937)
  ·
    refine ⟨196581089038536678443219203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262108118718048904590958937 196581089038536678443219203)
    ·
      refine ⟨294871633557805017664828805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196581089038536678443219203 294871633557805017664828805)
      ·
        refine ⟨55288431292088440812155401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294871633557805017664828805 55288431292088440812155401)
        ·
          refine ⟨41466323469066330609116551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55288431292088440812155401 41466323469066330609116551)
          ·
            refine ⟨62199485203599495913674827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41466323469066330609116551 62199485203599495913674827)
            ·
              refine ⟨93299227805399243870512241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62199485203599495913674827 93299227805399243870512241)
              ·
                refine ⟨69974420854049432902884181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93299227805399243870512241 69974420854049432902884181)
                ·
                  refine ⟨410006372191695895915337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69974420854049432902884181 410006372191695895915337)
                  ·
                    rfl

theorem cell23_7186361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 9].length) (baseStart_7186361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186361 prefixEnd_7186361 := by exact prefixLift 7186361
  have htrace : WordTrace (prefixWord ++ tailWord_7186361) baseStart_7186361 baseEnd_7186361 := by
    simpa [prefixWord, tailWord_7186361, baseEnd_7186361] using wordTrace_append hprefix tailTrace_7186361
  have hstable : (prefixWord ++ tailWord_7186361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186361).length < 2 ^ (prefixWord ++ tailWord_7186361).sum := by decide
  have hdescent : baseEnd_7186361 < baseStart_7186361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186391 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 3, 7]
def baseStart_7186391 : Nat := 118140960795 + 7186391 * 2 ^ 59
def prefixEnd_7186391 : Nat := 4983230072969 + 3 ^ 40 * 7186391 * 2
def baseEnd_7186391 : Nat := 1230024251381632648620965

theorem tailTrace_7186391 : CollatzResearch.WordTrace tailWord_7186391 prefixEnd_7186391 1230024251381632648620965 := by
  unfold tailWord_7186391
  simp only [CollatzResearch.WordTrace]
  refine ⟨262109212907940219714551027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174739475271960146476367351 262109212907940219714551027)
  ·
    refine ⟨393163819361910329571826541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262109212907940219714551027 393163819361910329571826541)
    ·
      refine ⟨147436432260716373589434953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393163819361910329571826541 147436432260716373589434953)
      ·
        refine ⟨110577324195537280192076215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147436432260716373589434953 110577324195537280192076215)
        ·
          refine ⟨165865986293305920288114323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110577324195537280192076215 165865986293305920288114323)
          ·
            refine ⟨248798979439958880432171485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165865986293305920288114323 248798979439958880432171485)
            ·
              refine ⟨93299617289984580162064307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248798979439958880432171485 93299617289984580162064307)
              ·
                refine ⟨139949425934976870243096461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93299617289984580162064307 139949425934976870243096461)
                ·
                  refine ⟨52481034725616326341161173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139949425934976870243096461 52481034725616326341161173)
                  ·
                    refine ⟨1230024251381632648620965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52481034725616326341161173 1230024251381632648620965)
                    ·
                      rfl

theorem cell23_7186391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_7186391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186391 prefixEnd_7186391 := by exact prefixLift 7186391
  have htrace : WordTrace (prefixWord ++ tailWord_7186391) baseStart_7186391 baseEnd_7186391 := by
    simpa [prefixWord, tailWord_7186391, baseEnd_7186391] using wordTrace_append hprefix tailTrace_7186391
  have hstable : (prefixWord ++ tailWord_7186391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186391).length < 2 ^ (prefixWord ++ tailWord_7186391).sum := by decide
  have hdescent : baseEnd_7186391 < baseStart_7186391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186408 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 2, 5]
def baseStart_7186408 : Nat := 118140960795 + 7186408 * 2 ^ 59
def prefixEnd_7186408 : Nat := 4983230072969 + 3 ^ 40 * 7186408 * 2
def baseEnd_7186408 : Nat := 1230027161105341459783439

theorem tailTrace_7186408 : CollatzResearch.WordTrace tailWord_7186408 prefixEnd_7186408 1230027161105341459783439 := by
  unfold tailWord_7186408
  simp only [CollatzResearch.WordTrace]
  refine ⟨131054916474439315808959939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174739888632585754411946585 131054916474439315808959939)
  ·
    refine ⟨196582374711658973713439909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131054916474439315808959939 196582374711658973713439909)
    ·
      refine ⟨36859195258436057571269983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196582374711658973713439909 36859195258436057571269983)
      ·
        refine ⟨55288792887654086356904975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36859195258436057571269983 55288792887654086356904975)
        ·
          refine ⟨82933189331481129535357463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55288792887654086356904975 82933189331481129535357463)
          ·
            refine ⟨124399783997221694303036195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82933189331481129535357463 124399783997221694303036195)
            ·
              refine ⟨186599675995832541454554293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124399783997221694303036195 186599675995832541454554293)
              ·
                refine ⟨17493719624609300761364465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186599675995832541454554293 17493719624609300761364465)
                ·
                  refine ⟨13120289718456975571023349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17493719624609300761364465 13120289718456975571023349)
                  ·
                    refine ⟨1230027161105341459783439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13120289718456975571023349 1230027161105341459783439)
                    ·
                      rfl

theorem cell23_7186408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_7186408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186408 prefixEnd_7186408 := by exact prefixLift 7186408
  have htrace : WordTrace (prefixWord ++ tailWord_7186408) baseStart_7186408 baseEnd_7186408 := by
    simpa [prefixWord, tailWord_7186408, baseEnd_7186408] using wordTrace_append hprefix tailTrace_7186408
  have hstable : (prefixWord ++ tailWord_7186408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186408).length < 2 ^ (prefixWord ++ tailWord_7186408).sum := by decide
  have hdescent : baseEnd_7186408 < baseStart_7186408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186489 : List Nat := [1, 2, 1, 5, 3, 1, 1, 4, 1, 4]
def baseStart_7186489 : Nat := 118140960795 + 7186489 * 2 ^ 59
def prefixEnd_7186489 : Nat := 4983230072969 + 3 ^ 40 * 7186489 * 2
def baseEnd_7186489 : Nat := 1230041025083012854145815

theorem tailTrace_7186489 : CollatzResearch.WordTrace tailWord_7186489 prefixEnd_7186489 1230041025083012854145815 := by
  unfold tailWord_7186489
  simp only [CollatzResearch.WordTrace]
  refine ⟨262112787261585182451618521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174741858174390121634412347 262112787261585182451618521)
  ·
    refine ⟨196584590446188886838713891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262112787261585182451618521 196584590446188886838713891)
    ·
      refine ⟨294876885669283330258070837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196584590446188886838713891 294876885669283330258070837)
      ·
        refine ⟨27644708031495312211694141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294876885669283330258070837 27644708031495312211694141)
        ·
          refine ⟨10366765511810742079385303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27644708031495312211694141 10366765511810742079385303)
          ·
            refine ⟨15550148267716113119077955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10366765511810742079385303 15550148267716113119077955)
            ·
              refine ⟨23325222401574169678616933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15550148267716113119077955 23325222401574169678616933)
              ·
                refine ⟨4373479200295156814740675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23325222401574169678616933 4373479200295156814740675)
                ·
                  refine ⟨6560218800442735222111013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373479200295156814740675 6560218800442735222111013)
                  ·
                    refine ⟨1230041025083012854145815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6560218800442735222111013 1230041025083012854145815)
                    ·
                      rfl

theorem cell23_7186489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 4].length) (baseStart_7186489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186489 prefixEnd_7186489 := by exact prefixLift 7186489
  have htrace : WordTrace (prefixWord ++ tailWord_7186489) baseStart_7186489 baseEnd_7186489 := by
    simpa [prefixWord, tailWord_7186489, baseEnd_7186489] using wordTrace_append hprefix tailTrace_7186489
  have hstable : (prefixWord ++ tailWord_7186489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186489).length < 2 ^ (prefixWord ++ tailWord_7186489).sum := by decide
  have hdescent : baseEnd_7186489 < baseStart_7186489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186502 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_7186502 : Nat := 118140960795 + 7186502 * 2 ^ 59
def prefixEnd_7186502 : Nat := 4983230072969 + 3 ^ 40 * 7186502 * 2
def baseEnd_7186502 : Nat := 410014416721949667952765

theorem tailTrace_7186502 : CollatzResearch.WordTrace tailWord_7186502 prefixEnd_7186502 410014416721949667952765 := by
  unfold tailWord_7186502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8191039419079315177245055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174742174273692057114561173 8191039419079315177245055)
  ·
    refine ⟨12286559128618972765867583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8191039419079315177245055 12286559128618972765867583)
    ·
      refine ⟨18429838692928459148801375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12286559128618972765867583 18429838692928459148801375)
      ·
        refine ⟨27644758039392688723202063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18429838692928459148801375 27644758039392688723202063)
        ·
          refine ⟨41467137059089033084803095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27644758039392688723202063 41467137059089033084803095)
          ·
            refine ⟨62200705588633549627204643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41467137059089033084803095 62200705588633549627204643)
            ·
              refine ⟨93301058382950324440806965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62200705588633549627204643 93301058382950324440806965)
              ·
                refine ⟨8746974223401592916325653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93301058382950324440806965 8746974223401592916325653)
                ·
                  refine ⟨410014416721949667952765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8746974223401592916325653 410014416721949667952765)
                  ·
                    rfl

theorem cell23_7186502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_7186502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186502 prefixEnd_7186502 := by exact prefixLift 7186502
  have htrace : WordTrace (prefixWord ++ tailWord_7186502) baseStart_7186502 baseEnd_7186502 := by
    simpa [prefixWord, tailWord_7186502, baseEnd_7186502] using wordTrace_append hprefix tailTrace_7186502
  have hstable : (prefixWord ++ tailWord_7186502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186502).length < 2 ^ (prefixWord ++ tailWord_7186502).sum := by decide
  have hdescent : baseEnd_7186502 < baseStart_7186502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186505 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 1, 5, 2]
def baseStart_7186505 : Nat := 118140960795 + 7186505 * 2 ^ 59
def prefixEnd_7186505 : Nat := 4983230072969 + 3 ^ 40 * 7186505 * 2
def baseEnd_7186505 : Nat := 3690131290939510499837371

theorem tailTrace_7186505 : CollatzResearch.WordTrace tailWord_7186505 prefixEnd_7186505 3690131290939510499837371 := by
  unfold tailWord_7186505
  simp only [CollatzResearch.WordTrace]
  refine ⟨262113370829527217184200969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174742247219684811456133979 262113370829527217184200969)
  ·
    refine ⟨196585028122145412888150727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262113370829527217184200969 196585028122145412888150727)
    ·
      refine ⟨294877542183218119332226091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196585028122145412888150727 294877542183218119332226091)
      ·
        refine ⟨442316313274827178998339137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294877542183218119332226091 442316313274827178998339137)
        ·
          refine ⟨331737234956120384248754353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442316313274827178998339137 331737234956120384248754353)
          ·
            refine ⟨248802926217090288186565765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331737234956120384248754353 248802926217090288186565765)
            ·
              refine ⟨46650548665704429034981081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248802926217090288186565765 46650548665704429034981081)
              ·
                refine ⟨34987911499278321776235811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46650548665704429034981081 34987911499278321776235811)
                ·
                  refine ⟨52481867248917482664353717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34987911499278321776235811 52481867248917482664353717)
                  ·
                    refine ⟨4920175054586013999783161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52481867248917482664353717 4920175054586013999783161)
                    ·
                      refine ⟨3690131290939510499837371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920175054586013999783161 3690131290939510499837371)
                      ·
                        rfl

theorem cell23_7186505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 5, 2].length) (baseStart_7186505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186505 prefixEnd_7186505 := by exact prefixLift 7186505
  have htrace : WordTrace (prefixWord ++ tailWord_7186505) baseStart_7186505 baseEnd_7186505 := by
    simpa [prefixWord, tailWord_7186505, baseEnd_7186505] using wordTrace_append hprefix tailTrace_7186505
  have hstable : (prefixWord ++ tailWord_7186505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186505).length < 2 ^ (prefixWord ++ tailWord_7186505).sum := by decide
  have hdescent : baseEnd_7186505 < baseStart_7186505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186532 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_7186532 : Nat := 118140960795 + 7186532 * 2 ^ 59
def prefixEnd_7186532 : Nat := 4983230072969 + 3 ^ 40 * 7186532 * 2
def baseEnd_7186532 : Nat := 1230048384972393964733249

theorem tailTrace_7186532 : CollatzResearch.WordTrace tailWord_7186532 prefixEnd_7186532 1230048384972393964733249 := by
  unfold tailWord_7186532
  simp only [CollatzResearch.WordTrace]
  refine ⟨131057177800214700397716925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174742903733619600530289233 131057177800214700397716925)
  ·
    refine ⟨49146441675080512649143847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131057177800214700397716925 49146441675080512649143847)
    ·
      refine ⟨73719662512620768973715771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49146441675080512649143847 73719662512620768973715771)
      ·
        refine ⟨110579493768931153460573657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73719662512620768973715771 110579493768931153460573657)
        ·
          refine ⟨82934620326698365095430243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110579493768931153460573657 82934620326698365095430243)
          ·
            refine ⟨124401930490047547643145365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82934620326698365095430243 124401930490047547643145365)
            ·
              refine ⟨5831340491720978795772439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124401930490047547643145365 5831340491720978795772439)
              ·
                refine ⟨8747010737581468193658659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5831340491720978795772439 8747010737581468193658659)
                ·
                  refine ⟨13120516106372202290487989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8747010737581468193658659 13120516106372202290487989)
                  ·
                    refine ⟨1230048384972393964733249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13120516106372202290487989 1230048384972393964733249)
                    ·
                      rfl

theorem cell23_7186532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_7186532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186532 prefixEnd_7186532 := by exact prefixLift 7186532
  have htrace : WordTrace (prefixWord ++ tailWord_7186532) baseStart_7186532 baseEnd_7186532 := by
    simpa [prefixWord, tailWord_7186532, baseEnd_7186532] using wordTrace_append hprefix tailTrace_7186532
  have hstable : (prefixWord ++ tailWord_7186532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186532).length < 2 ^ (prefixWord ++ tailWord_7186532).sum := by decide
  have hdescent : baseEnd_7186532 < baseStart_7186532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186545 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 4, 4]
def baseStart_7186545 : Nat := 118140960795 + 7186545 * 2 ^ 59
def prefixEnd_7186545 : Nat := 4983230072969 + 3 ^ 40 * 7186545 * 2
def baseEnd_7186545 : Nat := 1230050610055230114445729

theorem tailTrace_7186545 : CollatzResearch.WordTrace tailWord_7186545 prefixEnd_7186545 1230050610055230114445729 := by
  unfold tailWord_7186545
  simp only [CollatzResearch.WordTrace]
  refine ⟨262114829749382304015657089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174743219832921536010438059 262114829749382304015657089)
  ·
    refine ⟨196586122312036728011742817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262114829749382304015657089 196586122312036728011742817)
    ·
      refine ⟨147439591734027546008807113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196586122312036728011742817 147439591734027546008807113)
      ·
        refine ⟨110579693800520659506605335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147439591734027546008807113 110579693800520659506605335)
        ·
          refine ⟨165869540700780989259908003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110579693800520659506605335 165869540700780989259908003)
          ·
            refine ⟨248804311051171483889862005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165869540700780989259908003 248804311051171483889862005)
            ·
              refine ⟨23325404161047326614674563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248804311051171483889862005 23325404161047326614674563)
              ·
                refine ⟨34988106241570989922011845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23325404161047326614674563 34988106241570989922011845)
                ·
                  refine ⟨6560269920294560610377221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34988106241570989922011845 6560269920294560610377221)
                  ·
                    refine ⟨1230050610055230114445729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6560269920294560610377221 1230050610055230114445729)
                    ·
                      rfl

theorem cell23_7186545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_7186545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186545 prefixEnd_7186545 := by exact prefixLift 7186545
  have htrace : WordTrace (prefixWord ++ tailWord_7186545) baseStart_7186545 baseEnd_7186545 := by
    simpa [prefixWord, tailWord_7186545, baseEnd_7186545] using wordTrace_append hprefix tailTrace_7186545
  have hstable : (prefixWord ++ tailWord_7186545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186545).length < 2 ^ (prefixWord ++ tailWord_7186545).sum := by decide
  have hdescent : baseEnd_7186545 < baseStart_7186545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186565 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_7186565 : Nat := 118140960795 + 7186565 * 2 ^ 59
def prefixEnd_7186565 : Nat := 4983230072969 + 3 ^ 40 * 7186565 * 2
def baseEnd_7186565 : Nat := 3690162099778780265087095

theorem tailTrace_7186565 : CollatzResearch.WordTrace tailWord_7186565 prefixEnd_7186565 3690162099778780265087095 := by
  unfold tailWord_7186565
  simp only [CollatzResearch.WordTrace]
  refine ⟨262115559209309847431385149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174743706139539898287590099 262115559209309847431385149)
  ·
    refine ⟨98293334703491192786769431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262115559209309847431385149 98293334703491192786769431)
    ·
      refine ⟨147440002055236789180154147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98293334703491192786769431 147440002055236789180154147)
      ·
        refine ⟨221160003082855183770231221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147440002055236789180154147 221160003082855183770231221)
        ·
          refine ⟨20733750289017673478459177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221160003082855183770231221 20733750289017673478459177)
          ·
            refine ⟨15550312716763255108844383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20733750289017673478459177 15550312716763255108844383)
            ·
              refine ⟨23325469075144882663266575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15550312716763255108844383 23325469075144882663266575)
              ·
                refine ⟨34988203612717323994899863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23325469075144882663266575 34988203612717323994899863)
                ·
                  refine ⟨52482305419075985992349795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34988203612717323994899863 52482305419075985992349795)
                  ·
                    refine ⟨78723458128613978988524693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52482305419075985992349795 78723458128613978988524693)
                    ·
                      refine ⟨3690162099778780265087095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78723458128613978988524693 3690162099778780265087095)
                      ·
                        rfl

theorem cell23_7186565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_7186565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186565 prefixEnd_7186565 := by exact prefixLift 7186565
  have htrace : WordTrace (prefixWord ++ tailWord_7186565) baseStart_7186565 baseEnd_7186565 := by
    simpa [prefixWord, tailWord_7186565, baseEnd_7186565] using wordTrace_append hprefix tailTrace_7186565
  have hstable : (prefixWord ++ tailWord_7186565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186565).length < 2 ^ (prefixWord ++ tailWord_7186565).sum := by decide
  have hdescent : baseEnd_7186565 < baseStart_7186565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186580 : List Nat := [2, 4, 2, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7186580 : Nat := 118140960795 + 7186580 * 2 ^ 59
def prefixEnd_7186580 : Nat := 4983230072969 + 3 ^ 40 * 7186580 * 2
def baseEnd_7186580 : Nat := 3690169801988597706399527

theorem tailTrace_7186580 : CollatzResearch.WordTrace tailWord_7186580 prefixEnd_7186580 3690169801988597706399527 := by
  unfold tailWord_7186580
  simp only [CollatzResearch.WordTrace]
  refine ⟨131058053152127752496590597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174744070869503669995454129 131058053152127752496590597)
  ·
    refine ⟨24573384966023953593110737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131058053152127752496590597 24573384966023953593110737)
    ·
      refine ⟨18430038724517965194833053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24573384966023953593110737 18430038724517965194833053)
      ·
        refine ⟨6911264521694236948062395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18430038724517965194833053 6911264521694236948062395)
        ·
          refine ⟨10366896782541355422093593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911264521694236948062395 10366896782541355422093593)
          ·
            refine ⟨7775172586906016566570195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10366896782541355422093593 7775172586906016566570195)
            ·
              refine ⟨11662758880359024849855293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775172586906016566570195 11662758880359024849855293)
              ·
                refine ⟨4373534580134634318695735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11662758880359024849855293 4373534580134634318695735)
                ·
                  refine ⟨6560301870201951478043603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373534580134634318695735 6560301870201951478043603)
                  ·
                    refine ⟨9840452805302927217065405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6560301870201951478043603 9840452805302927217065405)
                    ·
                      refine ⟨3690169801988597706399527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9840452805302927217065405 3690169801988597706399527)
                      ·
                        rfl

theorem cell23_7186580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7186580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186580 prefixEnd_7186580 := by exact prefixLift 7186580
  have htrace : WordTrace (prefixWord ++ tailWord_7186580) baseStart_7186580 baseEnd_7186580 := by
    simpa [prefixWord, tailWord_7186580, baseEnd_7186580] using wordTrace_append hprefix tailTrace_7186580
  have hstable : (prefixWord ++ tailWord_7186580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186580).length < 2 ^ (prefixWord ++ tailWord_7186580).sum := by decide
  have hdescent : baseEnd_7186580 < baseStart_7186580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186585 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 3]
def baseStart_7186585 : Nat := 118140960795 + 7186585 * 2 ^ 59
def prefixEnd_7186585 : Nat := 4983230072969 + 3 ^ 40 * 7186585 * 2
def baseEnd_7186585 : Nat := 3690172369391870186837003

theorem tailTrace_7186585 : CollatzResearch.WordTrace tailWord_7186585 prefixEnd_7186585 3690172369391870186837003 := by
  unfold tailWord_7186585
  simp only [CollatzResearch.WordTrace]
  refine ⟨262116288669237390847113209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174744192446158260564742139 262116288669237390847113209)
  ·
    refine ⟨196587216501928043135334907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262116288669237390847113209 196587216501928043135334907)
    ·
      refine ⟨294880824752892064703002361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196587216501928043135334907 294880824752892064703002361)
      ·
        refine ⟨221160618564669048527251771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294880824752892064703002361 221160618564669048527251771)
        ·
          refine ⟨331740927847003572790877657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221160618564669048527251771 331740927847003572790877657)
          ·
            refine ⟨248805695885252679593158243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331740927847003572790877657 248805695885252679593158243)
            ·
              refine ⟨373208543827879019389737365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248805695885252679593158243 373208543827879019389737365)
              ·
                refine ⟨17494150491931829033893939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 373208543827879019389737365 17494150491931829033893939)
                ·
                  refine ⟨26241225737897743550840909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17494150491931829033893939 26241225737897743550840909)
                  ·
                    refine ⟨9840459651711653831565341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26241225737897743550840909 9840459651711653831565341)
                    ·
                      refine ⟨3690172369391870186837003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9840459651711653831565341 3690172369391870186837003)
                      ·
                        rfl

theorem cell23_7186585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_7186585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186585 prefixEnd_7186585 := by exact prefixLift 7186585
  have htrace : WordTrace (prefixWord ++ tailWord_7186585) baseStart_7186585 baseEnd_7186585 := by
    simpa [prefixWord, tailWord_7186585, baseEnd_7186585] using wordTrace_append hprefix tailTrace_7186585
  have hstable : (prefixWord ++ tailWord_7186585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186585).length < 2 ^ (prefixWord ++ tailWord_7186585).sum := by decide
  have hdescent : baseEnd_7186585 < baseStart_7186585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186613 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_7186613 : Nat := 118140960795 + 7186613 * 2 ^ 59
def prefixEnd_7186613 : Nat := 4983230072969 + 3 ^ 40 * 7186613 * 2
def baseEnd_7186613 : Nat := 1230062248950065359095625

theorem tailTrace_7186613 : CollatzResearch.WordTrace tailWord_7186613 prefixEnd_7186613 1230062248950065359095625 := by
  unfold tailWord_7186613
  simp only [CollatzResearch.WordTrace]
  refine ⟨262117309913135951629132493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174744873275423967752754995 262117309913135951629132493)
  ·
    refine ⟨98293991217425981860924685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262117309913135951629132493 98293991217425981860924685)
    ·
      refine ⟨36860246706534743197846757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98293991217425981860924685 36860246706534743197846757)
      ·
        refine ⟨6911296257475264349596267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36860246706534743197846757 6911296257475264349596267)
        ·
          refine ⟨10366944386212896524394401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911296257475264349596267 10366944386212896524394401)
          ·
            refine ⟨7775208289659672393295801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10366944386212896524394401 7775208289659672393295801)
            ·
              refine ⟨5831406217244754294971851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7775208289659672393295801 5831406217244754294971851)
              ·
                refine ⟨8747109325867131442457777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5831406217244754294971851 8747109325867131442457777)
                ·
                  refine ⟨6560331994400348581843333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8747109325867131442457777 6560331994400348581843333)
                  ·
                    refine ⟨1230062248950065359095625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6560331994400348581843333 1230062248950065359095625)
                    ·
                      rfl

theorem cell23_7186613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_7186613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186613 prefixEnd_7186613 := by exact prefixLift 7186613
  have htrace : WordTrace (prefixWord ++ tailWord_7186613) baseStart_7186613 baseEnd_7186613 := by
    simpa [prefixWord, tailWord_7186613, baseEnd_7186613] using wordTrace_append hprefix tailTrace_7186613
  have hstable : (prefixWord ++ tailWord_7186613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186613).length < 2 ^ (prefixWord ++ tailWord_7186613).sum := by decide
  have hdescent : baseEnd_7186613 < baseStart_7186613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186629 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 1, 3, 2]
def baseStart_7186629 : Nat := 118140960795 + 7186629 * 2 ^ 59
def prefixEnd_7186629 : Nat := 4983230072969 + 3 ^ 40 * 7186629 * 2
def baseEnd_7186629 : Nat := 3690194962540668014686801

theorem tailTrace_7186629 : CollatzResearch.WordTrace tailWord_7186629 prefixEnd_7186629 3690194962540668014686801 := by
  unfold tailWord_7186629
  simp only [CollatzResearch.WordTrace]
  refine ⟨262117893481077986361714941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174745262320718657574476627 262117893481077986361714941)
  ·
    refine ⟨98294210055404244885643103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262117893481077986361714941 98294210055404244885643103)
    ·
      refine ⟨147441315083106367328464655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98294210055404244885643103 147441315083106367328464655)
      ·
        refine ⟨221161972624659550992696983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147441315083106367328464655 221161972624659550992696983)
        ·
          refine ⟨331742958936989326489045475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221161972624659550992696983 331742958936989326489045475)
          ·
            refine ⟨497614438405483989733568213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331742958936989326489045475 497614438405483989733568213)
            ·
              refine ⟨11662838400128531009380505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 497614438405483989733568213 11662838400128531009380505)
              ·
                refine ⟨8747128800096398257035379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11662838400128531009380505 8747128800096398257035379)
                ·
                  refine ⟨13120693200144597385553069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8747128800096398257035379 13120693200144597385553069)
                  ·
                    refine ⟨4920259950054224019582401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13120693200144597385553069 4920259950054224019582401)
                    ·
                      refine ⟨3690194962540668014686801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920259950054224019582401 3690194962540668014686801)
                      ·
                        rfl

theorem cell23_7186629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_7186629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186629 prefixEnd_7186629 := by exact prefixLift 7186629
  have htrace : WordTrace (prefixWord ++ tailWord_7186629) baseStart_7186629 baseEnd_7186629 := by
    simpa [prefixWord, tailWord_7186629, baseEnd_7186629] using wordTrace_append hprefix tailTrace_7186629
  have hstable : (prefixWord ++ tailWord_7186629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186629).length < 2 ^ (prefixWord ++ tailWord_7186629).sum := by decide
  have hdescent : baseEnd_7186629 < baseStart_7186629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186655 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_7186655 : Nat := 118140960795 + 7186655 * 2 ^ 59
def prefixEnd_7186655 : Nat := 4983230072969 + 3 ^ 40 * 7186655 * 2
def baseEnd_7186655 : Nat := 3690208313037684912961681

theorem tailTrace_7186655 : CollatzResearch.WordTrace tailWord_7186655 prefixEnd_7186655 3690208313037684912961681 := by
  unfold tailWord_7186655
  simp only [CollatzResearch.WordTrace]
  refine ⟨262118841778983792802161419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174745894519322528534774279 262118841778983792802161419)
  ·
    refine ⟨393178262668475689203242129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262118841778983792802161419 393178262668475689203242129)
    ·
      refine ⟨294883697001356766902431597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393178262668475689203242129 294883697001356766902431597)
      ·
        refine ⟨110581386375508787588411849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294883697001356766902431597 110581386375508787588411849)
        ·
          refine ⟨82936039781631590691308887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110581386375508787588411849 82936039781631590691308887)
          ·
            refine ⟨124404059672447386036963331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82936039781631590691308887 124404059672447386036963331)
            ·
              refine ⟨186606089508671079055444997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124404059672447386036963331 186606089508671079055444997)
              ·
                refine ⟨34988641782875827322895937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186606089508671079055444997 34988641782875827322895937)
                ·
                  refine ⟨26241481337156870492171953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34988641782875827322895937 26241481337156870492171953)
                  ·
                    refine ⟨19681111002867652869128965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26241481337156870492171953 19681111002867652869128965)
                    ·
                      refine ⟨3690208313037684912961681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19681111002867652869128965 3690208313037684912961681)
                      ·
                        rfl

theorem cell23_7186655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_7186655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186655 prefixEnd_7186655 := by exact prefixLift 7186655
  have htrace : WordTrace (prefixWord ++ tailWord_7186655) baseStart_7186655 baseEnd_7186655 := by
    simpa [prefixWord, tailWord_7186655, baseEnd_7186655] using wordTrace_append hprefix tailTrace_7186655
  have hstable : (prefixWord ++ tailWord_7186655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186655).length < 2 ^ (prefixWord ++ tailWord_7186655).sum := by decide
  have hdescent : baseEnd_7186655 < baseStart_7186655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186727 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_7186727 : Nat := 118140960795 + 7186727 * 2 ^ 59
def prefixEnd_7186727 : Nat := 4983230072969 + 3 ^ 40 * 7186727 * 2
def baseEnd_7186727 : Nat := 3690245283644808631261351

theorem tailTrace_7186727 : CollatzResearch.WordTrace tailWord_7186727 prefixEnd_7186727 3690245283644808631261351 := by
  unfold tailWord_7186727
  simp only [CollatzResearch.WordTrace]
  refine ⟨262121467834722949098782435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174747645223148632732521623 262121467834722949098782435)
  ·
    refine ⟨393182201752084423648173653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262121467834722949098782435 393182201752084423648173653)
    ·
      refine ⟨4607603926782239339627035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 393182201752084423648173653 4607603926782239339627035)
      ·
        refine ⟨6911405890173359009440553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4607603926782239339627035 6911405890173359009440553)
        ·
          refine ⟨5183554417630019257080415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6911405890173359009440553 5183554417630019257080415)
          ·
            refine ⟨7775331626445028885620623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183554417630019257080415 7775331626445028885620623)
            ·
              refine ⟨11662997439667543328430935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775331626445028885620623 11662997439667543328430935)
              ·
                refine ⟨17494496159501314992646403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11662997439667543328430935 17494496159501314992646403)
                ·
                  refine ⟨26241744239251972488969605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17494496159501314992646403 26241744239251972488969605)
                  ·
                    refine ⟨4920327044859744841681801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26241744239251972488969605 4920327044859744841681801)
                    ·
                      refine ⟨3690245283644808631261351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920327044859744841681801 3690245283644808631261351)
                      ·
                        rfl

theorem cell23_7186727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_7186727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186727 prefixEnd_7186727 := by exact prefixLift 7186727
  have htrace : WordTrace (prefixWord ++ tailWord_7186727) baseStart_7186727 baseEnd_7186727 := by
    simpa [prefixWord, tailWord_7186727, baseEnd_7186727] using wordTrace_append hprefix tailTrace_7186727
  have hstable : (prefixWord ++ tailWord_7186727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186727).length < 2 ^ (prefixWord ++ tailWord_7186727).sum := by decide
  have hdescent : baseEnd_7186727 < baseStart_7186727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186755 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 8]
def baseStart_7186755 : Nat := 118140960795 + 7186755 * 2 ^ 59
def prefixEnd_7186755 : Nat := 4983230072969 + 3 ^ 40 * 7186755 * 2
def baseEnd_7186755 : Nat := 410028851233681613523469

theorem tailTrace_7186755 : CollatzResearch.WordTrace tailWord_7186755 prefixEnd_7186755 410028851233681613523469 := by
  unfold tailWord_7186755
  simp only [CollatzResearch.WordTrace]
  refine ⟨262122489078621509880801719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174748326052414339920534479 262122489078621509880801719)
  ·
    refine ⟨393183733617932264821202579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262122489078621509880801719 393183733617932264821202579)
    ·
      refine ⟨589775600426898397231803869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393183733617932264821202579 589775600426898397231803869)
      ·
        refine ⟨221165850160086898961926451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589775600426898397231803869 221165850160086898961926451)
        ·
          refine ⟨331748775240130348442889677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221165850160086898961926451 331748775240130348442889677)
          ·
            refine ⟨124405790715048880666083629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331748775240130348442889677 124405790715048880666083629)
            ·
              refine ⟨46652171518143330249781361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124405790715048880666083629 46652171518143330249781361)
              ·
                refine ⟨34989128638607497687336021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46652171518143330249781361 34989128638607497687336021)
                ·
                  refine ⟨410028851233681613523469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34989128638607497687336021 410028851233681613523469)
                  ·
                    rfl

theorem cell23_7186755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 8].length) (baseStart_7186755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186755 prefixEnd_7186755 := by exact prefixLift 7186755
  have htrace : WordTrace (prefixWord ++ tailWord_7186755) baseStart_7186755 baseEnd_7186755 := by
    simpa [prefixWord, tailWord_7186755, baseEnd_7186755] using wordTrace_append hprefix tailTrace_7186755
  have hstable : (prefixWord ++ tailWord_7186755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186755).length < 2 ^ (prefixWord ++ tailWord_7186755).sum := by decide
  have hdescent : baseEnd_7186755 < baseStart_7186755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186769 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_7186769 : Nat := 118140960795 + 7186769 * 2 ^ 59
def prefixEnd_7186769 : Nat := 4983230072969 + 3 ^ 40 * 7186769 * 2
def baseEnd_7186769 : Nat := 3690266849832297466936157

theorem tailTrace_7186769 : CollatzResearch.WordTrace tailWord_7186769 prefixEnd_7186769 3690266849832297466936157 := by
  unfold tailWord_7186769
  simp only [CollatzResearch.WordTrace]
  refine ⟨262122999700570790271811361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174748666467047193514540907 262122999700570790271811361)
  ·
    refine ⟨196592249775428092703858521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262122999700570790271811361 196592249775428092703858521)
    ·
      refine ⟨147444187331571069527893891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196592249775428092703858521 147444187331571069527893891)
      ·
        refine ⟨221166280997356604291840837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147444187331571069527893891 221166280997356604291840837)
        ·
          refine ⟨41468677687004363304720157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221166280997356604291840837 41468677687004363304720157)
          ·
            refine ⟨15550754132626636239270059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41468677687004363304720157 15550754132626636239270059)
            ·
              refine ⟨23326131198939954358905089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15550754132626636239270059 23326131198939954358905089)
              ·
                refine ⟨17494598399204965769178817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23326131198939954358905089 17494598399204965769178817)
                ·
                  refine ⟨13120948799403724326884113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17494598399204965769178817 13120948799403724326884113)
                  ·
                    refine ⟨9840711599552793245163085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13120948799403724326884113 9840711599552793245163085)
                    ·
                      refine ⟨3690266849832297466936157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9840711599552793245163085 3690266849832297466936157)
                      ·
                        rfl

theorem cell23_7186769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_7186769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186769 prefixEnd_7186769 := by exact prefixLift 7186769
  have htrace : WordTrace (prefixWord ++ tailWord_7186769) baseStart_7186769 baseEnd_7186769 := by
    simpa [prefixWord, tailWord_7186769, baseEnd_7186769] using wordTrace_append hprefix tailTrace_7186769
  have hstable : (prefixWord ++ tailWord_7186769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186769).length < 2 ^ (prefixWord ++ tailWord_7186769).sum := by decide
  have hdescent : baseEnd_7186769 < baseStart_7186769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186772 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 8]
def baseStart_7186772 : Nat := 118140960795 + 7186772 * 2 ^ 59
def prefixEnd_7186772 : Nat := 4983230072969 + 3 ^ 40 * 7186772 * 2
def baseEnd_7186772 : Nat := 410029821141584550577627

theorem tailTrace_7186772 : CollatzResearch.WordTrace tailWord_7186772 prefixEnd_7186772 410029821141584550577627 := by
  unfold tailWord_7186772
  simp only [CollatzResearch.WordTrace]
  refine ⟨131061554559779960892085285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174748739413039947856113713 131061554559779960892085285)
  ·
    refine ⟨24574041479958742667265991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131061554559779960892085285 24574041479958742667265991)
    ·
      refine ⟨36861062219938114000898987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24574041479958742667265991 36861062219938114000898987)
      ·
        refine ⟨55291593329907171001348481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36861062219938114000898987 55291593329907171001348481)
        ·
          refine ⟨41468694997430378251011361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55291593329907171001348481 41468694997430378251011361)
          ·
            refine ⟨31101521248072783688258521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41468694997430378251011361 31101521248072783688258521)
            ·
              refine ⟨23326140936054587766193891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31101521248072783688258521 23326140936054587766193891)
              ·
                refine ⟨34989211404081881649290837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23326140936054587766193891 34989211404081881649290837)
                ·
                  refine ⟨410029821141584550577627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34989211404081881649290837 410029821141584550577627)
                  ·
                    rfl

theorem cell23_7186772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_7186772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186772 prefixEnd_7186772 := by exact prefixLift 7186772
  have htrace : WordTrace (prefixWord ++ tailWord_7186772) baseStart_7186772 baseEnd_7186772 := by
    simpa [prefixWord, tailWord_7186772, baseEnd_7186772] using wordTrace_append hprefix tailTrace_7186772
  have hstable : (prefixWord ++ tailWord_7186772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186772).length < 2 ^ (prefixWord ++ tailWord_7186772).sum := by decide
  have hdescent : baseEnd_7186772 < baseStart_7186772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186785 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 11]
def baseStart_7186785 : Nat := 118140960795 + 7186785 * 2 ^ 59
def prefixEnd_7186785 : Nat := 4983230072969 + 3 ^ 40 * 7186785 * 2
def baseEnd_7186785 : Nat := 1230091688507589801445361

theorem tailTrace_7186785 : CollatzResearch.WordTrace tailWord_7186785 prefixEnd_7186785 1230091688507589801445361 := by
  unfold tailWord_7186785
  simp only [CollatzResearch.WordTrace]
  refine ⟨262123583268512825004393809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174749055512341883336262539 262123583268512825004393809)
  ·
    refine ⟨196592687451384618753295357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262123583268512825004393809 196592687451384618753295357)
    ·
      refine ⟨73722257794269232032485759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196592687451384618753295357 73722257794269232032485759)
      ·
        refine ⟨110583386691403848048728639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73722257794269232032485759 110583386691403848048728639)
        ·
          refine ⟨165875080037105772073092959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110583386691403848048728639 165875080037105772073092959)
          ·
            refine ⟨248812620055658658109639439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165875080037105772073092959 248812620055658658109639439)
            ·
              refine ⟨373218930083487987164459159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248812620055658658109639439 373218930083487987164459159)
              ·
                refine ⟨559828395125231980746688739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373218930083487987164459159 559828395125231980746688739)
                ·
                  refine ⟨839742592687847971120033109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559828395125231980746688739 839742592687847971120033109)
                  ·
                    refine ⟨1230091688507589801445361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 839742592687847971120033109 1230091688507589801445361)
                    ·
                      rfl

theorem cell23_7186785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_7186785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186785 prefixEnd_7186785 := by exact prefixLift 7186785
  have htrace : WordTrace (prefixWord ++ tailWord_7186785) baseStart_7186785 baseEnd_7186785 := by
    simpa [prefixWord, tailWord_7186785, baseEnd_7186785] using wordTrace_append hprefix tailTrace_7186785
  have hstable : (prefixWord ++ tailWord_7186785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186785).length < 2 ^ (prefixWord ++ tailWord_7186785).sum := by decide
  have hdescent : baseEnd_7186785 < baseStart_7186785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186789 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 6]
def baseStart_7186789 : Nat := 118140960795 + 7186789 * 2 ^ 59
def prefixEnd_7186789 : Nat := 4983230072969 + 3 ^ 40 * 7186789 * 2
def baseEnd_7186789 : Nat := 410030791049487487631785

theorem tailTrace_7186789 : CollatzResearch.WordTrace tailWord_7186789 prefixEnd_7186789 410030791049487487631785 := by
  unfold tailWord_7186789
  simp only [CollatzResearch.WordTrace]
  refine ⟨262123729160498333687539421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174749152773665555791692947 262123729160498333687539421)
  ·
    refine ⟨98296398435186875132827283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262123729160498333687539421 98296398435186875132827283)
    ·
      refine ⟨147444597652780312699240925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98296398435186875132827283 147444597652780312699240925)
      ·
        refine ⟨55291724119792617262215347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147444597652780312699240925 55291724119792617262215347)
        ·
          refine ⟨82937586179688925893323021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55291724119792617262215347 82937586179688925893323021)
          ·
            refine ⟨31101594817383347209996133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82937586179688925893323021 31101594817383347209996133)
            ·
              refine ⟨5831549028259377601874275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31101594817383347209996133 5831549028259377601874275)
              ·
                refine ⟨8747323542389066402811413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5831549028259377601874275 8747323542389066402811413)
                ·
                  refine ⟨410030791049487487631785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8747323542389066402811413 410030791049487487631785)
                  ·
                    rfl

theorem cell23_7186789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_7186789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186789 prefixEnd_7186789 := by exact prefixLift 7186789
  have htrace : WordTrace (prefixWord ++ tailWord_7186789) baseStart_7186789 baseEnd_7186789 := by
    simpa [prefixWord, tailWord_7186789, baseEnd_7186789] using wordTrace_append hprefix tailTrace_7186789
  have hstable : (prefixWord ++ tailWord_7186789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186789).length < 2 ^ (prefixWord ++ tailWord_7186789).sum := by decide
  have hdescent : baseEnd_7186789 < baseStart_7186789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186795 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 7]
def baseStart_7186795 : Nat := 118140960795 + 7186795 * 2 ^ 59
def prefixEnd_7186795 : Nat := 4983230072969 + 3 ^ 40 * 7186795 * 2
def baseEnd_7186795 : Nat := 3690280200329314365211037

theorem tailTrace_7186795 : CollatzResearch.WordTrace tailWord_7186795 prefixEnd_7186795 3690280200329314365211037 := by
  unfold tailWord_7186795
  simp only [CollatzResearch.WordTrace]
  refine ⟨262123947998476596712257839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174749298665651064474838559 262123947998476596712257839)
  ·
    refine ⟨393185921997714895068386759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262123947998476596712257839 393185921997714895068386759)
    ·
      refine ⟨589778882996572342602580139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393185921997714895068386759 589778882996572342602580139)
      ·
        refine ⟨884668324494858513903870209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589778882996572342602580139 884668324494858513903870209)
        ·
          refine ⟨663501243371143885427902657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884668324494858513903870209 663501243371143885427902657)
          ·
            refine ⟨497625932528357914070926993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663501243371143885427902657 497625932528357914070926993)
            ·
              refine ⟨373219449396268435553195245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497625932528357914070926993 373219449396268435553195245)
              ·
                refine ⟨139957293523600663332448217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373219449396268435553195245 139957293523600663332448217)
                ·
                  refine ⟨104967970142700497499336163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139957293523600663332448217 104967970142700497499336163)
                  ·
                    refine ⟨157451955214050746249004245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104967970142700497499336163 157451955214050746249004245)
                    ·
                      refine ⟨3690280200329314365211037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157451955214050746249004245 3690280200329314365211037)
                      ·
                        rfl

theorem cell23_7186795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_7186795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186795 prefixEnd_7186795 := by exact prefixLift 7186795
  have htrace : WordTrace (prefixWord ++ tailWord_7186795) baseStart_7186795 baseEnd_7186795 := by
    simpa [prefixWord, tailWord_7186795, baseEnd_7186795] using wordTrace_append hprefix tailTrace_7186795
  have hstable : (prefixWord ++ tailWord_7186795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186795).length < 2 ^ (prefixWord ++ tailWord_7186795).sum := by decide
  have hdescent : baseEnd_7186795 < baseStart_7186795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186852 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_7186852 : Nat := 118140960795 + 7186852 * 2 ^ 59
def prefixEnd_7186852 : Nat := 4983230072969 + 3 ^ 40 * 7186852 * 2
def baseEnd_7186852 : Nat := 3690309468726620642198275

theorem tailTrace_7186852 : CollatzResearch.WordTrace tailWord_7186852 prefixEnd_7186852 3690309468726620642198275 := by
  unfold tailWord_7186852
  simp only [CollatzResearch.WordTrace]
  refine ⟨131063013479635047723541405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174750684639513396964721873 131063013479635047723541405)
  ·
    refine ⟨49148630054863142896328027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131063013479635047723541405 49148630054863142896328027)
    ·
      refine ⟨73722945082294714344492041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49148630054863142896328027 73722945082294714344492041)
      ·
        refine ⟨55292208811721035758369031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73722945082294714344492041 55292208811721035758369031)
        ·
          refine ⟨82938313217581553637553547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55292208811721035758369031 82938313217581553637553547)
          ·
            refine ⟨124407469826372330456330321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82938313217581553637553547 124407469826372330456330321)
            ·
              refine ⟨93305602369779247842247741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124407469826372330456330321 93305602369779247842247741)
              ·
                refine ⟨34989600888667217940842903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93305602369779247842247741 34989600888667217940842903)
                ·
                  refine ⟨52484401333000826911264355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34989600888667217940842903 52484401333000826911264355)
                  ·
                    refine ⟨78726601999501240366896533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52484401333000826911264355 78726601999501240366896533)
                    ·
                      refine ⟨3690309468726620642198275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78726601999501240366896533 3690309468726620642198275)
                      ·
                        rfl

theorem cell23_7186852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_7186852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186852 prefixEnd_7186852 := by exact prefixLift 7186852
  have htrace : WordTrace (prefixWord ++ tailWord_7186852) baseStart_7186852 baseEnd_7186852 := by
    simpa [prefixWord, tailWord_7186852, baseEnd_7186852] using wordTrace_append hprefix tailTrace_7186852
  have hstable : (prefixWord ++ tailWord_7186852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186852).length < 2 ^ (prefixWord ++ tailWord_7186852).sum := by decide
  have hdescent : baseEnd_7186852 < baseStart_7186852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186856 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7186856 : Nat := 118140960795 + 7186856 * 2 ^ 59
def prefixEnd_7186856 : Nat := 4983230072969 + 3 ^ 40 * 7186856 * 2
def baseEnd_7186856 : Nat := 3690311522649238626548257

theorem tailTrace_7186856 : CollatzResearch.WordTrace tailWord_7186856 prefixEnd_7186856 3690311522649238626548257 := by
  unfold tailWord_7186856
  simp only [CollatzResearch.WordTrace]
  refine ⟨131063086425627802065114211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174750781900837069420152281 131063086425627802065114211)
  ·
    refine ⟨196594629638441703097671317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131063086425627802065114211 196594629638441703097671317)
    ·
      refine ⟨9215373264301954832703343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196594629638441703097671317 9215373264301954832703343)
      ·
        refine ⟨13823059896452932249055015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9215373264301954832703343 13823059896452932249055015)
        ·
          refine ⟨20734589844679398373582523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13823059896452932249055015 20734589844679398373582523)
          ·
            refine ⟨31101884767019097560373785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20734589844679398373582523 31101884767019097560373785)
            ·
              refine ⟨23326413575264323170280339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31101884767019097560373785 23326413575264323170280339)
              ·
                refine ⟨34989620362896484755420509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23326413575264323170280339 34989620362896484755420509)
                ·
                  refine ⟨13121107636086181783282691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34989620362896484755420509 13121107636086181783282691)
                  ·
                    refine ⟨19681661454129272674924037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13121107636086181783282691 19681661454129272674924037)
                    ·
                      refine ⟨3690311522649238626548257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19681661454129272674924037 3690311522649238626548257)
                      ·
                        rfl

theorem cell23_7186856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7186856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186856 prefixEnd_7186856 := by exact prefixLift 7186856
  have htrace : WordTrace (prefixWord ++ tailWord_7186856) baseStart_7186856 baseEnd_7186856 := by
    simpa [prefixWord, tailWord_7186856, baseEnd_7186856] using wordTrace_append hprefix tailTrace_7186856
  have hstable : (prefixWord ++ tailWord_7186856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186856).length < 2 ^ (prefixWord ++ tailWord_7186856).sum := by decide
  have hdescent : baseEnd_7186856 < baseStart_7186856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186873 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 1, 1, 4]
def baseStart_7186873 : Nat := 118140960795 + 7186873 * 2 ^ 59
def prefixEnd_7186873 : Nat := 4983230072969 + 3 ^ 40 * 7186873 * 2
def baseEnd_7186873 : Nat := 3690320251820365060035679

theorem tailTrace_7186873 : CollatzResearch.WordTrace tailWord_7186873 prefixEnd_7186873 3690320251820365060035679 := by
  unfold tailWord_7186873
  simp only [CollatzResearch.WordTrace]
  refine ⟨262126792892194016033597273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174751195261462677355731515 262126792892194016033597273)
  ·
    refine ⟨196595094669145512025197955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262126792892194016033597273 196595094669145512025197955)
    ·
      refine ⟨294892642003718268037796933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196595094669145512025197955 294892642003718268037796933)
      ·
        refine ⟨55292370375697175257086925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294892642003718268037796933 55292370375697175257086925)
        ·
          refine ⟨20734638890886440721407597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55292370375697175257086925 20734638890886440721407597)
          ·
            refine ⟨7775489584082415270527849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20734638890886440721407597 7775489584082415270527849)
            ·
              refine ⟨5831617188061811452895887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7775489584082415270527849 5831617188061811452895887)
              ·
                refine ⟨8747425782092717179343831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5831617188061811452895887 8747425782092717179343831)
                ·
                  refine ⟨13121138673139075769015747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8747425782092717179343831 13121138673139075769015747)
                  ·
                    refine ⟨19681708009708613653523621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13121138673139075769015747 19681708009708613653523621)
                    ·
                      refine ⟨3690320251820365060035679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19681708009708613653523621 3690320251820365060035679)
                      ·
                        rfl

theorem cell23_7186873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_7186873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186873 prefixEnd_7186873 := by exact prefixLift 7186873
  have htrace : WordTrace (prefixWord ++ tailWord_7186873) baseStart_7186873 baseEnd_7186873 := by
    simpa [prefixWord, tailWord_7186873, baseEnd_7186873] using wordTrace_append hprefix tailTrace_7186873
  have hstable : (prefixWord ++ tailWord_7186873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186873).length < 2 ^ (prefixWord ++ tailWord_7186873).sum := by decide
  have hdescent : baseEnd_7186873 < baseStart_7186873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186957 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7186957 : Nat := 118140960795 + 7186957 * 2 ^ 59
def prefixEnd_7186957 : Nat := 4983230072969 + 3 ^ 40 * 7186957 * 2
def baseEnd_7186957 : Nat := 3690363384195342731385293

theorem tailTrace_7186957 : CollatzResearch.WordTrace tailWord_7186957 prefixEnd_7186957 3690363384195342731385293 := by
  unfold tailWord_7186957
  simp only [CollatzResearch.WordTrace]
  refine ⟨262129856623889698379655125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174753237749259798919770083 262129856623889698379655125)
  ·
    refine ⟨6143668514622414805773167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 262129856623889698379655125 6143668514622414805773167)
    ·
      refine ⟨9215502771933622208659751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6143668514622414805773167 9215502771933622208659751)
      ·
        refine ⟨13823254157900433312989627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9215502771933622208659751 13823254157900433312989627)
        ·
          refine ⟨20734881236850649969484441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13823254157900433312989627 20734881236850649969484441)
          ·
            refine ⟨15551160927637987477113331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20734881236850649969484441 15551160927637987477113331)
            ·
              refine ⟨23326741391456981215669997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15551160927637987477113331 23326741391456981215669997)
              ·
                refine ⟨8747528021796367955876249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23326741391456981215669997 8747528021796367955876249)
                ·
                  refine ⟨6560646016347275966907187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8747528021796367955876249 6560646016347275966907187)
                  ·
                    refine ⟨9840969024520913950360781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6560646016347275966907187 9840969024520913950360781)
                    ·
                      refine ⟨3690363384195342731385293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9840969024520913950360781 3690363384195342731385293)
                      ·
                        rfl

theorem cell23_7186957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7186957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186957 prefixEnd_7186957 := by exact prefixLift 7186957
  have htrace : WordTrace (prefixWord ++ tailWord_7186957) baseStart_7186957 baseEnd_7186957 := by
    simpa [prefixWord, tailWord_7186957, baseEnd_7186957] using wordTrace_append hprefix tailTrace_7186957
  have hstable : (prefixWord ++ tailWord_7186957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186957).length < 2 ^ (prefixWord ++ tailWord_7186957).sum := by decide
  have hdescent : baseEnd_7186957 < baseStart_7186957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186963 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 2, 2, 2]
def baseStart_7186963 : Nat := 118140960795 + 7186963 * 2 ^ 59
def prefixEnd_7186963 : Nat := 4983230072969 + 3 ^ 40 * 7186963 * 2
def baseEnd_7186963 : Nat := 3690366465079269707910265

theorem tailTrace_7186963 : CollatzResearch.WordTrace tailWord_7186963 prefixEnd_7186963 3690366465079269707910265 := by
  unfold tailWord_7186963
  simp only [CollatzResearch.WordTrace]
  refine ⟨262130075461867961404373543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174753383641245307602915695 262130075461867961404373543)
  ·
    refine ⟨393195113192801942106560315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262130075461867961404373543 393195113192801942106560315)
    ·
      refine ⟨589792669789202913159840473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393195113192801942106560315 589792669789202913159840473)
      ·
        refine ⟨442344502341902184869880355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589792669789202913159840473 442344502341902184869880355)
        ·
          refine ⟨663516753512853277304820533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442344502341902184869880355 663516753512853277304820533)
          ·
            refine ⟨62204695641829994747326925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 663516753512853277304820533 62204695641829994747326925)
            ·
              refine ⟨23326760865686248030247597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62204695641829994747326925 23326760865686248030247597)
              ·
                refine ⟨8747535324632343011342849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23326760865686248030247597 8747535324632343011342849)
                ·
                  refine ⟨6560651493474257258507137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8747535324632343011342849 6560651493474257258507137)
                  ·
                    refine ⟨4920488620105692943880353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6560651493474257258507137 4920488620105692943880353)
                    ·
                      refine ⟨3690366465079269707910265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920488620105692943880353 3690366465079269707910265)
                      ·
                        rfl

theorem cell23_7186963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 2, 2].length) (baseStart_7186963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186963 prefixEnd_7186963 := by exact prefixLift 7186963
  have htrace : WordTrace (prefixWord ++ tailWord_7186963) baseStart_7186963 baseEnd_7186963 := by
    simpa [prefixWord, tailWord_7186963, baseEnd_7186963] using wordTrace_append hprefix tailTrace_7186963
  have hstable : (prefixWord ++ tailWord_7186963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186963).length < 2 ^ (prefixWord ++ tailWord_7186963).sum := by decide
  have hdescent : baseEnd_7186963 < baseStart_7186963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186967 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7186967 : Nat := 118140960795 + 7186967 * 2 ^ 59
def prefixEnd_7186967 : Nat := 4983230072969 + 3 ^ 40 * 7186967 * 2
def baseEnd_7186967 : Nat := 3690368519001887692260247

theorem tailTrace_7186967 : CollatzResearch.WordTrace tailWord_7186967 prefixEnd_7186967 3690368519001887692260247 := by
  unfold tailWord_7186967
  simp only [CollatzResearch.WordTrace]
  refine ⟨262130221353853470087519155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174753480902568980058346103 262130221353853470087519155)
  ·
    refine ⟨393195332030780205131278733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262130221353853470087519155 393195332030780205131278733)
    ·
      refine ⟨147448249511542576924229525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393195332030780205131278733 147448249511542576924229525)
      ·
        refine ⟨6911636695853558293323259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147448249511542576924229525 6911636695853558293323259)
        ·
          refine ⟨10367455043780337439984889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911636695853558293323259 10367455043780337439984889)
          ·
            refine ⟨7775591282835253079988667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10367455043780337439984889 7775591282835253079988667)
            ·
              refine ⟨11663386924252879619983001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775591282835253079988667 11663386924252879619983001)
              ·
                refine ⟨8747540193189659714987251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11663386924252879619983001 8747540193189659714987251)
                ·
                  refine ⟨13121310289784489572480877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8747540193189659714987251 13121310289784489572480877)
                  ·
                    refine ⟨4920491358669183589680329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13121310289784489572480877 4920491358669183589680329)
                    ·
                      refine ⟨3690368519001887692260247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920491358669183589680329 3690368519001887692260247)
                      ·
                        rfl

theorem cell23_7186967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7186967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186967 prefixEnd_7186967 := by exact prefixLift 7186967
  have htrace : WordTrace (prefixWord ++ tailWord_7186967) baseStart_7186967 baseEnd_7186967 := by
    simpa [prefixWord, tailWord_7186967, baseEnd_7186967] using wordTrace_append hprefix tailTrace_7186967
  have hstable : (prefixWord ++ tailWord_7186967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186967).length < 2 ^ (prefixWord ++ tailWord_7186967).sum := by decide
  have hdescent : baseEnd_7186967 < baseStart_7186967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186980 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7186980 : Nat := 118140960795 + 7186980 * 2 ^ 59
def prefixEnd_7186980 : Nat := 4983230072969 + 3 ^ 40 * 7186980 * 2
def baseEnd_7186980 : Nat := 3690375194250396141397687

theorem tailTrace_7186980 : CollatzResearch.WordTrace tailWord_7186980 prefixEnd_7186980 3690375194250396141397687 := by
  unfold tailWord_7186980
  simp only [CollatzResearch.WordTrace]
  refine ⟨131065347751403186653871197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174753797001870915538494929 131065347751403186653871197)
  ·
    refine ⟨49149505406776194995201699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131065347751403186653871197 49149505406776194995201699)
    ·
      refine ⟨73724258110164292492802549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49149505406776194995201699 73724258110164292492802549)
      ·
        refine ⟨6911649197827902421200239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73724258110164292492802549 6911649197827902421200239)
        ·
          refine ⟨10367473796741853631800359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911649197827902421200239 10367473796741853631800359)
          ·
            refine ⟨15551210695112780447700539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10367473796741853631800359 15551210695112780447700539)
            ·
              refine ⟨23326816042669170671550809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15551210695112780447700539 23326816042669170671550809)
              ·
                refine ⟨17495112032001878003663107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23326816042669170671550809 17495112032001878003663107)
                ·
                  refine ⟨26242668048002817005494661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17495112032001878003663107 26242668048002817005494661)
                  ·
                    refine ⟨4920500259000528188530249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26242668048002817005494661 4920500259000528188530249)
                    ·
                      refine ⟨3690375194250396141397687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920500259000528188530249 3690375194250396141397687)
                      ·
                        rfl

theorem cell23_7186980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7186980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186980 prefixEnd_7186980 := by exact prefixLift 7186980
  have htrace : WordTrace (prefixWord ++ tailWord_7186980) baseStart_7186980 baseEnd_7186980 := by
    simpa [prefixWord, tailWord_7186980, baseEnd_7186980] using wordTrace_append hprefix tailTrace_7186980
  have hstable : (prefixWord ++ tailWord_7186980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186980).length < 2 ^ (prefixWord ++ tailWord_7186980).sum := by decide
  have hdescent : baseEnd_7186980 < baseStart_7186980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186999 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 2, 5]
def baseStart_7186999 : Nat := 118140960795 + 7186999 * 2 ^ 59
def prefixEnd_7186999 : Nat := 4983230072969 + 3 ^ 40 * 7186999 * 2
def baseEnd_7186999 : Nat := 1230128316794277189020033

theorem tailTrace_7186999 : CollatzResearch.WordTrace tailWord_7186999 prefixEnd_7186999 1230128316794277189020033 := by
  unfold tailWord_7186999
  simp only [CollatzResearch.WordTrace]
  refine ⟨262131388489737539552684051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174754258993158359701789367 262131388489737539552684051)
  ·
    refine ⟨393197082734606309329026077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262131388489737539552684051 393197082734606309329026077)
    ·
      refine ⟨147448906025477365998384779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393197082734606309329026077 147448906025477365998384779)
      ·
        refine ⟨221173359038216048997577169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147448906025477365998384779 221173359038216048997577169)
        ·
          refine ⟨165880019278662036748182877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221173359038216048997577169 165880019278662036748182877)
          ·
            refine ⟨62205007229498263780568579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165880019278662036748182877 62205007229498263780568579)
            ·
              refine ⟨93307510844247395670852869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62205007229498263780568579 93307510844247395670852869)
              ·
                refine ⟨17495158283296386688284913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93307510844247395670852869 17495158283296386688284913)
                ·
                  refine ⟨13121368712472290016213685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17495158283296386688284913 13121368712472290016213685)
                  ·
                    refine ⟨1230128316794277189020033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13121368712472290016213685 1230128316794277189020033)
                    ·
                      rfl

theorem cell23_7186999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_7186999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186999 prefixEnd_7186999 := by exact prefixLift 7186999
  have htrace : WordTrace (prefixWord ++ tailWord_7186999) baseStart_7186999 baseEnd_7186999 := by
    simpa [prefixWord, tailWord_7186999, baseEnd_7186999] using wordTrace_append hprefix tailTrace_7186999
  have hstable : (prefixWord ++ tailWord_7186999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186999).length < 2 ^ (prefixWord ++ tailWord_7186999).sum := by decide
  have hdescent : baseEnd_7186999 < baseStart_7186999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187019 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 4]
def baseStart_7187019 : Nat := 118140960795 + 7187019 * 2 ^ 59
def prefixEnd_7187019 : Nat := 4983230072969 + 3 ^ 40 * 7187019 * 2
def baseEnd_7187019 : Nat := 3690395219995921488810007

theorem tailTrace_7187019 : CollatzResearch.WordTrace tailWord_7187019 prefixEnd_7187019 3690395219995921488810007 := by
  unfold tailWord_7187019
  simp only [CollatzResearch.WordTrace]
  refine ⟨262132117949665082968412111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174754745299776721978941407 262132117949665082968412111)
  ·
    refine ⟨393198176924497624452618167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262132117949665082968412111 393198176924497624452618167)
    ·
      refine ⟨589797265386746436678927251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393198176924497624452618167 589797265386746436678927251)
      ·
        refine ⟨884695898080119655018390877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589797265386746436678927251 884695898080119655018390877)
        ·
          refine ⟨331760961780044870631896579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 884695898080119655018390877 331760961780044870631896579)
          ·
            refine ⟨497641442670067305947844869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331760961780044870631896579 497641442670067305947844869)
            ·
              refine ⟨93307770500637619865220913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 497641442670067305947844869 93307770500637619865220913)
              ·
                refine ⟨69980827875478214898915685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93307770500637619865220913 69980827875478214898915685)
                ·
                  refine ⟨13121405226652165293546691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69980827875478214898915685 13121405226652165293546691)
                  ·
                    refine ⟨19682107839978247940320037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13121405226652165293546691 19682107839978247940320037)
                    ·
                      refine ⟨3690395219995921488810007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19682107839978247940320037 3690395219995921488810007)
                      ·
                        rfl

theorem cell23_7187019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 4].length) (baseStart_7187019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187019 prefixEnd_7187019 := by exact prefixLift 7187019
  have htrace : WordTrace (prefixWord ++ tailWord_7187019) baseStart_7187019 baseEnd_7187019 := by
    simpa [prefixWord, tailWord_7187019, baseEnd_7187019] using wordTrace_append hprefix tailTrace_7187019
  have hstable : (prefixWord ++ tailWord_7187019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187019).length < 2 ^ (prefixWord ++ tailWord_7187019).sum := by decide
  have hdescent : baseEnd_7187019 < baseStart_7187019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187053 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_7187053 : Nat := 118140960795 + 7187053 * 2 ^ 59
def prefixEnd_7187053 : Nat := 4983230072969 + 3 ^ 40 * 7187053 * 2
def baseEnd_7187053 : Nat := 3690412678338174355784851

theorem tailTrace_7187053 : CollatzResearch.WordTrace tailWord_7187053 prefixEnd_7187053 3690412678338174355784851 := by
  unfold tailWord_7187053
  simp only [CollatzResearch.WordTrace]
  refine ⟨262133358031541906775149813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174755572021027937850099875 262133358031541906775149813)
  ·
    refine ⟨24575002315457053760170295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262133358031541906775149813 24575002315457053760170295)
    ·
      refine ⟨36862503473185580640255443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24575002315457053760170295 36862503473185580640255443)
      ·
        refine ⟨55293755209778370960383165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36862503473185580640255443 55293755209778370960383165)
        ·
          refine ⟨20735158203666889110143687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55293755209778370960383165 20735158203666889110143687)
          ·
            refine ⟨31102737305500333665215531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20735158203666889110143687 31102737305500333665215531)
            ·
              refine ⟨46654105958250500497823297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31102737305500333665215531 46654105958250500497823297)
              ·
                refine ⟨34990579468687875373367473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46654105958250500497823297 34990579468687875373367473)
                ·
                  refine ⟨26242934601515906530025605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34990579468687875373367473 26242934601515906530025605)
                  ·
                    refine ⟨4920550237784232474379801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26242934601515906530025605 4920550237784232474379801)
                    ·
                      refine ⟨3690412678338174355784851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920550237784232474379801 3690412678338174355784851)
                      ·
                        rfl

theorem cell23_7187053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_7187053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187053 prefixEnd_7187053 := by exact prefixLift 7187053
  have htrace : WordTrace (prefixWord ++ tailWord_7187053) baseStart_7187053 baseEnd_7187053 := by
    simpa [prefixWord, tailWord_7187053, baseEnd_7187053] using wordTrace_append hprefix tailTrace_7187053
  have hstable : (prefixWord ++ tailWord_7187053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187053).length < 2 ^ (prefixWord ++ tailWord_7187053).sum := by decide
  have hdescent : baseEnd_7187053 < baseStart_7187053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187059 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 6]
def baseStart_7187059 : Nat := 118140960795 + 7187059 * 2 ^ 59
def prefixEnd_7187059 : Nat := 4983230072969 + 3 ^ 40 * 7187059 * 2
def baseEnd_7187059 : Nat := 410046195469122370256647

theorem tailTrace_7187059 : CollatzResearch.WordTrace tailWord_7187059 prefixEnd_7187059 410046195469122370256647 := by
  unfold tailWord_7187059
  simp only [CollatzResearch.WordTrace]
  refine ⟨262133576869520169799868231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174755717913013446533245487 262133576869520169799868231)
  ·
    refine ⟨393200365304280254699802347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262133576869520169799868231 393200365304280254699802347)
    ·
      refine ⟨589800547956420382049703521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393200365304280254699802347 589800547956420382049703521)
      ·
        refine ⟨442350410967315286537277641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589800547956420382049703521 442350410967315286537277641)
        ·
          refine ⟨331762808225486464902958231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442350410967315286537277641 331762808225486464902958231)
          ·
            refine ⟨497644212338229697354437347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331762808225486464902958231 497644212338229697354437347)
            ·
              refine ⟨746466318507344546031656021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497644212338229697354437347 746466318507344546031656021)
              ·
                refine ⟨8747652170007943898808469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 746466318507344546031656021 8747652170007943898808469)
                ·
                  refine ⟨410046195469122370256647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8747652170007943898808469 410046195469122370256647)
                  ·
                    rfl

theorem cell23_7187059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 6].length) (baseStart_7187059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187059 prefixEnd_7187059 := by exact prefixLift 7187059
  have htrace : WordTrace (prefixWord ++ tailWord_7187059) baseStart_7187059 baseEnd_7187059 := by
    simpa [prefixWord, tailWord_7187059, baseEnd_7187059] using wordTrace_append hprefix tailTrace_7187059
  have hstable : (prefixWord ++ tailWord_7187059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187059).length < 2 ^ (prefixWord ++ tailWord_7187059).sum := by decide
  have hdescent : baseEnd_7187059 < baseStart_7187059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187063 : List Nat := [1, 1, 3, 1, 1, 3, 4, 4, 1, 4]
def baseStart_7187063 : Nat := 118140960795 + 7187063 * 2 ^ 59
def prefixEnd_7187063 : Nat := 4983230072969 + 3 ^ 40 * 7187063 * 2
def baseEnd_7187063 : Nat := 1230139271048239772219935

theorem tailTrace_7187063 : CollatzResearch.WordTrace tailWord_7187063 prefixEnd_7187063 1230139271048239772219935 := by
  unfold tailWord_7187063
  simp only [CollatzResearch.WordTrace]
  refine ⟨262133722761505678483013843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174755815174337118988675895 262133722761505678483013843)
  ·
    refine ⟨393200584142258517724520765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262133722761505678483013843 393200584142258517724520765)
    ·
      refine ⟨147450219053346944146695287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393200584142258517724520765 147450219053346944146695287)
      ·
        refine ⟨221175328580020416220042931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147450219053346944146695287 221175328580020416220042931)
        ·
          refine ⟨331762992870030624330064397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221175328580020416220042931 331762992870030624330064397)
          ·
            refine ⟨124411122326261484123774149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331762992870030624330064397 124411122326261484123774149)
            ·
              refine ⟨23327085436174028273207653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124411122326261484123774149 23327085436174028273207653)
              ·
                refine ⟨4373828519282630301226435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23327085436174028273207653 4373828519282630301226435)
                ·
                  refine ⟨6560742778923945451839653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373828519282630301226435 6560742778923945451839653)
                  ·
                    refine ⟨1230139271048239772219935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6560742778923945451839653 1230139271048239772219935)
                    ·
                      rfl

theorem cell23_7187063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_7187063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187063 prefixEnd_7187063 := by exact prefixLift 7187063
  have htrace : WordTrace (prefixWord ++ tailWord_7187063) baseStart_7187063 baseEnd_7187063 := by
    simpa [prefixWord, tailWord_7187063, baseEnd_7187063] using wordTrace_append hprefix tailTrace_7187063
  have hstable : (prefixWord ++ tailWord_7187063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187063).length < 2 ^ (prefixWord ++ tailWord_7187063).sum := by decide
  have hdescent : baseEnd_7187063 < baseStart_7187063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187079 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_7187079 : Nat := 118140960795 + 7187079 * 2 ^ 59
def prefixEnd_7187079 : Nat := 4983230072969 + 3 ^ 40 * 7187079 * 2
def baseEnd_7187079 : Nat := 3690426028835191254059731

theorem tailTrace_7187079 : CollatzResearch.WordTrace tailWord_7187079 prefixEnd_7187079 3690426028835191254059731 := by
  unfold tailWord_7187079
  simp only [CollatzResearch.WordTrace]
  refine ⟨262134306329447713215596291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174756204219631808810397527 262134306329447713215596291)
  ·
    refine ⟨393201459494171569823394437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262134306329447713215596291 393201459494171569823394437)
    ·
      refine ⟨73725273655157169341886457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393201459494171569823394437 73725273655157169341886457)
      ·
        refine ⟨55293955241367877006414843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73725273655157169341886457 55293955241367877006414843)
        ·
          refine ⟨82940932862051815509622265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55293955241367877006414843 82940932862051815509622265)
          ·
            refine ⟨62205699646538861632216699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82940932862051815509622265 62205699646538861632216699)
            ·
              refine ⟨93308549469808292448325049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62205699646538861632216699 93308549469808292448325049)
              ·
                refine ⟨69981412102356219336243787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93308549469808292448325049 69981412102356219336243787)
                ·
                  refine ⟨104972118153534329004365681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69981412102356219336243787 104972118153534329004365681)
                  ·
                    refine ⟨78729088615150746753274261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104972118153534329004365681 78729088615150746753274261)
                    ·
                      refine ⟨3690426028835191254059731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78729088615150746753274261 3690426028835191254059731)
                      ·
                        rfl

theorem cell23_7187079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_7187079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187079 prefixEnd_7187079 := by exact prefixLift 7187079
  have htrace : WordTrace (prefixWord ++ tailWord_7187079) baseStart_7187079 baseEnd_7187079 := by
    simpa [prefixWord, tailWord_7187079, baseEnd_7187079] using wordTrace_append hprefix tailTrace_7187079
  have hstable : (prefixWord ++ tailWord_7187079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187079).length < 2 ^ (prefixWord ++ tailWord_7187079).sum := by decide
  have hdescent : baseEnd_7187079 < baseStart_7187079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187086 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_7187086 : Nat := 118140960795 + 7187086 * 2 ^ 59
def prefixEnd_7187086 : Nat := 4983230072969 + 3 ^ 40 * 7187086 * 2
def baseEnd_7187086 : Nat := 3690429623199772726672199

theorem tailTrace_7187086 : CollatzResearch.WordTrace tailWord_7187086 prefixEnd_7187086 3690429623199772726672199 := by
  unfold tailWord_7187086
  simp only [CollatzResearch.WordTrace]
  refine ⟨32766820205052794176387639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174756374426948235607400741 32766820205052794176387639)
  ·
    refine ⟨49150230307579191264581459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32766820205052794176387639 49150230307579191264581459)
    ·
      refine ⟨73725345461368786896872189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49150230307579191264581459 73725345461368786896872189)
      ·
        refine ⟨27647004548013295086327071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73725345461368786896872189 27647004548013295086327071)
        ·
          refine ⟨41470506822019942629490607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27647004548013295086327071 41470506822019942629490607)
          ·
            refine ⟨62205760233029913944235911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41470506822019942629490607 62205760233029913944235911)
            ·
              refine ⟨93308640349544870916353867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62205760233029913944235911 93308640349544870916353867)
              ·
                refine ⟨139962960524317306374530801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93308640349544870916353867 139962960524317306374530801)
                ·
                  refine ⟨104972220393237979780898101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139962960524317306374530801 104972220393237979780898101)
                  ·
                    refine ⟨9841145661866060604459197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104972220393237979780898101 9841145661866060604459197)
                    ·
                      refine ⟨3690429623199772726672199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9841145661866060604459197 3690429623199772726672199)
                      ·
                        rfl

theorem cell23_7187086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_7187086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187086 prefixEnd_7187086 := by exact prefixLift 7187086
  have htrace : WordTrace (prefixWord ++ tailWord_7187086) baseStart_7187086 baseEnd_7187086 := by
    simpa [prefixWord, tailWord_7187086, baseEnd_7187086] using wordTrace_append hprefix tailTrace_7187086
  have hstable : (prefixWord ++ tailWord_7187086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187086).length < 2 ^ (prefixWord ++ tailWord_7187086).sum := by decide
  have hdescent : baseEnd_7187086 < baseStart_7187086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187089 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 7, 5]
def baseStart_7187089 : Nat := 118140960795 + 7187089 * 2 ^ 59
def prefixEnd_7187089 : Nat := 4983230072969 + 3 ^ 40 * 7187089 * 2
def baseEnd_7187089 : Nat := 1230143721213912071644895

theorem tailTrace_7187089 : CollatzResearch.WordTrace tailWord_7187089 prefixEnd_7187089 1230143721213912071644895 := by
  unfold tailWord_7187089
  simp only [CollatzResearch.WordTrace]
  refine ⟨262134671059411484923460321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174756447372940989948973547 262134671059411484923460321)
  ·
    refine ⟨196601003294558613692595241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262134671059411484923460321 196601003294558613692595241)
    ·
      refine ⟨147450752470918960269446431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196601003294558613692595241 147450752470918960269446431)
      ·
        refine ⟨221176128706378440404169647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147450752470918960269446431 221176128706378440404169647)
        ·
          refine ⟨331764193059567660606254471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221176128706378440404169647 331764193059567660606254471)
          ·
            refine ⟨497646289589351490909381707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331764193059567660606254471 497646289589351490909381707)
            ·
              refine ⟨746469434384027236364072561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497646289589351490909381707 746469434384027236364072561)
              ·
                refine ⟨559852075788020427273054421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746469434384027236364072561 559852075788020427273054421)
                ·
                  refine ⟨13121533026281728764212213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 559852075788020427273054421 13121533026281728764212213)
                  ·
                    refine ⟨1230143721213912071644895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13121533026281728764212213 1230143721213912071644895)
                    ·
                      rfl

theorem cell23_7187089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_7187089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187089 prefixEnd_7187089 := by exact prefixLift 7187089
  have htrace : WordTrace (prefixWord ++ tailWord_7187089) baseStart_7187089 baseEnd_7187089 := by
    simpa [prefixWord, tailWord_7187089, baseEnd_7187089] using wordTrace_append hprefix tailTrace_7187089
  have hstable : (prefixWord ++ tailWord_7187089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187089).length < 2 ^ (prefixWord ++ tailWord_7187089).sum := by decide
  have hdescent : baseEnd_7187089 < baseStart_7187089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187114 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7187114 : Nat := 118140960795 + 7187114 * 2 ^ 59
def prefixEnd_7187114 : Nat := 4983230072969 + 3 ^ 40 * 7187114 * 2
def baseEnd_7187114 : Nat := 1230148000219366205707357

theorem tailTrace_7187114 : CollatzResearch.WordTrace tailWord_7187114 prefixEnd_7187114 1230148000219366205707357 := by
  unfold tailWord_7187114
  simp only [CollatzResearch.WordTrace]
  refine ⟨65533895721080228548280099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174757055256213942795413597 65533895721080228548280099)
  ·
    refine ⟨98300843581620342822420149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65533895721080228548280099 98300843581620342822420149)
    ·
      refine ⟨9215704085776907139601889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98300843581620342822420149 9215704085776907139601889)
      ·
        refine ⟨6911778064332680354701417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9215704085776907139601889 6911778064332680354701417)
        ·
          refine ⟨5183833548249510266026063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6911778064332680354701417 5183833548249510266026063)
          ·
            refine ⟨7775750322374265399039095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183833548249510266026063 7775750322374265399039095)
            ·
              refine ⟨11663625483561398098558643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775750322374265399039095 11663625483561398098558643)
              ·
                refine ⟨17495438225342097147837965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11663625483561398098558643 17495438225342097147837965)
                ·
                  refine ⟨6560789334503286430439237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17495438225342097147837965 6560789334503286430439237)
                  ·
                    refine ⟨1230148000219366205707357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6560789334503286430439237 1230148000219366205707357)
                    ·
                      rfl

theorem cell23_7187114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7187114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187114 prefixEnd_7187114 := by exact prefixLift 7187114
  have htrace : WordTrace (prefixWord ++ tailWord_7187114) baseStart_7187114 baseEnd_7187114 := by
    simpa [prefixWord, tailWord_7187114, baseEnd_7187114] using wordTrace_append hprefix tailTrace_7187114
  have hstable : (prefixWord ++ tailWord_7187114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187114).length < 2 ^ (prefixWord ++ tailWord_7187114).sum := by decide
  have hdescent : baseEnd_7187114 < baseStart_7187114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187140 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_7187140 : Nat := 118140960795 + 7187140 * 2 ^ 59
def prefixEnd_7187140 : Nat := 4983230072969 + 3 ^ 40 * 7187140 * 2
def baseEnd_7187140 : Nat := 1230152450385038505132317

theorem tailTrace_7187140 : CollatzResearch.WordTrace tailWord_7187140 prefixEnd_7187140 1230152450385038505132317 := by
  unfold tailWord_7187140
  simp only [CollatzResearch.WordTrace]
  refine ⟨131068265591113360316783437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174757687454817813755711249 131068265591113360316783437)
  ·
    refine ⟨49150599596667510118793789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131068265591113360316783437 49150599596667510118793789)
    ·
      refine ⟨18431474848750316294547671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49150599596667510118793789 18431474848750316294547671)
      ·
        refine ⟨27647212273125474441821507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18431474848750316294547671 27647212273125474441821507)
        ·
          refine ⟨41470818409688211662732261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27647212273125474441821507 41470818409688211662732261)
          ·
            refine ⟨7775778451816539686762299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41470818409688211662732261 7775778451816539686762299)
            ·
              refine ⟨11663667677724809530143449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775778451816539686762299 11663667677724809530143449)
              ·
                refine ⟨8747750758293607147607587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11663667677724809530143449 8747750758293607147607587)
                ·
                  refine ⟨13121626137440410721411381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8747750758293607147607587 13121626137440410721411381)
                  ·
                    refine ⟨1230152450385038505132317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13121626137440410721411381 1230152450385038505132317)
                    ·
                      rfl

theorem cell23_7187140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_7187140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187140 prefixEnd_7187140 := by exact prefixLift 7187140
  have htrace : WordTrace (prefixWord ++ tailWord_7187140) baseStart_7187140 baseEnd_7187140 := by
    simpa [prefixWord, tailWord_7187140, baseEnd_7187140] using wordTrace_append hprefix tailTrace_7187140
  have hstable : (prefixWord ++ tailWord_7187140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187140).length < 2 ^ (prefixWord ++ tailWord_7187140).sum := by decide
  have hdescent : baseEnd_7187140 < baseStart_7187140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187157 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_7187157 : Nat := 118140960795 + 7187157 * 2 ^ 59
def prefixEnd_7187157 : Nat := 4983230072969 + 3 ^ 40 * 7187157 * 2
def baseEnd_7187157 : Nat := 1230155360108747316294791

theorem tailTrace_7187157 : CollatzResearch.WordTrace tailWord_7187157 prefixEnd_7187157 1230155360108747316294791 := by
  unfold tailWord_7187157
  simp only [CollatzResearch.WordTrace]
  refine ⟨262137151223165132536935725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174758100815443421691290483 262137151223165132536935725)
  ·
    refine ⟨98301431708686924701350897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262137151223165132536935725 98301431708686924701350897)
    ·
      refine ⟨73726073781515193526013173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98301431708686924701350897 73726073781515193526013173)
      ·
        refine ⟨6911819417017049393063735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73726073781515193526013173 6911819417017049393063735)
        ·
          refine ⟨10367729125525574089595603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911819417017049393063735 10367729125525574089595603)
          ·
            refine ⟨15551593688288361134393405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10367729125525574089595603 15551593688288361134393405)
            ·
              refine ⟨5831847633108135425397527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15551593688288361134393405 5831847633108135425397527)
              ·
                refine ⟨8747771449662203138096291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5831847633108135425397527 8747771449662203138096291)
                ·
                  refine ⟨13121657174493304707144437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8747771449662203138096291 13121657174493304707144437)
                  ·
                    refine ⟨1230155360108747316294791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13121657174493304707144437 1230155360108747316294791)
                    ·
                      rfl

theorem cell23_7187157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_7187157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187157 prefixEnd_7187157 := by exact prefixLift 7187157
  have htrace : WordTrace (prefixWord ++ tailWord_7187157) baseStart_7187157 baseEnd_7187157 := by
    simpa [prefixWord, tailWord_7187157, baseEnd_7187157] using wordTrace_append hprefix tailTrace_7187157
  have hstable : (prefixWord ++ tailWord_7187157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187157).length < 2 ^ (prefixWord ++ tailWord_7187157).sum := by decide
  have hdescent : baseEnd_7187157 < baseStart_7187157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187160 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 1, 1, 4]
def baseStart_7187160 : Nat := 118140960795 + 7187160 * 2 ^ 59
def prefixEnd_7187160 : Nat := 4983230072969 + 3 ^ 40 * 7187160 * 2
def baseEnd_7187160 : Nat := 3690467620768205437146859

theorem tailTrace_7187160 : CollatzResearch.WordTrace tailWord_7187160 prefixEnd_7187160 3690467620768205437146859 := by
  unfold tailWord_7187160
  simp only [CollatzResearch.WordTrace]
  refine ⟨131068630321077132024647467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174758173761436176032863289 131068630321077132024647467)
  ·
    refine ⟨196602945481615698036971201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131068630321077132024647467 196602945481615698036971201)
    ·
      refine ⟨147452209111211773527728401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196602945481615698036971201 147452209111211773527728401)
      ·
        refine ⟨110589156833408830145796301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147452209111211773527728401 110589156833408830145796301)
        ·
          refine ⟨41470933812528311304673613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110589156833408830145796301 41470933812528311304673613)
          ·
            refine ⟨15551600179698116739252605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41470933812528311304673613 15551600179698116739252605)
            ·
              refine ⟨5831850067386793777219727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15551600179698116739252605 5831850067386793777219727)
              ·
                refine ⟨8747775101080190665829591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5831850067386793777219727 8747775101080190665829591)
                ·
                  refine ⟨13121662651620285998744387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8747775101080190665829591 13121662651620285998744387)
                  ·
                    refine ⟨19682493977430428998116581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13121662651620285998744387 19682493977430428998116581)
                    ·
                      refine ⟨3690467620768205437146859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19682493977430428998116581 3690467620768205437146859)
                      ·
                        rfl

theorem cell23_7187160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_7187160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187160 prefixEnd_7187160 := by exact prefixLift 7187160
  have htrace : WordTrace (prefixWord ++ tailWord_7187160) baseStart_7187160 baseEnd_7187160 := by
    simpa [prefixWord, tailWord_7187160, baseEnd_7187160] using wordTrace_append hprefix tailTrace_7187160
  have hstable : (prefixWord ++ tailWord_7187160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187160).length < 2 ^ (prefixWord ++ tailWord_7187160).sum := by decide
  have hdescent : baseEnd_7187160 < baseStart_7187160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187226 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_7187226 : Nat := 118140960795 + 7187226 * 2 ^ 59
def prefixEnd_7187226 : Nat := 4983230072969 + 3 ^ 40 * 7187226 * 2
def baseEnd_7187226 : Nat := 1230167170163800726307185

theorem tailTrace_7187226 : CollatzResearch.WordTrace tailWord_7187226 prefixEnd_7187226 1230167170163800726307185 := by
  unfold tailWord_7187226
  simp only [CollatzResearch.WordTrace]
  refine ⟨65534916964978789330299383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174759778573276771547465021 65534916964978789330299383)
  ·
    refine ⟨98302375447468183995449075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65534916964978789330299383 98302375447468183995449075)
    ·
      refine ⟨147453563171202275993173613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98302375447468183995449075 147453563171202275993173613)
      ·
        refine ⟨55295086189200853497440105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147453563171202275993173613 55295086189200853497440105)
        ·
          refine ⟨41471314641900640123080079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55295086189200853497440105 41471314641900640123080079)
          ·
            refine ⟨62206971962850960184620119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41471314641900640123080079 62206971962850960184620119)
            ·
              refine ⟨93310457944276440276930179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62206971962850960184620119 93310457944276440276930179)
              ·
                refine ⟨139965686916414660415395269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93310457944276440276930179 139965686916414660415395269)
                ·
                  refine ⟨26243566296827748827886613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139965686916414660415395269 26243566296827748827886613)
                  ·
                    refine ⟨1230167170163800726307185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26243566296827748827886613 1230167170163800726307185)
                    ·
                      rfl

theorem cell23_7187226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_7187226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187226 prefixEnd_7187226 := by exact prefixLift 7187226
  have htrace : WordTrace (prefixWord ++ tailWord_7187226) baseStart_7187226 baseEnd_7187226 := by
    simpa [prefixWord, tailWord_7187226, baseEnd_7187226] using wordTrace_append hprefix tailTrace_7187226
  have hstable : (prefixWord ++ tailWord_7187226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187226).length < 2 ^ (prefixWord ++ tailWord_7187226).sum := by decide
  have hdescent : baseEnd_7187226 < baseStart_7187226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187256 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 7]
def baseStart_7187256 : Nat := 118140960795 + 7187256 * 2 ^ 59
def prefixEnd_7187256 : Nat := 4983230072969 + 3 ^ 40 * 7187256 * 2
def baseEnd_7187256 : Nat := 410057434990115229060713

theorem tailTrace_7187256 : CollatzResearch.WordTrace tailWord_7187256 prefixEnd_7187256 410057434990115229060713 := by
  unfold tailWord_7187256
  simp only [CollatzResearch.WordTrace]
  refine ⟨131070381024903236222394811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174760508033204314963193081 131070381024903236222394811)
  ·
    refine ⟨196605571537354854333592217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131070381024903236222394811 196605571537354854333592217)
    ·
      refine ⟨147454178653016140750194163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196605571537354854333592217 147454178653016140750194163)
      ·
        refine ⟨221181267979524211125291245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147454178653016140750194163 221181267979524211125291245)
        ·
          refine ⟨82942975492321579171984217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221181267979524211125291245 82942975492321579171984217)
          ·
            refine ⟨62207231619241184378988163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82942975492321579171984217 62207231619241184378988163)
            ·
              refine ⟨93310847428861776568482245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62207231619241184378988163 93310847428861776568482245)
              ·
                refine ⟨17495783892911583106590421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93310847428861776568482245 17495783892911583106590421)
                ·
                  refine ⟨410057434990115229060713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17495783892911583106590421 410057434990115229060713)
                  ·
                    rfl

theorem cell23_7187256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 7].length) (baseStart_7187256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187256 prefixEnd_7187256 := by exact prefixLift 7187256
  have htrace : WordTrace (prefixWord ++ tailWord_7187256) baseStart_7187256 baseEnd_7187256 := by
    simpa [prefixWord, tailWord_7187256, baseEnd_7187256] using wordTrace_append hprefix tailTrace_7187256
  have hstable : (prefixWord ++ tailWord_7187256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187256).length < 2 ^ (prefixWord ++ tailWord_7187256).sum := by decide
  have hdescent : baseEnd_7187256 < baseStart_7187256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187323 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 4]
def baseStart_7187323 : Nat := 118140960795 + 7187323 * 2 ^ 59
def prefixEnd_7187323 : Nat := 4983230072969 + 3 ^ 40 * 7187323 * 2
def baseEnd_7187323 : Nat := 3690551318114888299408609

theorem tailTrace_7187323 : CollatzResearch.WordTrace tailWord_7187323 prefixEnd_7187323 3690551318114888299408609 := by
  unfold tailWord_7187323
  simp only [CollatzResearch.WordTrace]
  refine ⟨262143205740563742887478623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174762137160375828591652415 262143205740563742887478623)
  ·
    refine ⟨393214808610845614331217935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262143205740563742887478623 393214808610845614331217935)
    ·
      refine ⟨589822212916268421496826903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393214808610845614331217935 589822212916268421496826903)
      ·
        refine ⟨884733319374402632245240355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589822212916268421496826903 884733319374402632245240355)
        ·
          refine ⟨1327099979061603948367860533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884733319374402632245240355 1327099979061603948367860533)
          ·
            refine ⟨124415623037025370159486925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1327099979061603948367860533 124415623037025370159486925)
            ·
              refine ⟨46655858638884513809807597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124415623037025370159486925 46655858638884513809807597)
              ·
                refine ⟨17495946989581692678677849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46655858638884513809807597 17495946989581692678677849)
                ·
                  refine ⟨13121960242186269509008387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17495946989581692678677849 13121960242186269509008387)
                  ·
                    refine ⟨19682940363279404263512581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13121960242186269509008387 19682940363279404263512581)
                    ·
                      refine ⟨3690551318114888299408609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19682940363279404263512581 3690551318114888299408609)
                      ·
                        rfl

theorem cell23_7187323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 4].length) (baseStart_7187323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187323 prefixEnd_7187323 := by exact prefixLift 7187323
  have htrace : WordTrace (prefixWord ++ tailWord_7187323) baseStart_7187323 baseEnd_7187323 := by
    simpa [prefixWord, tailWord_7187323, baseEnd_7187323] using wordTrace_append hprefix tailTrace_7187323
  have hstable : (prefixWord ++ tailWord_7187323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187323).length < 2 ^ (prefixWord ++ tailWord_7187323).sum := by decide
  have hdescent : baseEnd_7187323 < baseStart_7187323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187363 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 6]
def baseStart_7187363 : Nat := 118140960795 + 7187363 * 2 ^ 59
def prefixEnd_7187363 : Nat := 4983230072969 + 3 ^ 40 * 7187363 * 2
def baseEnd_7187363 : Nat := 410063539704563126989825

theorem tailTrace_7187363 : CollatzResearch.WordTrace tailWord_7187363 prefixEnd_7187363 410063539704563126989825 := by
  unfold tailWord_7187363
  simp only [CollatzResearch.WordTrace]
  refine ⟨262144664660418829718934743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174763109773612553145956495 262144664660418829718934743)
  ·
    refine ⟨393216996990628244578402115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262144664660418829718934743 393216996990628244578402115)
    ·
      refine ⟨589825495485942366867603173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393216996990628244578402115 589825495485942366867603173)
      ·
        refine ⟨110592280403614193787675595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 589825495485942366867603173 110592280403614193787675595)
        ·
          refine ⟨165888420605421290681513393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110592280403614193787675595 165888420605421290681513393)
          ·
            refine ⟨124416315454065968011135045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165888420605421290681513393 124416315454065968011135045)
            ·
              refine ⟨23328059147637369002087821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124416315454065968011135045 23328059147637369002087821)
              ·
                refine ⟨8748022180364013375782933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23328059147637369002087821 8748022180364013375782933)
                ·
                  refine ⟨410063539704563126989825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8748022180364013375782933 410063539704563126989825)
                  ·
                    rfl

theorem cell23_7187363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 6].length) (baseStart_7187363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187363 prefixEnd_7187363 := by exact prefixLift 7187363
  have htrace : WordTrace (prefixWord ++ tailWord_7187363) baseStart_7187363 baseEnd_7187363 := by
    simpa [prefixWord, tailWord_7187363, baseEnd_7187363] using wordTrace_append hprefix tailTrace_7187363
  have hstable : (prefixWord ++ tailWord_7187363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187363).length < 2 ^ (prefixWord ++ tailWord_7187363).sum := by decide
  have hdescent : baseEnd_7187363 < baseStart_7187363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187367 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 3, 4]
def baseStart_7187367 : Nat := 118140960795 + 7187367 * 2 ^ 59
def prefixEnd_7187367 : Nat := 4983230072969 + 3 ^ 40 * 7187367 * 2
def baseEnd_7187367 : Nat := 1230191303754562042419469

theorem tailTrace_7187367 : CollatzResearch.WordTrace tailWord_7187367 prefixEnd_7187367 1230191303754562042419469 := by
  unfold tailWord_7187367
  simp only [CollatzResearch.WordTrace]
  refine ⟨262144810552404338402080355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174763207034936225601386903 262144810552404338402080355)
  ·
    refine ⟨393217215828606507603120533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262144810552404338402080355 393217215828606507603120533)
    ·
      refine ⟨18432056991965930043896275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 393217215828606507603120533 18432056991965930043896275)
      ·
        refine ⟨27648085487948895065844413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18432056991965930043896275 27648085487948895065844413)
        ·
          refine ⟨10368032057980835649691655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27648085487948895065844413 10368032057980835649691655)
          ·
            refine ⟨15552048086971253474537483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10368032057980835649691655 15552048086971253474537483)
            ·
              refine ⟨23328072130456880211806225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15552048086971253474537483 23328072130456880211806225)
              ·
                refine ⟨17496054097842660158854669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23328072130456880211806225 17496054097842660158854669)
                ·
                  refine ⟨6561020286690997559570501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17496054097842660158854669 6561020286690997559570501)
                  ·
                    refine ⟨1230191303754562042419469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6561020286690997559570501 1230191303754562042419469)
                    ·
                      rfl

theorem cell23_7187367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_7187367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187367 prefixEnd_7187367 := by exact prefixLift 7187367
  have htrace : WordTrace (prefixWord ++ tailWord_7187367) baseStart_7187367 baseEnd_7187367 := by
    simpa [prefixWord, tailWord_7187367, baseEnd_7187367] using wordTrace_append hprefix tailTrace_7187367
  have hstable : (prefixWord ++ tailWord_7187367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187367).length < 2 ^ (prefixWord ++ tailWord_7187367).sum := by decide
  have hdescent : baseEnd_7187367 < baseStart_7187367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187407 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 3]
def baseStart_7187407 : Nat := 118140960795 + 7187407 * 2 ^ 59
def prefixEnd_7187407 : Nat := 4983230072969 + 3 ^ 40 * 7187407 * 2
def baseEnd_7187407 : Nat := 3690594450489865970758223

theorem tailTrace_7187407 : CollatzResearch.WordTrace tailWord_7187407 prefixEnd_7187407 3690594450489865970758223 := by
  unfold tailWord_7187407
  simp only [CollatzResearch.WordTrace]
  refine ⟨262146269472259425233536475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174764179648172950155690983 262146269472259425233536475)
  ·
    refine ⟨393219404208389137850304713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262146269472259425233536475 393219404208389137850304713)
    ·
      refine ⟨294914553156291853387728535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393219404208389137850304713 294914553156291853387728535)
      ·
        refine ⟨442371829734437780081592803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294914553156291853387728535 442371829734437780081592803)
        ·
          refine ⟨663557744601656670122389205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442371829734437780081592803 663557744601656670122389205)
          ·
            refine ⟨15552134639101328205993497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 663557744601656670122389205 15552134639101328205993497)
            ·
              refine ⟨11664100979325996154495123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15552134639101328205993497 11664100979325996154495123)
              ·
                refine ⟨17496151468988994231742685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11664100979325996154495123 17496151468988994231742685)
                ·
                  refine ⟨6561056800870872836903507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17496151468988994231742685 6561056800870872836903507)
                  ·
                    refine ⟨9841585201306309255355261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6561056800870872836903507 9841585201306309255355261)
                    ·
                      refine ⟨3690594450489865970758223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9841585201306309255355261 3690594450489865970758223)
                      ·
                        rfl

theorem cell23_7187407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 3].length) (baseStart_7187407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187407 prefixEnd_7187407 := by exact prefixLift 7187407
  have htrace : WordTrace (prefixWord ++ tailWord_7187407) baseStart_7187407 baseEnd_7187407 := by
    simpa [prefixWord, tailWord_7187407, baseEnd_7187407] using wordTrace_append hprefix tailTrace_7187407
  have hstable : (prefixWord ++ tailWord_7187407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187407).length < 2 ^ (prefixWord ++ tailWord_7187407).sum := by decide
  have hdescent : baseEnd_7187407 < baseStart_7187407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187414 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_7187414 : Nat := 118140960795 + 7187414 * 2 ^ 59
def prefixEnd_7187414 : Nat := 4983230072969 + 3 ^ 40 * 7187414 * 2
def baseEnd_7187414 : Nat := 410066449428271938152299

theorem tailTrace_7187414 : CollatzResearch.WordTrace tailWord_7187414 prefixEnd_7187414 410066449428271938152299 := by
  unfold tailWord_7187414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16384157798952129089315081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174764349855489376952694197 16384157798952129089315081)
  ·
    refine ⟨12288118349214096816986311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16384157798952129089315081 12288118349214096816986311)
    ·
      refine ⟨18432177523821145225479467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12288118349214096816986311 18432177523821145225479467)
      ·
        refine ⟨27648266285731717838219201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18432177523821145225479467 27648266285731717838219201)
        ·
          refine ⟨20736199714298788378664401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27648266285731717838219201 20736199714298788378664401)
          ·
            refine ⟨15552149785724091283998301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20736199714298788378664401 15552149785724091283998301)
            ·
              refine ⟨5832056169646534231499363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15552149785724091283998301 5832056169646534231499363)
              ·
                refine ⟨8748084254469801347249045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832056169646534231499363 8748084254469801347249045)
                ·
                  refine ⟨410066449428271938152299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8748084254469801347249045 410066449428271938152299)
                  ·
                    rfl

theorem cell23_7187414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_7187414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187414 prefixEnd_7187414 := by exact prefixLift 7187414
  have htrace : WordTrace (prefixWord ++ tailWord_7187414) baseStart_7187414 baseEnd_7187414 := by
    simpa [prefixWord, tailWord_7187414, baseEnd_7187414] using wordTrace_append hprefix tailTrace_7187414
  have hstable : (prefixWord ++ tailWord_7187414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187414).length < 2 ^ (prefixWord ++ tailWord_7187414).sum := by decide
  have hdescent : baseEnd_7187414 < baseStart_7187414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187433 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 3]
def baseStart_7187433 : Nat := 118140960795 + 7187433 * 2 ^ 59
def prefixEnd_7187433 : Nat := 4983230072969 + 3 ^ 40 * 7187433 * 2
def baseEnd_7187433 : Nat := 3690607800986882869033103

theorem tailTrace_7187433 : CollatzResearch.WordTrace tailWord_7187433 prefixEnd_7187433 3690607800986882869033103 := by
  unfold tailWord_7187433
  simp only [CollatzResearch.WordTrace]
  refine ⟨262147217770165231673982953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174764811846776821115988635 262147217770165231673982953)
  ·
    refine ⟨196610413327623923755487215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262147217770165231673982953 196610413327623923755487215)
    ·
      refine ⟨294915619991435885633230823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196610413327623923755487215 294915619991435885633230823)
      ·
        refine ⟨442373429987153828449846235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294915619991435885633230823 442373429987153828449846235)
        ·
          refine ⟨663560144980730742674769353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442373429987153828449846235 663560144980730742674769353)
          ·
            refine ⟨497670108735548057006077015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663560144980730742674769353 497670108735548057006077015)
            ·
              refine ⟨746505163103322085509115523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497670108735548057006077015 746505163103322085509115523)
              ·
                refine ⟨1119757744654983128263673285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746505163103322085509115523 1119757744654983128263673285)
                ·
                  refine ⟨209954577122809336549438741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119757744654983128263673285 209954577122809336549438741)
                  ·
                    refine ⟨9841620802631687650754941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 209954577122809336549438741 9841620802631687650754941)
                    ·
                      refine ⟨3690607800986882869033103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9841620802631687650754941 3690607800986882869033103)
                      ·
                        rfl

theorem cell23_7187433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_7187433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187433 prefixEnd_7187433 := by exact prefixLift 7187433
  have htrace : WordTrace (prefixWord ++ tailWord_7187433) baseStart_7187433 baseEnd_7187433 := by
    simpa [prefixWord, tailWord_7187433, baseEnd_7187433] using wordTrace_append hprefix tailTrace_7187433
  have hstable : (prefixWord ++ tailWord_7187433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187433).length < 2 ^ (prefixWord ++ tailWord_7187433).sum := by decide
  have hdescent : baseEnd_7187433 < baseStart_7187433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187441 : List Nat := [1, 2, 2, 2, 4, 3, 1, 3, 1, 1, 3]
def baseStart_7187441 : Nat := 118140960795 + 7187441 * 2 ^ 59
def prefixEnd_7187441 : Nat := 4983230072969 + 3 ^ 40 * 7187441 * 2
def baseEnd_7187441 : Nat := 3690611908832118837733067

theorem tailTrace_7187441 : CollatzResearch.WordTrace tailWord_7187441 prefixEnd_7187441 3690611908832118837733067 := by
  unfold tailWord_7187441
  simp only [CollatzResearch.WordTrace]
  refine ⟨262147509554136249040274177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174765006369424166026849451 262147509554136249040274177)
  ·
    refine ⟨196610632165602186780205633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262147509554136249040274177 196610632165602186780205633)
    ·
      refine ⟨147457974124201640085154225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196610632165602186780205633 147457974124201640085154225)
      ·
        refine ⟨110593480593151230063865669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147457974124201640085154225 110593480593151230063865669)
        ·
          refine ⟨20736277611215855636974813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110593480593151230063865669 20736277611215855636974813)
          ·
            refine ⟨7776104104205945863865555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20736277611215855636974813 7776104104205945863865555)
            ·
              refine ⟨11664156156308918795798333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7776104104205945863865555 11664156156308918795798333)
              ·
                refine ⟨4374058558615844548424375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11664156156308918795798333 4374058558615844548424375)
                ·
                  refine ⟨6561087837923766822636563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4374058558615844548424375 6561087837923766822636563)
                  ·
                    refine ⟨9841631756885650233954845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6561087837923766822636563 9841631756885650233954845)
                    ·
                      refine ⟨3690611908832118837733067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9841631756885650233954845 3690611908832118837733067)
                      ·
                        rfl

theorem cell23_7187441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_7187441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187441 prefixEnd_7187441 := by exact prefixLift 7187441
  have htrace : WordTrace (prefixWord ++ tailWord_7187441) baseStart_7187441 baseEnd_7187441 := by
    simpa [prefixWord, tailWord_7187441, baseEnd_7187441] using wordTrace_append hprefix tailTrace_7187441
  have hstable : (prefixWord ++ tailWord_7187441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187441).length < 2 ^ (prefixWord ++ tailWord_7187441).sum := by decide
  have hdescent : baseEnd_7187441 < baseStart_7187441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187458 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7187458 : Nat := 118140960795 + 7187458 * 2 ^ 59
def prefixEnd_7187458 : Nat := 4983230072969 + 3 ^ 40 * 7187458 * 2
def baseEnd_7187458 : Nat := 3690620638003245271220489

theorem tailTrace_7187458 : CollatzResearch.WordTrace tailWord_7187458 prefixEnd_7187458 3690620638003245271220489 := by
  unfold tailWord_7187458
  simp only [CollatzResearch.WordTrace]
  refine ⟨65537032398768665235910757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174765419730049773962428685 65537032398768665235910757)
  ·
    refine ⟨12288193574769124731733267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65537032398768665235910757 12288193574769124731733267)
    ·
      refine ⟨18432290362153687097599901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12288193574769124731733267 18432290362153687097599901)
      ·
        refine ⟨6912108885807632661599963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18432290362153687097599901 6912108885807632661599963)
        ·
          refine ⟨10368163328711448992399945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6912108885807632661599963 10368163328711448992399945)
          ·
            refine ⟨7776122496533586744299959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10368163328711448992399945 7776122496533586744299959)
            ·
              refine ⟨11664183744800380116449939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7776122496533586744299959 11664183744800380116449939)
              ·
                refine ⟨17496275617200570174674909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11664183744800380116449939 17496275617200570174674909)
                ·
                  refine ⟨6561103356450213815503091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17496275617200570174674909 6561103356450213815503091)
                  ·
                    refine ⟨9841655034675320723254637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6561103356450213815503091 9841655034675320723254637)
                    ·
                      refine ⟨3690620638003245271220489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9841655034675320723254637 3690620638003245271220489)
                      ·
                        rfl

theorem cell23_7187458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7187458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187458 prefixEnd_7187458 := by exact prefixLift 7187458
  have htrace : WordTrace (prefixWord ++ tailWord_7187458) baseStart_7187458 baseEnd_7187458 := by
    simpa [prefixWord, tailWord_7187458, baseEnd_7187458] using wordTrace_append hprefix tailTrace_7187458
  have hstable : (prefixWord ++ tailWord_7187458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187458).length < 2 ^ (prefixWord ++ tailWord_7187458).sum := by decide
  have hdescent : baseEnd_7187458 < baseStart_7187458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187464 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_7187464 : Nat := 118140960795 + 7187464 * 2 ^ 59
def prefixEnd_7187464 : Nat := 4983230072969 + 3 ^ 40 * 7187464 * 2
def baseEnd_7187464 : Nat := 3690623718887172247745461

theorem tailTrace_7187464 : CollatzResearch.WordTrace tailWord_7187464 prefixEnd_7187464 3690623718887172247745461 := by
  unfold tailWord_7187464
  simp only [CollatzResearch.WordTrace]
  refine ⟨131074174216526461984180723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174765565622035282645574297 131074174216526461984180723)
  ·
    refine ⟨196611261324789692976271085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131074174216526461984180723 196611261324789692976271085)
    ·
      refine ⟨73729222996796134866101657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196611261324789692976271085 73729222996796134866101657)
      ·
        refine ⟨55296917247597101149576243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73729222996796134866101657 55296917247597101149576243)
        ·
          refine ⟨82945375871395651724364365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55296917247597101149576243 82945375871395651724364365)
          ·
            refine ⟨31104515951773369396636637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82945375871395651724364365 31104515951773369396636637)
            ·
              refine ⟨11664193481915013523738739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31104515951773369396636637 11664193481915013523738739)
              ·
                refine ⟨17496290222872520285608109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11664193481915013523738739 17496290222872520285608109)
                ·
                  refine ⟨6561108833577195107103041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17496290222872520285608109 6561108833577195107103041)
                  ·
                    refine ⟨4920831625182896330327281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6561108833577195107103041 4920831625182896330327281)
                    ·
                      refine ⟨3690623718887172247745461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920831625182896330327281 3690623718887172247745461)
                      ·
                        rfl

theorem cell23_7187464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_7187464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187464 prefixEnd_7187464 := by exact prefixLift 7187464
  have htrace : WordTrace (prefixWord ++ tailWord_7187464) baseStart_7187464 baseEnd_7187464 := by
    simpa [prefixWord, tailWord_7187464, baseEnd_7187464] using wordTrace_append hprefix tailTrace_7187464
  have hstable : (prefixWord ++ tailWord_7187464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187464).length < 2 ^ (prefixWord ++ tailWord_7187464).sum := by decide
  have hdescent : baseEnd_7187464 < baseStart_7187464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187470 : List Nat := [4, 1, 1, 2, 2, 3, 2, 8]
def baseStart_7187470 : Nat := 118140960795 + 7187470 * 2 ^ 59
def prefixEnd_7187470 : Nat := 4983230072969 + 3 ^ 40 * 7187470 * 2
def baseEnd_7187470 : Nat := 136689881473003674972979

theorem tailTrace_7187470 : CollatzResearch.WordTrace tailWord_7187470 prefixEnd_7187470 136689881473003674972979 := by
  unfold tailWord_7187470
  simp only [CollatzResearch.WordTrace]
  refine ⟨32768570908878898374134983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174765711514020791328719909 32768570908878898374134983)
  ·
    refine ⟨49152856363318347561202475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32768570908878898374134983 49152856363318347561202475)
    ·
      refine ⟨73729284544977521341803713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49152856363318347561202475 73729284544977521341803713)
      ·
        refine ⟨55296963408733141006352785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73729284544977521341803713 55296963408733141006352785)
        ·
          refine ⟨41472722556549855754764589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55296963408733141006352785 41472722556549855754764589)
          ·
            refine ⟨15552270958706195908036721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41472722556549855754764589 15552270958706195908036721)
            ·
              refine ⟨11664203219029646931027541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15552270958706195908036721 11664203219029646931027541)
              ·
                refine ⟨136689881473003674972979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11664203219029646931027541 136689881473003674972979)
                ·
                  rfl

theorem cell23_7187470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_7187470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187470 prefixEnd_7187470 := by exact prefixLift 7187470
  have htrace : WordTrace (prefixWord ++ tailWord_7187470) baseStart_7187470 baseEnd_7187470 := by
    simpa [prefixWord, tailWord_7187470, baseEnd_7187470] using wordTrace_append hprefix tailTrace_7187470
  have hstable : (prefixWord ++ tailWord_7187470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187470).length < 2 ^ (prefixWord ++ tailWord_7187470).sum := by decide
  have hdescent : baseEnd_7187470 < baseStart_7187470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187537 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 1, 4, 2]
def baseStart_7187537 : Nat := 118140960795 + 7187537 * 2 ^ 59
def prefixEnd_7187537 : Nat := 4983230072969 + 3 ^ 40 * 7187537 * 2
def baseEnd_7187537 : Nat := 3690661202974950462132625

theorem tailTrace_7187537 : CollatzResearch.WordTrace tailWord_7187537 prefixEnd_7187537 3690661202974950462132625 := by
  unfold tailWord_7187537
  simp only [CollatzResearch.WordTrace]
  refine ⟨262151010961788457435768865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174767340641192304957179243 262151010961788457435768865)
  ·
    refine ⟨196613258221341343076826649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262151010961788457435768865 196613258221341343076826649)
    ·
      refine ⟨147459943666006007307619987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196613258221341343076826649 147459943666006007307619987)
      ·
        refine ⟨221189915499009010961429981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147459943666006007307619987 221189915499009010961429981)
        ·
          refine ⟨82946218312128379110536243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221189915499009010961429981 82946218312128379110536243)
          ·
            refine ⟨124419327468192568665804365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82946218312128379110536243 124419327468192568665804365)
            ·
              refine ⟨46657247800572213249676637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124419327468192568665804365 46657247800572213249676637)
              ·
                refine ⟨17496467925214579968628739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46657247800572213249676637 17496467925214579968628739)
                ·
                  refine ⟨26244701887821869952943109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17496467925214579968628739 26244701887821869952943109)
                  ·
                    refine ⟨4920881603966600616176833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26244701887821869952943109 4920881603966600616176833)
                    ·
                      refine ⟨3690661202974950462132625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920881603966600616176833 3690661202974950462132625)
                      ·
                        rfl

theorem cell23_7187537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_7187537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187537 prefixEnd_7187537 := by exact prefixLift 7187537
  have htrace : WordTrace (prefixWord ++ tailWord_7187537) baseStart_7187537 baseEnd_7187537 := by
    simpa [prefixWord, tailWord_7187537, baseEnd_7187537] using wordTrace_append hprefix tailTrace_7187537
  have hstable : (prefixWord ++ tailWord_7187537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187537).length < 2 ^ (prefixWord ++ tailWord_7187537).sum := by decide
  have hdescent : baseEnd_7187537 < baseStart_7187537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187540 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_7187540 : Nat := 118140960795 + 7187540 * 2 ^ 59
def prefixEnd_7187540 : Nat := 4983230072969 + 3 ^ 40 * 7187540 * 2
def baseEnd_7187540 : Nat := 3690662743416913950395111

theorem tailTrace_7187540 : CollatzResearch.WordTrace tailWord_7187540 prefixEnd_7187540 3690662743416913950395111 := by
  unfold tailWord_7187540
  simp only [CollatzResearch.WordTrace]
  refine ⟨131075560190388794474064037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174767413587185059298752049 131075560190388794474064037)
  ·
    refine ⟨24576667535697898963887007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131075560190388794474064037 24576667535697898963887007)
    ·
      refine ⟨36865001303546848445830511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24576667535697898963887007 36865001303546848445830511)
      ·
        refine ⟨55297501955320272668745767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36865001303546848445830511 55297501955320272668745767)
        ·
          refine ⟨82946252932980409003118651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55297501955320272668745767 82946252932980409003118651)
          ·
            refine ⟨124419379399470613504677977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82946252932980409003118651 124419379399470613504677977)
            ·
              refine ⟨93314534549602960128508483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124419379399470613504677977 93314534549602960128508483)
              ·
                refine ⟨139971801824404440192762725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93314534549602960128508483 139971801824404440192762725)
                ·
                  refine ⟨26244712842075832536143011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139971801824404440192762725 26244712842075832536143011)
                  ·
                    refine ⟨39367069263113748804214517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26244712842075832536143011 39367069263113748804214517)
                    ·
                      refine ⟨3690662743416913950395111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39367069263113748804214517 3690662743416913950395111)
                      ·
                        rfl

theorem cell23_7187540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_7187540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187540 prefixEnd_7187540 := by exact prefixLift 7187540
  have htrace : WordTrace (prefixWord ++ tailWord_7187540) baseStart_7187540 baseEnd_7187540 := by
    simpa [prefixWord, tailWord_7187540, baseEnd_7187540] using wordTrace_append hprefix tailTrace_7187540
  have hstable : (prefixWord ++ tailWord_7187540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187540).length < 2 ^ (prefixWord ++ tailWord_7187540).sum := by decide
  have hdescent : baseEnd_7187540 < baseStart_7187540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187577 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 7]
def baseStart_7187577 : Nat := 118140960795 + 7187577 * 2 ^ 59
def prefixEnd_7187577 : Nat := 4983230072969 + 3 ^ 40 * 7187577 * 2
def baseEnd_7187577 : Nat := 410075749133458922848049

theorem tailTrace_7187577 : CollatzResearch.WordTrace tailWord_7187577 prefixEnd_7187577 410075749133458922848049 := by
  unfold tailWord_7187577
  simp only [CollatzResearch.WordTrace]
  refine ⟨262152469881643544267224985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174768313254429029511483323 262152469881643544267224985)
  ·
    refine ⟨196614352411232658200418739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262152469881643544267224985 196614352411232658200418739)
    ·
      refine ⟨294921528616848987300628109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196614352411232658200418739 294921528616848987300628109)
      ·
        refine ⟨110595573231318370237735541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294921528616848987300628109 110595573231318370237735541)
        ·
          refine ⟨10368334990436097209787707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110595573231318370237735541 10368334990436097209787707)
          ·
            refine ⟨15552502485654145814681561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10368334990436097209787707 15552502485654145814681561)
            ·
              refine ⟨11664376864240609361011171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15552502485654145814681561 11664376864240609361011171)
              ·
                refine ⟨17496565296360914041516757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11664376864240609361011171 17496565296360914041516757)
                ·
                  refine ⟨410075749133458922848049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17496565296360914041516757 410075749133458922848049)
                  ·
                    rfl

theorem cell23_7187577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 7].length) (baseStart_7187577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187577 prefixEnd_7187577 := by exact prefixLift 7187577
  have htrace : WordTrace (prefixWord ++ tailWord_7187577) baseStart_7187577 baseEnd_7187577 := by
    simpa [prefixWord, tailWord_7187577, baseEnd_7187577] using wordTrace_append hprefix tailTrace_7187577
  have hstable : (prefixWord ++ tailWord_7187577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187577).length < 2 ^ (prefixWord ++ tailWord_7187577).sum := by decide
  have hdescent : baseEnd_7187577 < baseStart_7187577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187582 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7187582 : Nat := 118140960795 + 7187582 * 2 ^ 59
def prefixEnd_7187582 : Nat := 4983230072969 + 3 ^ 40 * 7187582 * 2
def baseEnd_7187582 : Nat := 3690684309604402786069919

theorem tailTrace_7187582 : CollatzResearch.WordTrace tailWord_7187582 prefixEnd_7187582 3690684309604402786069919 := by
  unfold tailWord_7187582
  simp only [CollatzResearch.WordTrace]
  refine ⟨32769081530828178765144625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174768434831083620080771333 32769081530828178765144625)
  ·
    refine ⟨24576811148121134073858469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32769081530828178765144625 24576811148121134073858469)
    ·
      refine ⟨4608152090272712638848463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24576811148121134073858469 4608152090272712638848463)
      ·
        refine ⟨6912228135409068958272695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4608152090272712638848463 6912228135409068958272695)
        ·
          refine ⟨10368342203113603437409043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6912228135409068958272695 10368342203113603437409043)
          ·
            refine ⟨15552513304670405156113565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10368342203113603437409043 15552513304670405156113565)
            ·
              refine ⟨5832192489251401933542587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15552513304670405156113565 5832192489251401933542587)
              ·
                refine ⟨8748288733877102900313881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832192489251401933542587 8748288733877102900313881)
                ·
                  refine ⟨6561216550407827175235411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8748288733877102900313881 6561216550407827175235411)
                  ·
                    refine ⟨9841824825611740762853117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6561216550407827175235411 9841824825611740762853117)
                    ·
                      refine ⟨3690684309604402786069919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9841824825611740762853117 3690684309604402786069919)
                      ·
                        rfl

theorem cell23_7187582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7187582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187582 prefixEnd_7187582 := by exact prefixLift 7187582
  have htrace : WordTrace (prefixWord ++ tailWord_7187582) baseStart_7187582 baseEnd_7187582 := by
    simpa [prefixWord, tailWord_7187582, baseEnd_7187582] using wordTrace_append hprefix tailTrace_7187582
  have hstable : (prefixWord ++ tailWord_7187582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187582).length < 2 ^ (prefixWord ++ tailWord_7187582).sum := by decide
  have hdescent : baseEnd_7187582 < baseStart_7187582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187588 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_7187588 : Nat := 118140960795 + 7187588 * 2 ^ 59
def prefixEnd_7187588 : Nat := 4983230072969 + 3 ^ 40 * 7187588 * 2
def baseEnd_7187588 : Nat := 3690687390488329762594891

theorem tailTrace_7187588 : CollatzResearch.WordTrace tailWord_7187588 prefixEnd_7187588 3690687390488329762594891 := by
  unfold tailWord_7187588
  simp only [CollatzResearch.WordTrace]
  refine ⟨131076435542301846572937709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174768580723069128763916945 131076435542301846572937709)
  ·
    refine ⟨49153663328363192464851641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131076435542301846572937709 49153663328363192464851641)
    ·
      refine ⟨36865247496272394348638731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49153663328363192464851641 36865247496272394348638731)
      ·
        refine ⟨55297871244408591522958097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36865247496272394348638731 55297871244408591522958097)
        ·
          refine ⟨41473403433306443642218573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55297871244408591522958097 41473403433306443642218573)
          ·
            refine ⟨15552526287489916365831965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41473403433306443642218573 15552526287489916365831965)
            ·
              refine ⟨5832197357808718637186987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15552526287489916365831965 5832197357808718637186987)
              ·
                refine ⟨8748296036713077955780481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832197357808718637186987 8748296036713077955780481)
                ·
                  refine ⟨6561222027534808466835361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8748296036713077955780481 6561222027534808466835361)
                  ·
                    refine ⟨4920916520651106350126521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6561222027534808466835361 4920916520651106350126521)
                    ·
                      refine ⟨3690687390488329762594891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4920916520651106350126521 3690687390488329762594891)
                      ·
                        rfl

theorem cell23_7187588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_7187588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187588 prefixEnd_7187588 := by exact prefixLift 7187588
  have htrace : WordTrace (prefixWord ++ tailWord_7187588) baseStart_7187588 baseEnd_7187588 := by
    simpa [prefixWord, tailWord_7187588, baseEnd_7187588] using wordTrace_append hprefix tailTrace_7187588
  have hstable : (prefixWord ++ tailWord_7187588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187588).length < 2 ^ (prefixWord ++ tailWord_7187588).sum := by decide
  have hdescent : baseEnd_7187588 < baseStart_7187588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187640 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_7187640 : Nat := 118140960795 + 7187640 * 2 ^ 59
def prefixEnd_7187640 : Nat := 4983230072969 + 3 ^ 40 * 7187640 * 2
def baseEnd_7187640 : Nat := 3690714091482363559144651

theorem tailTrace_7187640 : CollatzResearch.WordTrace tailWord_7187640 prefixEnd_7187640 3690714091482363559144651 := by
  unfold tailWord_7187640
  simp only [CollatzResearch.WordTrace]
  refine ⟨131077383840207653013384187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174769845120276870684512249 131077383840207653013384187)
  ·
    refine ⟨196616075760311479520076281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131077383840207653013384187 196616075760311479520076281)
    ·
      refine ⟨147462056820233609640057211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196616075760311479520076281 147462056820233609640057211)
      ·
        refine ⟨221193085230350414460085817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147462056820233609640057211 221193085230350414460085817)
        ·
          refine ⟨165894813922762810845064363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221193085230350414460085817 165894813922762810845064363)
          ·
            refine ⟨248842220884144216267596545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165894813922762810845064363 248842220884144216267596545)
            ·
              refine ⟨186631665663108162200697409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248842220884144216267596545 186631665663108162200697409)
              ·
                refine ⟨139973749247331121650523057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186631665663108162200697409 139973749247331121650523057)
                ·
                  refine ⟨104980311935498341237892293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139973749247331121650523057 104980311935498341237892293)
                  ·
                    refine ⟨19683808487905938982104805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104980311935498341237892293 19683808487905938982104805)
                    ·
                      refine ⟨3690714091482363559144651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19683808487905938982104805 3690714091482363559144651)
                      ·
                        rfl

theorem cell23_7187640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_7187640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187640 prefixEnd_7187640 := by exact prefixLift 7187640
  have htrace : WordTrace (prefixWord ++ tailWord_7187640) baseStart_7187640 baseEnd_7187640 := by
    simpa [prefixWord, tailWord_7187640, baseEnd_7187640] using wordTrace_append hprefix tailTrace_7187640
  have hstable : (prefixWord ++ tailWord_7187640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187640).length < 2 ^ (prefixWord ++ tailWord_7187640).sum := by decide
  have hdescent : baseEnd_7187640 < baseStart_7187640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187717 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_7187717 : Nat := 118140960795 + 7187717 * 2 ^ 59
def prefixEnd_7187717 : Nat := 4983230072969 + 3 ^ 40 * 7187717 * 2
def baseEnd_7187717 : Nat := 3690753629492759757881797

theorem tailTrace_7187717 : CollatzResearch.WordTrace tailWord_7187717 prefixEnd_7187717 3690753629492759757881797 := by
  unfold tailWord_7187717
  simp only [CollatzResearch.WordTrace]
  refine ⟨262157576101136348177321405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174771717400757565451547603 262157576101136348177321405)
  ·
    refine ⟨98309091037926130566495527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262157576101136348177321405 98309091037926130566495527)
    ·
      refine ⟨147463636556889195849743291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98309091037926130566495527 147463636556889195849743291)
      ·
        refine ⟨221195454835333793774614937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147463636556889195849743291 221195454835333793774614937)
        ·
          refine ⟨165896591126500345330961203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221195454835333793774614937 165896591126500345330961203)
          ·
            refine ⟨248844886689750517996441805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165896591126500345330961203 248844886689750517996441805)
            ·
              refine ⟨93316832508656444248665677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248844886689750517996441805 93316832508656444248665677)
              ·
                refine ⟨34993812190746166593249629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93316832508656444248665677 34993812190746166593249629)
                ·
                  refine ⟨13122679571529812472468611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34993812190746166593249629 13122679571529812472468611)
                  ·
                    refine ⟨19684019357294718708702917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13122679571529812472468611 19684019357294718708702917)
                    ·
                      refine ⟨3690753629492759757881797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19684019357294718708702917 3690753629492759757881797)
                      ·
                        rfl

theorem cell23_7187717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_7187717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187717 prefixEnd_7187717 := by exact prefixLift 7187717
  have htrace : WordTrace (prefixWord ++ tailWord_7187717) baseStart_7187717 baseEnd_7187717 := by
    simpa [prefixWord, tailWord_7187717, baseEnd_7187717] using wordTrace_append hprefix tailTrace_7187717
  have hstable : (prefixWord ++ tailWord_7187717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187717).length < 2 ^ (prefixWord ++ tailWord_7187717).sum := by decide
  have hdescent : baseEnd_7187717 < baseStart_7187717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187754 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7187754 : Nat := 118140960795 + 7187754 * 2 ^ 59
def prefixEnd_7187754 : Nat := 4983230072969 + 3 ^ 40 * 7187754 * 2
def baseEnd_7187754 : Nat := 3690772628276976113119127

theorem tailTrace_7187754 : CollatzResearch.WordTrace tailWord_7187754 prefixEnd_7187754 3690772628276976113119127 := by
  unfold tailWord_7187754
  simp only [CollatzResearch.WordTrace]
  refine ⟨65539731400500575874104579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174772617068001535664278877 65539731400500575874104579)
  ·
    refine ⟨98309597100750863811156869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65539731400500575874104579 98309597100750863811156869)
    ·
      refine ⟨18433049456390786964591913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98309597100750863811156869 18433049456390786964591913)
      ·
        refine ⟨13824787092293090223443935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18433049456390786964591913 13824787092293090223443935)
        ·
          refine ⟨20737180638439635335165903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13824787092293090223443935 20737180638439635335165903)
          ·
            refine ⟨31105770957659453002748855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20737180638439635335165903 31105770957659453002748855)
            ·
              refine ⟨46658656436489179504123283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31105770957659453002748855 46658656436489179504123283)
              ·
                refine ⟨69987984654733769256184925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46658656436489179504123283 69987984654733769256184925)
                ·
                  refine ⟨26245494245525163471069347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69987984654733769256184925 26245494245525163471069347)
                  ·
                    refine ⟨39368241368287745206604021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26245494245525163471069347 39368241368287745206604021)
                    ·
                      refine ⟨3690772628276976113119127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39368241368287745206604021 3690772628276976113119127)
                      ·
                        rfl

theorem cell23_7187754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7187754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187754 prefixEnd_7187754 := by exact prefixLift 7187754
  have htrace : WordTrace (prefixWord ++ tailWord_7187754) baseStart_7187754 baseEnd_7187754 := by
    simpa [prefixWord, tailWord_7187754, baseEnd_7187754] using wordTrace_append hprefix tailTrace_7187754
  have hstable : (prefixWord ++ tailWord_7187754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187754).length < 2 ^ (prefixWord ++ tailWord_7187754).sum := by decide
  have hdescent : baseEnd_7187754 < baseStart_7187754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187764 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7187764 : Nat := 118140960795 + 7187764 * 2 ^ 59
def prefixEnd_7187764 : Nat := 4983230072969 + 3 ^ 40 * 7187764 * 2
def baseEnd_7187764 : Nat := 3690777763083521073994081

theorem tailTrace_7187764 : CollatzResearch.WordTrace tailWord_7187764 prefixEnd_7187764 3690777763083521073994081 := by
  unfold tailWord_7187764
  simp only [CollatzResearch.WordTrace]
  refine ⟨131079645165983037602141173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174772860221310716802854897 131079645165983037602141173)
  ·
    refine ⟨12288716734310909775200735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131079645165983037602141173 12288716734310909775200735)
    ·
      refine ⟨18433075101466364662801103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12288716734310909775200735 18433075101466364662801103)
      ·
        refine ⟨27649612652199546994201655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18433075101466364662801103 27649612652199546994201655)
        ·
          refine ⟨41474418978299320491302483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27649612652199546994201655 41474418978299320491302483)
          ·
            refine ⟨62211628467448980736953725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41474418978299320491302483 62211628467448980736953725)
            ·
              refine ⟨23329360675293367776357647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62211628467448980736953725 23329360675293367776357647)
              ·
                refine ⟨34994041012940051664536471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23329360675293367776357647 34994041012940051664536471)
                ·
                  refine ⟨52491061519410077496804707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34994041012940051664536471 52491061519410077496804707)
                  ·
                    refine ⟨78736592279115116245207061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52491061519410077496804707 78736592279115116245207061)
                    ·
                      refine ⟨3690777763083521073994081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78736592279115116245207061 3690777763083521073994081)
                      ·
                        rfl

theorem cell23_7187764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7187764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187764 prefixEnd_7187764 := by exact prefixLift 7187764
  have htrace : WordTrace (prefixWord ++ tailWord_7187764) baseStart_7187764 baseEnd_7187764 := by
    simpa [prefixWord, tailWord_7187764, baseEnd_7187764] using wordTrace_append hprefix tailTrace_7187764
  have hstable : (prefixWord ++ tailWord_7187764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187764).length < 2 ^ (prefixWord ++ tailWord_7187764).sum := by decide
  have hdescent : baseEnd_7187764 < baseStart_7187764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187807 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_7187807 : Nat := 118140960795 + 7187807 * 2 ^ 59
def prefixEnd_7187807 : Nat := 4983230072969 + 3 ^ 40 * 7187807 * 2
def baseEnd_7187807 : Nat := 3690799842751664405756383

theorem tailTrace_7187807 : CollatzResearch.WordTrace tailWord_7187807 prefixEnd_7187807 3690799842751664405756383 := by
  unfold tailWord_7187807
  simp only [CollatzResearch.WordTrace]
  refine ⟨262160858670810293548097675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174773905780540195698731783 262160858670810293548097675)
  ·
    refine ⟨393241288006215440322146513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262160858670810293548097675 393241288006215440322146513)
    ·
      refine ⟨294930966004661580241609885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393241288006215440322146513 294930966004661580241609885)
      ·
        refine ⟨110599112251748092590603707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294930966004661580241609885 110599112251748092590603707)
        ·
          refine ⟨165898668377622138885905561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110599112251748092590603707 165898668377622138885905561)
          ·
            refine ⟨124424001283216604164429171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165898668377622138885905561 124424001283216604164429171)
            ·
              refine ⟨186636001924824906246643757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124424001283216604164429171 186636001924824906246643757)
              ·
                refine ⟨69988500721809339842491409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186636001924824906246643757 69988500721809339842491409)
                ·
                  refine ⟨52491375541357004881868557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69988500721809339842491409 52491375541357004881868557)
                  ·
                    refine ⟨19684265828008876830700709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52491375541357004881868557 19684265828008876830700709)
                    ·
                      refine ⟨3690799842751664405756383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19684265828008876830700709 3690799842751664405756383)
                      ·
                        rfl

theorem cell23_7187807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_7187807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187807 prefixEnd_7187807 := by exact prefixLift 7187807
  have htrace : WordTrace (prefixWord ++ tailWord_7187807) baseStart_7187807 baseEnd_7187807 := by
    simpa [prefixWord, tailWord_7187807, baseEnd_7187807] using wordTrace_append hprefix tailTrace_7187807
  have hstable : (prefixWord ++ tailWord_7187807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187807).length < 2 ^ (prefixWord ++ tailWord_7187807).sum := by decide
  have hdescent : baseEnd_7187807 < baseStart_7187807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187822 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_7187822 : Nat := 118140960795 + 7187822 * 2 ^ 59
def prefixEnd_7187822 : Nat := 4983230072969 + 3 ^ 40 * 7187822 * 2
def baseEnd_7187822 : Nat := 3690807544961481847068815

theorem tailTrace_7187822 : CollatzResearch.WordTrace tailWord_7187822 prefixEnd_7187822 3690807544961481847068815 := by
  unfold tailWord_7187822
  simp only [CollatzResearch.WordTrace]
  refine ⟨32770175720719493888736715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174774270510503967406595813 32770175720719493888736715)
  ·
    refine ⟨49155263581079240833105073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32770175720719493888736715 49155263581079240833105073)
    ·
      refine ⟨36866447685809430624828805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49155263581079240833105073 36866447685809430624828805)
      ·
        refine ⟨6912458941089268242155401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36866447685809430624828805 6912458941089268242155401)
        ·
          refine ⟨5184344205816951181616551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6912458941089268242155401 5184344205816951181616551)
          ·
            refine ⟨7776516308725426772424827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5184344205816951181616551 7776516308725426772424827)
            ·
              refine ⟨11664774463088140158637241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7776516308725426772424827 11664774463088140158637241)
              ·
                refine ⟨8748580847316105118977931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11664774463088140158637241 8748580847316105118977931)
                ·
                  refine ⟨13122871270974157678466897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8748580847316105118977931 13122871270974157678466897)
                  ·
                    refine ⟨9842153453230618258850173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13122871270974157678466897 9842153453230618258850173)
                    ·
                      refine ⟨3690807544961481847068815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9842153453230618258850173 3690807544961481847068815)
                      ·
                        rfl

theorem cell23_7187822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_7187822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187822 prefixEnd_7187822 := by exact prefixLift 7187822
  have htrace : WordTrace (prefixWord ++ tailWord_7187822) baseStart_7187822 baseEnd_7187822 := by
    simpa [prefixWord, tailWord_7187822, baseEnd_7187822] using wordTrace_append hprefix tailTrace_7187822
  have hstable : (prefixWord ++ tailWord_7187822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187822).length < 2 ^ (prefixWord ++ tailWord_7187822).sum := by decide
  have hdescent : baseEnd_7187822 < baseStart_7187822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187844 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_7187844 : Nat := 118140960795 + 7187844 * 2 ^ 59
def prefixEnd_7187844 : Nat := 4983230072969 + 3 ^ 40 * 7187844 * 2
def baseEnd_7187844 : Nat := 3690818841535880760993713

theorem tailTrace_7187844 : CollatzResearch.WordTrace tailWord_7187844 prefixEnd_7187844 3690818841535880760993713 := by
  unfold tailWord_7187844
  simp only [CollatzResearch.WordTrace]
  refine ⟨131081104085838124433597293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174774805447784165911463057 131081104085838124433597293)
  ·
    refine ⟨49155414032189296662598985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131081104085838124433597293 49155414032189296662598985)
    ·
      refine ⟨36866560524141972496949239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49155414032189296662598985 36866560524141972496949239)
      ·
        refine ⟨55299840786212958745423859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36866560524141972496949239 55299840786212958745423859)
        ·
          refine ⟨82949761179319438118135789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55299840786212958745423859 82949761179319438118135789)
          ·
            refine ⟨31106160442244789294300921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82949761179319438118135789 31106160442244789294300921)
            ·
              refine ⟨23329620331683591970725691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31106160442244789294300921 23329620331683591970725691)
              ·
                refine ⟨34994430497525387956088537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23329620331683591970725691 34994430497525387956088537)
                ·
                  refine ⟨26245822873144040967066403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34994430497525387956088537 26245822873144040967066403)
                  ·
                    refine ⟨39368734309716061450599605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26245822873144040967066403 39368734309716061450599605)
                    ·
                      refine ⟨3690818841535880760993713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39368734309716061450599605 3690818841535880760993713)
                      ·
                        rfl

theorem cell23_7187844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_7187844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187844 prefixEnd_7187844 := by exact prefixLift 7187844
  have htrace : WordTrace (prefixWord ++ tailWord_7187844) baseStart_7187844 baseEnd_7187844 := by
    simpa [prefixWord, tailWord_7187844, baseEnd_7187844] using wordTrace_append hprefix tailTrace_7187844
  have hstable : (prefixWord ++ tailWord_7187844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187844).length < 2 ^ (prefixWord ++ tailWord_7187844).sum := by decide
  have hdescent : baseEnd_7187844 < baseStart_7187844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187887 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_7187887 : Nat := 118140960795 + 7187887 * 2 ^ 59
def prefixEnd_7187887 : Nat := 4983230072969 + 3 ^ 40 * 7187887 * 2
def baseEnd_7187887 : Nat := 3690840921204024092756015

theorem tailTrace_7187887 : CollatzResearch.WordTrace tailWord_7187887 prefixEnd_7187887 3690840921204024092756015 := by
  unfold tailWord_7187887
  simp only [CollatzResearch.WordTrace]
  refine ⟨262163776510520467211009915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174775851007013644807339943 262163776510520467211009915)
  ·
    refine ⟨393245664765780700816514873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262163776510520467211009915 393245664765780700816514873)
    ·
      refine ⟨294934248574335525612386155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393245664765780700816514873 294934248574335525612386155)
      ·
        refine ⟨442401372861503288418579233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294934248574335525612386155 442401372861503288418579233)
        ·
          refine ⟨331801029646127466313934425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442401372861503288418579233 331801029646127466313934425)
          ·
            refine ⟨248850772234595599735450819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331801029646127466313934425 248850772234595599735450819)
            ·
              refine ⟨373276158351893399603176229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248850772234595599735450819 373276158351893399603176229)
              ·
                refine ⟨69989279690980012425595543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373276158351893399603176229 69989279690980012425595543)
                ·
                  refine ⟨104983919536470018638393315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69989279690980012425595543 104983919536470018638393315)
                  ·
                    refine ⟨157475879304705027957589973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104983919536470018638393315 157475879304705027957589973)
                    ·
                      refine ⟨3690840921204024092756015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157475879304705027957589973 3690840921204024092756015)
                      ·
                        rfl

theorem cell23_7187887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_7187887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187887 prefixEnd_7187887 := by exact prefixLift 7187887
  have htrace : WordTrace (prefixWord ++ tailWord_7187887) baseStart_7187887 baseEnd_7187887 := by
    simpa [prefixWord, tailWord_7187887, baseEnd_7187887] using wordTrace_append hprefix tailTrace_7187887
  have hstable : (prefixWord ++ tailWord_7187887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187887).length < 2 ^ (prefixWord ++ tailWord_7187887).sum := by decide
  have hdescent : baseEnd_7187887 < baseStart_7187887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7187944 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7187944 : Nat := 118140960795 + 7187944 * 2 ^ 59
def prefixEnd_7187944 : Nat := 4983230072969 + 3 ^ 40 * 7187944 * 2
def baseEnd_7187944 : Nat := 3690870189601330369743253

theorem tailTrace_7187944 : CollatzResearch.WordTrace tailWord_7187944 prefixEnd_7187944 3690870189601330369743253 := by
  unfold tailWord_7187944
  simp only [CollatzResearch.WordTrace]
  refine ⟨131082927735656982972917443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174777236980875977297223257 131082927735656982972917443)
  ·
    refine ⟨196624391603485474459376165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131082927735656982972917443 196624391603485474459376165)
    ·
      refine ⟨36867073425653526461133031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196624391603485474459376165 36867073425653526461133031)
      ·
        refine ⟨55300610138480289691699547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36867073425653526461133031 55300610138480289691699547)
        ·
          refine ⟨82950915207720434537549321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55300610138480289691699547 82950915207720434537549321)
          ·
            refine ⟨62213186405790325903161991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82950915207720434537549321 62213186405790325903161991)
            ·
              refine ⟨93319779608685488854742987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62213186405790325903161991 93319779608685488854742987)
              ·
                refine ⟨139979669413028233282114481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93319779608685488854742987 139979669413028233282114481)
                ·
                  refine ⟨104984752059771174961585861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139979669413028233282114481 104984752059771174961585861)
                  ·
                    refine ⟨19684641011207095305297349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104984752059771174961585861 19684641011207095305297349)
                    ·
                      refine ⟨3690870189601330369743253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19684641011207095305297349 3690870189601330369743253)
                      ·
                        rfl

theorem cell23_7187944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7187944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7187944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7187944 prefixEnd_7187944 := by exact prefixLift 7187944
  have htrace : WordTrace (prefixWord ++ tailWord_7187944) baseStart_7187944 baseEnd_7187944 := by
    simpa [prefixWord, tailWord_7187944, baseEnd_7187944] using wordTrace_append hprefix tailTrace_7187944
  have hstable : (prefixWord ++ tailWord_7187944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7187944).length < 2 ^ (prefixWord ++ tailWord_7187944).sum := by decide
  have hdescent : baseEnd_7187944 < baseStart_7187944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7187944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188001 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 3, 5]
def baseStart_7188001 : Nat := 118140960795 + 7188001 * 2 ^ 59
def prefixEnd_7188001 : Nat := 4983230072969 + 3 ^ 40 * 7188001 * 2
def baseEnd_7188001 : Nat := 1230299819332878882243497

theorem tailTrace_7188001 : CollatzResearch.WordTrace tailWord_7188001 prefixEnd_7188001 1230299819332878882243497 := by
  unfold tailWord_7188001
  simp only [CollatzResearch.WordTrace]
  refine ⟨262167934432107464680659857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174778622954738309787106571 262167934432107464680659857)
  ·
    refine ⟨196625950824080598510494893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262167934432107464680659857 196625950824080598510494893)
    ·
      refine ⟨73734731559030224441435585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196625950824080598510494893 73734731559030224441435585)
      ·
        refine ⟨55301048669272668331076689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73734731559030224441435585 55301048669272668331076689)
        ·
          refine ⟨41475786501954501248307517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55301048669272668331076689 41475786501954501248307517)
          ·
            refine ⟨15553419938232937968115319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41475786501954501248307517 15553419938232937968115319)
            ·
              refine ⟨23330129907349406952172979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15553419938232937968115319 23330129907349406952172979)
              ·
                refine ⟨34995194861024110428259469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23330129907349406952172979 34995194861024110428259469)
                ·
                  refine ⟨13123198072884041410597301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34995194861024110428259469 13123198072884041410597301)
                  ·
                    refine ⟨1230299819332878882243497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13123198072884041410597301 1230299819332878882243497)
                    ·
                      rfl

theorem cell23_7188001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_7188001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188001 prefixEnd_7188001 := by exact prefixLift 7188001
  have htrace : WordTrace (prefixWord ++ tailWord_7188001) baseStart_7188001 baseEnd_7188001 := by
    simpa [prefixWord, tailWord_7188001, baseEnd_7188001] using wordTrace_append hprefix tailTrace_7188001
  have hstable : (prefixWord ++ tailWord_7188001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188001).length < 2 ^ (prefixWord ++ tailWord_7188001).sum := by decide
  have hdescent : baseEnd_7188001 < baseStart_7188001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188055 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 3, 2, 2]
def baseStart_7188055 : Nat := 118140960795 + 7188055 * 2 ^ 59
def prefixEnd_7188055 : Nat := 4983230072969 + 3 ^ 40 * 7188055 * 2
def baseEnd_7188055 : Nat := 3690927185953979435455243

theorem tailTrace_7188055 : CollatzResearch.WordTrace tailWord_7188055 prefixEnd_7188055 3690927185953979435455243 := by
  unfold tailWord_7188055
  simp only [CollatzResearch.WordTrace]
  refine ⟨262169903973911831903125619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174779935982607887935417079 262169903973911831903125619)
  ·
    refine ⟨393254855960867747854688429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262169903973911831903125619 393254855960867747854688429)
    ·
      refine ⟨147470570985325405445508161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393254855960867747854688429 147470570985325405445508161)
      ·
        refine ⟨110602928238994054084131121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147470570985325405445508161 110602928238994054084131121)
        ·
          refine ⟨82952196179245540563098341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110602928238994054084131121 82952196179245540563098341)
          ·
            refine ⟨15553536783608538855580939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82952196179245540563098341 15553536783608538855580939)
            ·
              refine ⟨23330305175412808283371409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15553536783608538855580939 23330305175412808283371409)
              ·
                refine ⟨17497728881559606212528557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23330305175412808283371409 17497728881559606212528557)
                ·
                  refine ⟨6561648330584852329698209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17497728881559606212528557 6561648330584852329698209)
                  ·
                    refine ⟨4921236247938639247273657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6561648330584852329698209 4921236247938639247273657)
                    ·
                      refine ⟨3690927185953979435455243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921236247938639247273657 3690927185953979435455243)
                      ·
                        rfl

theorem cell23_7188055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_7188055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188055 prefixEnd_7188055 := by exact prefixLift 7188055
  have htrace : WordTrace (prefixWord ++ tailWord_7188055) baseStart_7188055 baseEnd_7188055 := by
    simpa [prefixWord, tailWord_7188055, baseEnd_7188055] using wordTrace_append hprefix tailTrace_7188055
  have hstable : (prefixWord ++ tailWord_7188055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188055).length < 2 ^ (prefixWord ++ tailWord_7188055).sum := by decide
  have hdescent : baseEnd_7188055 < baseStart_7188055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188072 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7188072 : Nat := 118140960795 + 7188072 * 2 ^ 59
def prefixEnd_7188072 : Nat := 4983230072969 + 3 ^ 40 * 7188072 * 2
def baseEnd_7188072 : Nat := 3690935915125105868942665

theorem tailTrace_7188072 : CollatzResearch.WordTrace tailWord_7188072 prefixEnd_7188072 3690935915125105868942665 := by
  unfold tailWord_7188072
  simp only [CollatzResearch.WordTrace]
  refine ⟨131085262007425121903247235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174780349343233495870996313 131085262007425121903247235)
  ·
    refine ⟨196627893011137682854870853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131085262007425121903247235 196627893011137682854870853)
    ·
      refine ⟨36867729939588315535288285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196627893011137682854870853 36867729939588315535288285)
      ·
        refine ⟨13825398727345618325733107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36867729939588315535288285 13825398727345618325733107)
        ·
          refine ⟨20738098091018427488599661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13825398727345618325733107 20738098091018427488599661)
          ·
            refine ⟨7776786784131910308224873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20738098091018427488599661 7776786784131910308224873)
            ·
              refine ⟨5832590088098932731168655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7776786784131910308224873 5832590088098932731168655)
              ·
                refine ⟨8748885132148399096752983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832590088098932731168655 8748885132148399096752983)
                ·
                  refine ⟨13123327698222598645129475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8748885132148399096752983 13123327698222598645129475)
                  ·
                    refine ⟨19684991547333897967694213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13123327698222598645129475 19684991547333897967694213)
                    ·
                      refine ⟨3690935915125105868942665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19684991547333897967694213 3690935915125105868942665)
                      ·
                        rfl

theorem cell23_7188072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7188072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188072 prefixEnd_7188072 := by exact prefixLift 7188072
  have htrace : WordTrace (prefixWord ++ tailWord_7188072) baseStart_7188072 baseEnd_7188072 := by
    simpa [prefixWord, tailWord_7188072, baseEnd_7188072] using wordTrace_append hprefix tailTrace_7188072
  have hstable : (prefixWord ++ tailWord_7188072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188072).length < 2 ^ (prefixWord ++ tailWord_7188072).sum := by decide
  have hdescent : baseEnd_7188072 < baseStart_7188072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188131 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 5]
def baseStart_7188131 : Nat := 118140960795 + 7188131 * 2 ^ 59
def prefixEnd_7188131 : Nat := 4983230072969 + 3 ^ 40 * 7188131 * 2
def baseEnd_7188131 : Nat := 3690966210483721138104893

theorem tailTrace_7188131 : CollatzResearch.WordTrace tailWord_7188131 prefixEnd_7188131 3690966210483721138104893 := by
  unfold tailWord_7188131
  simp only [CollatzResearch.WordTrace]
  refine ⟨262172675921636496882892247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174781783947757664588594831 262172675921636496882892247)
  ·
    refine ⟨393259013882454745324338371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262172675921636496882892247 393259013882454745324338371)
    ·
      refine ⟨589888520823682117986507557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393259013882454745324338371 589888520823682117986507557)
      ·
        refine ⟨110604097654440397122470167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 589888520823682117986507557 110604097654440397122470167)
        ·
          refine ⟨165906146481660595683705251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110604097654440397122470167 165906146481660595683705251)
          ·
            refine ⟨248859219722490893525557877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165906146481660595683705251 248859219722490893525557877)
            ·
              refine ⟨23330551848983521268021051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248859219722490893525557877 23330551848983521268021051)
              ·
                refine ⟨34995827773475281902031577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23330551848983521268021051 34995827773475281902031577)
                ·
                  refine ⟨26246870830106461426523683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34995827773475281902031577 26246870830106461426523683)
                  ·
                    refine ⟨39370306245159692139785525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26246870830106461426523683 39370306245159692139785525)
                    ·
                      refine ⟨3690966210483721138104893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39370306245159692139785525 3690966210483721138104893)
                      ·
                        rfl

theorem cell23_7188131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_7188131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188131 prefixEnd_7188131 := by exact prefixLift 7188131
  have htrace : WordTrace (prefixWord ++ tailWord_7188131) baseStart_7188131 baseEnd_7188131 := by
    simpa [prefixWord, tailWord_7188131, baseEnd_7188131] using wordTrace_append hprefix tailTrace_7188131
  have hstable : (prefixWord ++ tailWord_7188131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188131).length < 2 ^ (prefixWord ++ tailWord_7188131).sum := by decide
  have hdescent : baseEnd_7188131 < baseStart_7188131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188166 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7188166 : Nat := 118140960795 + 7188166 * 2 ^ 59
def prefixEnd_7188166 : Nat := 4983230072969 + 3 ^ 40 * 7188166 * 2
def baseEnd_7188166 : Nat := 3690984182306628501167233

theorem tailTrace_7188166 : CollatzResearch.WordTrace tailWord_7188166 prefixEnd_7188166 3690984182306628501167233 := by
  unfold tailWord_7188166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8192936014890928058138011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174782634984339798573610901 8192936014890928058138011)
  ·
    refine ⟨12289404022336392087207017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8192936014890928058138011 12289404022336392087207017)
    ·
      refine ⟨9217053016752294065405263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12289404022336392087207017 9217053016752294065405263)
      ·
        refine ⟨13825579525128441098107895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9217053016752294065405263 13825579525128441098107895)
        ·
          refine ⟨20738369287692661647161843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13825579525128441098107895 20738369287692661647161843)
          ·
            refine ⟨31107553931538992470742765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20738369287692661647161843 31107553931538992470742765)
            ·
              refine ⟨11665332724327122176528537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31107553931538992470742765 11665332724327122176528537)
              ·
                refine ⟨8748999543245341632396403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11665332724327122176528537 8748999543245341632396403)
                ·
                  refine ⟨13123499314868012448594605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8748999543245341632396403 13123499314868012448594605)
                  ·
                    refine ⟨4921312243075504668222977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13123499314868012448594605 4921312243075504668222977)
                    ·
                      refine ⟨3690984182306628501167233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921312243075504668222977 3690984182306628501167233)
                      ·
                        rfl

theorem cell23_7188166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7188166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188166 prefixEnd_7188166 := by exact prefixLift 7188166
  have htrace : WordTrace (prefixWord ++ tailWord_7188166) baseStart_7188166 baseEnd_7188166 := by
    simpa [prefixWord, tailWord_7188166, baseEnd_7188166] using wordTrace_append hprefix tailTrace_7188166
  have hstable : (prefixWord ++ tailWord_7188166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188166).length < 2 ^ (prefixWord ++ tailWord_7188166).sum := by decide
  have hdescent : baseEnd_7188166 < baseStart_7188166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188191 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_7188191 : Nat := 118140960795 + 7188191 * 2 ^ 59
def prefixEnd_7188191 : Nat := 4983230072969 + 3 ^ 40 * 7188191 * 2
def baseEnd_7188191 : Nat := 3690997019322990903354617

theorem tailTrace_7188191 : CollatzResearch.WordTrace tailWord_7188191 prefixEnd_7188191 3690997019322990903354617 := by
  unfold tailWord_7188191
  simp only [CollatzResearch.WordTrace]
  refine ⟨262174864301419127130076427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174783242867612751420050951 262174864301419127130076427)
  ·
    refine ⟨393262296452128690695114641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262174864301419127130076427 393262296452128690695114641)
    ·
      refine ⟨294946722339096518021335981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393262296452128690695114641 294946722339096518021335981)
      ·
        refine ⟨110605020877161194258000993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294946722339096518021335981 110605020877161194258000993)
        ·
          refine ⟨82953765657870895693500745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110605020877161194258000993 82953765657870895693500745)
          ·
            refine ⟨62215324243403171770125559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82953765657870895693500745 62215324243403171770125559)
            ·
              refine ⟨93322986365104757655188339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62215324243403171770125559 93322986365104757655188339)
              ·
                refine ⟨139984479547657136482782509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93322986365104757655188339 139984479547657136482782509)
                ·
                  refine ⟨52494179830371426181043441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139984479547657136482782509 52494179830371426181043441)
                  ·
                    refine ⟨39370634872778569635782581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52494179830371426181043441 39370634872778569635782581)
                    ·
                      refine ⟨3690997019322990903354617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39370634872778569635782581 3690997019322990903354617)
                      ·
                        rfl

theorem cell23_7188191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_7188191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188191 prefixEnd_7188191 := by exact prefixLift 7188191
  have htrace : WordTrace (prefixWord ++ tailWord_7188191) baseStart_7188191 baseEnd_7188191 := by
    simpa [prefixWord, tailWord_7188191, baseEnd_7188191] using wordTrace_append hprefix tailTrace_7188191
  have hstable : (prefixWord ++ tailWord_7188191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188191).length < 2 ^ (prefixWord ++ tailWord_7188191).sum := by decide
  have hdescent : baseEnd_7188191 < baseStart_7188191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188201 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_7188201 : Nat := 118140960795 + 7188201 * 2 ^ 59
def prefixEnd_7188201 : Nat := 4983230072969 + 3 ^ 40 * 7188201 * 2
def baseEnd_7188201 : Nat := 3691002154129535864229571

theorem tailTrace_7188201 : CollatzResearch.WordTrace tailWord_7188201 prefixEnd_7188201 3691002154129535864229571 := by
  unfold tailWord_7188201
  simp only [CollatzResearch.WordTrace]
  refine ⟨262175229031382898837940457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174783486020921932558626971 262175229031382898837940457)
  ·
    refine ⟨196631421773537174128455343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262175229031382898837940457 196631421773537174128455343)
    ·
      refine ⟨294947132660305761192683015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196631421773537174128455343 294947132660305761192683015)
      ·
        refine ⟨442420698990458641789024523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294947132660305761192683015 442420698990458641789024523)
        ·
          refine ⟨663631048485687962683536785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442420698990458641789024523 663631048485687962683536785)
          ·
            refine ⟨497723286364265972012652589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663631048485687962683536785 497723286364265972012652589)
            ·
              refine ⟨186646232386599739504744721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497723286364265972012652589 186646232386599739504744721)
              ·
                refine ⟨139984674289949804628558541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186646232386599739504744721 139984674289949804628558541)
                ·
                  refine ⟨52494252858731176735709453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139984674289949804628558541 52494252858731176735709453)
                  ·
                    refine ⟨19685344822024191275891045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52494252858731176735709453 19685344822024191275891045)
                    ·
                      refine ⟨3691002154129535864229571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19685344822024191275891045 3691002154129535864229571)
                      ·
                        rfl

theorem cell23_7188201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_7188201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188201 prefixEnd_7188201 := by exact prefixLift 7188201
  have htrace : WordTrace (prefixWord ++ tailWord_7188201) baseStart_7188201 baseEnd_7188201 := by
    simpa [prefixWord, tailWord_7188201, baseEnd_7188201] using wordTrace_append hprefix tailTrace_7188201
  have hstable : (prefixWord ++ tailWord_7188201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188201).length < 2 ^ (prefixWord ++ tailWord_7188201).sum := by decide
  have hdescent : baseEnd_7188201 < baseStart_7188201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188205 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_7188205 : Nat := 118140960795 + 7188205 * 2 ^ 59
def prefixEnd_7188205 : Nat := 4983230072969 + 3 ^ 40 * 7188205 * 2
def baseEnd_7188205 : Nat := 3691004208052153848579553

theorem tailTrace_7188205 : CollatzResearch.WordTrace tailWord_7188205 prefixEnd_7188205 3691004208052153848579553 := by
  unfold tailWord_7188205
  simp only [CollatzResearch.WordTrace]
  refine ⟨262175374923368407521086069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174783583282245605014057379 262175374923368407521086069)
  ·
    refine ⟨24578941399065788205101819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262175374923368407521086069 24578941399065788205101819)
    ·
      refine ⟨36868412098598682307652729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24578941399065788205101819 36868412098598682307652729)
      ·
        refine ⟨27651309073949011730739547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36868412098598682307652729 27651309073949011730739547)
        ·
          refine ⟨41476963610923517596109321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27651309073949011730739547 41476963610923517596109321)
          ·
            refine ⟨31107722708192638197081991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41476963610923517596109321 31107722708192638197081991)
            ·
              refine ⟨46661584062288957295622987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31107722708192638197081991 46661584062288957295622987)
              ·
                refine ⟨69992376093433435943434481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46661584062288957295622987 69992376093433435943434481)
                ·
                  refine ⟨52494282070075076957575861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69992376093433435943434481 52494282070075076957575861)
                  ·
                    refine ⟨4921338944069538464772737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52494282070075076957575861 4921338944069538464772737)
                    ·
                      refine ⟨3691004208052153848579553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921338944069538464772737 3691004208052153848579553)
                      ·
                        rfl

theorem cell23_7188205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_7188205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188205 prefixEnd_7188205 := by exact prefixLift 7188205
  have htrace : WordTrace (prefixWord ++ tailWord_7188205) baseStart_7188205 baseEnd_7188205 := by
    simpa [prefixWord, tailWord_7188205, baseEnd_7188205] using wordTrace_append hprefix tailTrace_7188205
  have hstable : (prefixWord ++ tailWord_7188205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188205).length < 2 ^ (prefixWord ++ tailWord_7188205).sum := by decide
  have hdescent : baseEnd_7188205 < baseStart_7188205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188212 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7188212 : Nat := 118140960795 + 7188212 * 2 ^ 59
def prefixEnd_7188212 : Nat := 4983230072969 + 3 ^ 40 * 7188212 * 2
def baseEnd_7188212 : Nat := 3691007802416735321192021

theorem tailTrace_7188212 : CollatzResearch.WordTrace tailWord_7188212 prefixEnd_7188212 3691007802416735321192021 := by
  unfold tailWord_7188212
  simp only [CollatzResearch.WordTrace]
  refine ⟨131087815117171523858295445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174783753489562031811060593 131087815117171523858295445)
  ·
    refine ⟨6144741333617415180857599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131087815117171523858295445 6144741333617415180857599)
    ·
      refine ⟨9217112000426122771286399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6144741333617415180857599 9217112000426122771286399)
      ·
        refine ⟨13825668000639184156929599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9217112000426122771286399 13825668000639184156929599)
        ·
          refine ⟨20738502000958776235394399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13825668000639184156929599 20738502000958776235394399)
          ·
            refine ⟨31107753001438164353091599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20738502000958776235394399 31107753001438164353091599)
            ·
              refine ⟨46661629502157246529637399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31107753001438164353091599 46661629502157246529637399)
              ·
                refine ⟨69992444253235869794456099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46661629502157246529637399 69992444253235869794456099)
                ·
                  refine ⟨104988666379853804691684149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69992444253235869794456099 104988666379853804691684149)
                  ·
                    refine ⟨9842687473111294189845389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104988666379853804691684149 9842687473111294189845389)
                    ·
                      refine ⟨3691007802416735321192021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9842687473111294189845389 3691007802416735321192021)
                      ·
                        rfl

theorem cell23_7188212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7188212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188212 prefixEnd_7188212 := by exact prefixLift 7188212
  have htrace : WordTrace (prefixWord ++ tailWord_7188212) baseStart_7188212 baseEnd_7188212 := by
    simpa [prefixWord, tailWord_7188212, baseEnd_7188212] using wordTrace_append hprefix tailTrace_7188212
  have hstable : (prefixWord ++ tailWord_7188212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188212).length < 2 ^ (prefixWord ++ tailWord_7188212).sum := by decide
  have hdescent : baseEnd_7188212 < baseStart_7188212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188241 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 8]
def baseStart_7188241 : Nat := 118140960795 + 7188241 * 2 ^ 59
def prefixEnd_7188241 : Nat := 4983230072969 + 3 ^ 40 * 7188241 * 2
def baseEnd_7188241 : Nat := 410113632595079523081043

theorem tailTrace_7188241 : CollatzResearch.WordTrace tailWord_7188241 prefixEnd_7188241 410113632595079523081043 := by
  unfold tailWord_7188241
  simp only [CollatzResearch.WordTrace]
  refine ⟨262176687951237985669396577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174784458634158657112931051 262176687951237985669396577)
  ·
    refine ⟨196632515963428489252047433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262176687951237985669396577 196632515963428489252047433)
    ·
      refine ⟨147474386972571366939035575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196632515963428489252047433 147474386972571366939035575)
      ·
        refine ⟨221211580458857050408553363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147474386972571366939035575 221211580458857050408553363)
        ·
          refine ⟨331817370688285575612830045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221211580458857050408553363 331817370688285575612830045)
          ·
            refine ⟨124431514008107090854811267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331817370688285575612830045 124431514008107090854811267)
            ·
              refine ⟨186647271012160636282216901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124431514008107090854811267 186647271012160636282216901)
              ·
                refine ⟨34996363314780119302915669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186647271012160636282216901 34996363314780119302915669)
                ·
                  refine ⟨410113632595079523081043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34996363314780119302915669 410113632595079523081043)
                  ·
                    rfl

theorem cell23_7188241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 8].length) (baseStart_7188241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188241 prefixEnd_7188241 := by exact prefixLift 7188241
  have htrace : WordTrace (prefixWord ++ tailWord_7188241) baseStart_7188241 baseEnd_7188241 := by
    simpa [prefixWord, tailWord_7188241, baseEnd_7188241] using wordTrace_append hprefix tailTrace_7188241
  have hstable : (prefixWord ++ tailWord_7188241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188241).length < 2 ^ (prefixWord ++ tailWord_7188241).sum := by decide
  have hdescent : baseEnd_7188241 < baseStart_7188241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188258 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 8]
def baseStart_7188258 : Nat := 118140960795 + 7188258 * 2 ^ 59
def prefixEnd_7188258 : Nat := 4983230072969 + 3 ^ 40 * 7188258 * 2
def baseEnd_7188258 : Nat := 410114602502982460135201

theorem tailTrace_7188258 : CollatzResearch.WordTrace tailWord_7188258 prefixEnd_7188258 410114602502982460135201 := by
  unfold tailWord_7188258
  simp only [CollatzResearch.WordTrace]
  refine ⟨65544326998044099393191357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174784871994784265048510285 65544326998044099393191357)
  ·
    refine ⟨24579122624266537272446759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65544326998044099393191357 24579122624266537272446759)
    ·
      refine ⟨36868683936399805908670139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24579122624266537272446759 36868683936399805908670139)
      ·
        refine ⟨55303025904599708863005209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36868683936399805908670139 55303025904599708863005209)
        ·
          refine ⟨41477269428449781647253907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55303025904599708863005209 41477269428449781647253907)
          ·
            refine ⟨62215904142674672470880861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41477269428449781647253907 62215904142674672470880861)
            ·
              refine ⟨23330964053503002176580323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62215904142674672470880861 23330964053503002176580323)
              ·
                refine ⟨34996446080254503264870485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23330964053503002176580323 34996446080254503264870485)
                ·
                  refine ⟨410114602502982460135201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34996446080254503264870485 410114602502982460135201)
                  ·
                    rfl

theorem cell23_7188258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_7188258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188258 prefixEnd_7188258 := by exact prefixLift 7188258
  have htrace : WordTrace (prefixWord ++ tailWord_7188258) baseStart_7188258 baseEnd_7188258 := by
    simpa [prefixWord, tailWord_7188258, baseEnd_7188258] using wordTrace_append hprefix tailTrace_7188258
  have hstable : (prefixWord ++ tailWord_7188258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188258).length < 2 ^ (prefixWord ++ tailWord_7188258).sum := by decide
  have hdescent : baseEnd_7188258 < baseStart_7188258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188295 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_7188295 : Nat := 118140960795 + 7188295 * 2 ^ 59
def prefixEnd_7188295 : Nat := 4983230072969 + 3 ^ 40 * 7188295 * 2
def baseEnd_7188295 : Nat := 3691050421311058496454139

theorem tailTrace_7188295 : CollatzResearch.WordTrace tailWord_7188295 prefixEnd_7188295 3691050421311058496454139 := by
  unfold tailWord_7188295
  simp only [CollatzResearch.WordTrace]
  refine ⟨262178657493042352891862339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174785771662028235261241559 262178657493042352891862339)
  ·
    refine ⟨393267986239563529337793509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262178657493042352891862339 393267986239563529337793509)
    ·
      refine ⟨73737747419918161750836283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393267986239563529337793509 73737747419918161750836283)
      ·
        refine ⟨110606621129877242626254425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73737747419918161750836283 110606621129877242626254425)
        ·
          refine ⟨82954965847407931969690819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110606621129877242626254425 82954965847407931969690819)
          ·
            refine ⟨124432448771111897954536229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82954965847407931969690819 124432448771111897954536229)
            ·
              refine ⟨23331084144583480866475543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124432448771111897954536229 23331084144583480866475543)
              ·
                refine ⟨34996626216875221299713315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23331084144583480866475543 34996626216875221299713315)
                ·
                  refine ⟨52494939325312831949569973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34996626216875221299713315 52494939325312831949569973)
                  ·
                    refine ⟨4921400561748077995272185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52494939325312831949569973 4921400561748077995272185)
                    ·
                      refine ⟨3691050421311058496454139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921400561748077995272185 3691050421311058496454139)
                      ·
                        rfl

theorem cell23_7188295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_7188295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188295 prefixEnd_7188295 := by exact prefixLift 7188295
  have htrace : WordTrace (prefixWord ++ tailWord_7188295) baseStart_7188295 baseEnd_7188295 := by
    simpa [prefixWord, tailWord_7188295, baseEnd_7188295] using wordTrace_append hprefix tailTrace_7188295
  have hstable : (prefixWord ++ tailWord_7188295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188295).length < 2 ^ (prefixWord ++ tailWord_7188295).sum := by decide
  have hdescent : baseEnd_7188295 < baseStart_7188295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188305 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 1, 5]
def baseStart_7188305 : Nat := 118140960795 + 7188305 * 2 ^ 59
def prefixEnd_7188305 : Nat := 4983230072969 + 3 ^ 40 * 7188305 * 2
def baseEnd_7188305 : Nat := 1230351852039201152443031

theorem tailTrace_7188305 : CollatzResearch.WordTrace tailWord_7188305 prefixEnd_7188305 1230351852039201152443031 := by
  unfold tailWord_7188305
  simp only [CollatzResearch.WordTrace]
  refine ⟨262179022223006124599726369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174786014815337416399817579 262179022223006124599726369)
  ·
    refine ⟨196634266667254593449794777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262179022223006124599726369 196634266667254593449794777)
    ·
      refine ⟨147475700000440945087346083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196634266667254593449794777 147475700000440945087346083)
      ·
        refine ⟨221213550000661417631019125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147475700000440945087346083 221213550000661417631019125)
        ·
          refine ⟨20738770312562007902908043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221213550000661417631019125 20738770312562007902908043)
          ·
            refine ⟨31108155468843011854362065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20738770312562007902908043 31108155468843011854362065)
            ·
              refine ⟨23331116601632258890771549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31108155468843011854362065 23331116601632258890771549)
              ·
                refine ⟨8749168725612097084039331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23331116601632258890771549 8749168725612097084039331)
                ·
                  refine ⟨13123753088418145626058997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8749168725612097084039331 13123753088418145626058997)
                  ·
                    refine ⟨1230351852039201152443031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13123753088418145626058997 1230351852039201152443031)
                    ·
                      rfl

theorem cell23_7188305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_7188305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188305 prefixEnd_7188305 := by exact prefixLift 7188305
  have htrace : WordTrace (prefixWord ++ tailWord_7188305) baseStart_7188305 baseEnd_7188305 := by
    simpa [prefixWord, tailWord_7188305, baseEnd_7188305] using wordTrace_append hprefix tailTrace_7188305
  have hstable : (prefixWord ++ tailWord_7188305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188305).length < 2 ^ (prefixWord ++ tailWord_7188305).sum := by decide
  have hdescent : baseEnd_7188305 < baseStart_7188305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188345 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 3]
def baseStart_7188345 : Nat := 118140960795 + 7188345 * 2 ^ 59
def prefixEnd_7188345 : Nat := 4983230072969 + 3 ^ 40 * 7188345 * 2
def baseEnd_7188345 : Nat := 3691076095343783300828909

theorem tailTrace_7188345 : CollatzResearch.WordTrace tailWord_7188345 prefixEnd_7188345 3691076095343783300828909 := by
  unfold tailWord_7188345
  simp only [CollatzResearch.WordTrace]
  refine ⟨262180481142861211431182489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174786987428574140954121659 262180481142861211431182489)
  ·
    refine ⟨196635360857145908573386867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262180481142861211431182489 196635360857145908573386867)
    ·
      refine ⟨294953041285718862860080301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196635360857145908573386867 294953041285718862860080301)
      ·
        refine ⟨110607390482144573572530113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294953041285718862860080301 110607390482144573572530113)
        ·
          refine ⟨82955542861608430179397585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110607390482144573572530113 82955542861608430179397585)
          ·
            refine ⟨62216657146206322634548189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82955542861608430179397585 62216657146206322634548189)
            ·
              refine ⟨23331246429827370987955571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62216657146206322634548189 23331246429827370987955571)
              ·
                refine ⟨34996869644741056481933357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23331246429827370987955571 34996869644741056481933357)
                ·
                  refine ⟨13123826116777896180725009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34996869644741056481933357 13123826116777896180725009)
                  ·
                    refine ⟨9842869587583422135543757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13123826116777896180725009 9842869587583422135543757)
                    ·
                      refine ⟨3691076095343783300828909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9842869587583422135543757 3691076095343783300828909)
                      ·
                        rfl

theorem cell23_7188345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_7188345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188345 prefixEnd_7188345 := by exact prefixLift 7188345
  have htrace : WordTrace (prefixWord ++ tailWord_7188345) baseStart_7188345 baseEnd_7188345 := by
    simpa [prefixWord, tailWord_7188345, baseEnd_7188345] using wordTrace_append hprefix tailTrace_7188345
  have hstable : (prefixWord ++ tailWord_7188345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188345).length < 2 ^ (prefixWord ++ tailWord_7188345).sum := by decide
  have hdescent : baseEnd_7188345 < baseStart_7188345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188355 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 4]
def baseStart_7188355 : Nat := 118140960795 + 7188355 * 2 ^ 59
def prefixEnd_7188355 : Nat := 4983230072969 + 3 ^ 40 * 7188355 * 2
def baseEnd_7188355 : Nat := 3691081230150328261703863

theorem tailTrace_7188355 : CollatzResearch.WordTrace tailWord_7188355 prefixEnd_7188355 3691081230150328261703863 := by
  unfold tailWord_7188355
  simp only [CollatzResearch.WordTrace]
  refine ⟨262180845872824983139046519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174787230581883322092697679 262180845872824983139046519)
  ·
    refine ⟨393271268809237474708569779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262180845872824983139046519 393271268809237474708569779)
    ·
      refine ⟨589906903213856212062854669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393271268809237474708569779 589906903213856212062854669)
      ·
        refine ⟨221215088705196079523570501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589906903213856212062854669 221215088705196079523570501)
        ·
          refine ⟨41477829132224264910669469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221215088705196079523570501 41477829132224264910669469)
          ·
            refine ⟨15554185924584099341501051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41477829132224264910669469 15554185924584099341501051)
            ·
              refine ⟨23331278886876149012251577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15554185924584099341501051 23331278886876149012251577)
              ·
                refine ⟨17498459165157111759188683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23331278886876149012251577 17498459165157111759188683)
                ·
                  refine ⟨26247688747735667638783025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17498459165157111759188683 26247688747735667638783025)
                  ·
                    refine ⟨19685766560801750729087269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26247688747735667638783025 19685766560801750729087269)
                    ·
                      refine ⟨3691081230150328261703863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19685766560801750729087269 3691081230150328261703863)
                      ·
                        rfl

theorem cell23_7188355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_7188355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188355 prefixEnd_7188355 := by exact prefixLift 7188355
  have htrace : WordTrace (prefixWord ++ tailWord_7188355) baseStart_7188355 baseEnd_7188355 := by
    simpa [prefixWord, tailWord_7188355, baseEnd_7188355] using wordTrace_append hprefix tailTrace_7188355
  have hstable : (prefixWord ++ tailWord_7188355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188355).length < 2 ^ (prefixWord ++ tailWord_7188355).sum := by decide
  have hdescent : baseEnd_7188355 < baseStart_7188355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188359 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_7188359 : Nat := 118140960795 + 7188359 * 2 ^ 59
def prefixEnd_7188359 : Nat := 4983230072969 + 3 ^ 40 * 7188359 * 2
def baseEnd_7188359 : Nat := 3691083284072946246053845

theorem tailTrace_7188359 : CollatzResearch.WordTrace tailWord_7188359 prefixEnd_7188359 3691083284072946246053845 := by
  unfold tailWord_7188359
  simp only [CollatzResearch.WordTrace]
  refine ⟨262180991764810491822192131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174787327843206994548128087 262180991764810491822192131)
  ·
    refine ⟨393271487647215737733288197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262180991764810491822192131 393271487647215737733288197)
    ·
      refine ⟨73738403933852950824991537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393271487647215737733288197 73738403933852950824991537)
      ·
        refine ⟨55303802950389713118743653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73738403933852950824991537 55303802950389713118743653)
        ·
          refine ⟨10369463053198071209764435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55303802950389713118743653 10369463053198071209764435)
          ·
            refine ⟨15554194579797106814646653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10369463053198071209764435 15554194579797106814646653)
            ·
              refine ⟨5832822967423915055492495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15554194579797106814646653 5832822967423915055492495)
              ·
                refine ⟨8749234451135872583238743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832822967423915055492495 8749234451135872583238743)
                ·
                  refine ⟨13123851676703808874858115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8749234451135872583238743 13123851676703808874858115)
                  ·
                    refine ⟨19685777515055713312287173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13123851676703808874858115 19685777515055713312287173)
                    ·
                      refine ⟨3691083284072946246053845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19685777515055713312287173 3691083284072946246053845)
                      ·
                        rfl

theorem cell23_7188359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_7188359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188359 prefixEnd_7188359 := by exact prefixLift 7188359
  have htrace : WordTrace (prefixWord ++ tailWord_7188359) baseStart_7188359 baseEnd_7188359 := by
    simpa [prefixWord, tailWord_7188359, baseEnd_7188359] using wordTrace_append hprefix tailTrace_7188359
  have hstable : (prefixWord ++ tailWord_7188359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188359).length < 2 ^ (prefixWord ++ tailWord_7188359).sum := by decide
  have hdescent : baseEnd_7188359 < baseStart_7188359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188408 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 1, 8]
def baseStart_7188408 : Nat := 118140960795 + 7188408 * 2 ^ 59
def prefixEnd_7188408 : Nat := 4983230072969 + 3 ^ 40 * 7188408 * 2
def baseEnd_7188408 : Nat := 1230369481541672184780373

theorem tailTrace_7188408 : CollatzResearch.WordTrace tailWord_7188408 prefixEnd_7188408 1230369481541672184780373 := by
  unfold tailWord_7188408
  simp only [CollatzResearch.WordTrace]
  refine ⟨131091389470816486595362939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174788519294421982127150585 131091389470816486595362939)
  ·
    refine ⟨196637084206224729893044409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131091389470816486595362939 196637084206224729893044409)
    ·
      refine ⟨147477813154668547419783307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196637084206224729893044409 147477813154668547419783307)
      ·
        refine ⟨221216719732002821129674961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147477813154668547419783307 221216719732002821129674961)
        ·
          refine ⟨165912539799002115847256221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221216719732002821129674961 165912539799002115847256221)
          ·
            refine ⟨62217202424625793442721083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165912539799002115847256221 62217202424625793442721083)
            ·
              refine ⟨93325803636938690164081625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62217202424625793442721083 93325803636938690164081625)
              ·
                refine ⟨69994352727704017623061219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93325803636938690164081625 69994352727704017623061219)
                ·
                  refine ⟨104991529091556026434591829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69994352727704017623061219 104991529091556026434591829)
                  ·
                    refine ⟨1230369481541672184780373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104991529091556026434591829 1230369481541672184780373)
                    ·
                      rfl

theorem cell23_7188408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_7188408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188408 prefixEnd_7188408 := by exact prefixLift 7188408
  have htrace : WordTrace (prefixWord ++ tailWord_7188408) baseStart_7188408 baseEnd_7188408 := by
    simpa [prefixWord, tailWord_7188408, baseEnd_7188408] using wordTrace_append hprefix tailTrace_7188408
  have hstable : (prefixWord ++ tailWord_7188408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188408).length < 2 ^ (prefixWord ++ tailWord_7188408).sum := by decide
  have hdescent : baseEnd_7188408 < baseStart_7188408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188448 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_7188448 : Nat := 118140960795 + 7188448 * 2 ^ 59
def prefixEnd_7188448 : Nat := 4983230072969 + 3 ^ 40 * 7188448 * 2
def baseEnd_7188448 : Nat := 3691128983851196397840935

theorem tailTrace_7188448 : CollatzResearch.WordTrace tailWord_7188448 prefixEnd_7188448 3691128983851196397840935 := by
  unfold tailWord_7188448
  simp only [CollatzResearch.WordTrace]
  refine ⟨131092118930744030011090999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174789491907658706681454665 131092118930744030011090999)
  ·
    refine ⟨196638178396116045016636499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131092118930744030011090999 196638178396116045016636499)
    ·
      refine ⟨294957267594174067524954749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196638178396116045016636499 294957267594174067524954749)
      ·
        refine ⟨110608975347815275321858031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294957267594174067524954749 110608975347815275321858031)
        ·
          refine ⟨165913463021722912982787047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110608975347815275321858031 165913463021722912982787047)
          ·
            refine ⟨248870194532584369474180571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165913463021722912982787047 248870194532584369474180571)
            ·
              refine ⟨373305291798876554211270857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248870194532584369474180571 373305291798876554211270857)
              ·
                refine ⟨279978968849157415658453143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373305291798876554211270857 279978968849157415658453143)
                ·
                  refine ⟨419968453273736123487679715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279978968849157415658453143 419968453273736123487679715)
                  ·
                    refine ⟨629952679910604185231519573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 419968453273736123487679715 629952679910604185231519573)
                    ·
                      refine ⟨3691128983851196397840935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 629952679910604185231519573 3691128983851196397840935)
                      ·
                        rfl

theorem cell23_7188448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_7188448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188448 prefixEnd_7188448 := by exact prefixLift 7188448
  have htrace : WordTrace (prefixWord ++ tailWord_7188448) baseStart_7188448 baseEnd_7188448 := by
    simpa [prefixWord, tailWord_7188448, baseEnd_7188448] using wordTrace_append hprefix tailTrace_7188448
  have hstable : (prefixWord ++ tailWord_7188448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188448).length < 2 ^ (prefixWord ++ tailWord_7188448).sum := by decide
  have hdescent : baseEnd_7188448 < baseStart_7188448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188449 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_7188449 : Nat := 118140960795 + 7188449 * 2 ^ 59
def prefixEnd_7188449 : Nat := 4983230072969 + 3 ^ 40 * 7188449 * 2
def baseEnd_7188449 : Nat := 3691129497331850893928431

theorem tailTrace_7188449 : CollatzResearch.WordTrace tailWord_7188449 prefixEnd_7188449 3691129497331850893928431 := by
  unfold tailWord_7188449
  simp only [CollatzResearch.WordTrace]
  refine ⟨262184274334484437192968401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174789516222989624795312267 262184274334484437192968401)
  ·
    refine ⟨196638205750863327894726301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262184274334484437192968401 196638205750863327894726301)
    ·
      refine ⟨73739327156573747960522363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196638205750863327894726301 73739327156573747960522363)
      ·
        refine ⟨110608990734860621940783545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73739327156573747960522363 110608990734860621940783545)
        ·
          refine ⟨82956743051145466455587659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110608990734860621940783545 82956743051145466455587659)
          ·
            refine ⟨124435114576718199683381489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82956743051145466455587659 124435114576718199683381489)
            ·
              refine ⟨93326335932538649762536117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124435114576718199683381489 93326335932538649762536117)
              ·
                refine ⟨8749343993675498415237761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93326335932538649762536117 8749343993675498415237761)
                ·
                  refine ⟨6562007995256623811428321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8749343993675498415237761 6562007995256623811428321)
                  ·
                    refine ⟨4921505996442467858571241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562007995256623811428321 4921505996442467858571241)
                    ·
                      refine ⟨3691129497331850893928431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921505996442467858571241 3691129497331850893928431)
                      ·
                        rfl

theorem cell23_7188449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_7188449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188449 prefixEnd_7188449 := by exact prefixLift 7188449
  have htrace : WordTrace (prefixWord ++ tailWord_7188449) baseStart_7188449 baseEnd_7188449 := by
    simpa [prefixWord, tailWord_7188449, baseEnd_7188449] using wordTrace_append hprefix tailTrace_7188449
  have hstable : (prefixWord ++ tailWord_7188449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188449).length < 2 ^ (prefixWord ++ tailWord_7188449).sum := by decide
  have hdescent : baseEnd_7188449 < baseStart_7188449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188472 : List Nat := [2, 1, 2, 1, 1, 3, 5, 3, 5]
def baseStart_7188472 : Nat := 118140960795 + 7188472 * 2 ^ 59
def prefixEnd_7188472 : Nat := 4983230072969 + 3 ^ 40 * 7188472 * 2
def baseEnd_7188472 : Nat := 410126811931878255993425

theorem tailTrace_7188472 : CollatzResearch.WordTrace tailWord_7188472 prefixEnd_7188472 410126811931878255993425 := by
  unfold tailWord_7188472
  simp only [CollatzResearch.WordTrace]
  refine ⟨131092556606700556060527835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174790075475600741414037113 131092556606700556060527835)
  ·
    refine ⟨196638834910050834090791753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131092556606700556060527835 196638834910050834090791753)
    ·
      refine ⟨147479126182538125568093815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196638834910050834090791753 147479126182538125568093815)
      ·
        refine ⟨221218689273807188352140723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147479126182538125568093815 221218689273807188352140723)
        ·
          refine ⟨331828033910710782528211085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221218689273807188352140723 331828033910710782528211085)
          ·
            refine ⟨124435512716516543448079157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331828033910710782528211085 124435512716516543448079157)
            ·
              refine ⟨11665829317173425948257421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124435512716516543448079157 11665829317173425948257421)
              ·
                refine ⟨4374685993940034730596533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11665829317173425948257421 4374685993940034730596533)
                ·
                  refine ⟨410126811931878255993425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4374685993940034730596533 410126811931878255993425)
                  ·
                    rfl

theorem cell23_7188472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 5].length) (baseStart_7188472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188472 prefixEnd_7188472 := by exact prefixLift 7188472
  have htrace : WordTrace (prefixWord ++ tailWord_7188472) baseStart_7188472 baseEnd_7188472 := by
    simpa [prefixWord, tailWord_7188472, baseEnd_7188472] using wordTrace_append hprefix tailTrace_7188472
  have hstable : (prefixWord ++ tailWord_7188472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188472).length < 2 ^ (prefixWord ++ tailWord_7188472).sum := by decide
  have hdescent : baseEnd_7188472 < baseStart_7188472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188485 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_7188485 : Nat := 118140960795 + 7188485 * 2 ^ 59
def prefixEnd_7188485 : Nat := 4983230072969 + 3 ^ 40 * 7188485 * 2
def baseEnd_7188485 : Nat := 1230382660878470917692755

theorem tailTrace_7188485 : CollatzResearch.WordTrace tailWord_7188485 prefixEnd_7188485 1230382660878470917692755 := by
  unfold tailWord_7188485
  simp only [CollatzResearch.WordTrace]
  refine ⟨262185587362354015341278909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174790391574902676894185939 262185587362354015341278909)
  ·
    refine ⟨98319595260882755752979591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262185587362354015341278909 98319595260882755752979591)
    ·
      refine ⟨147479392891324133629469387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98319595260882755752979591 147479392891324133629469387)
      ·
        refine ⟨221219089336986200444204081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147479392891324133629469387 221219089336986200444204081)
        ·
          refine ⟨165914317002739650333153061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221219089336986200444204081 165914317002739650333153061)
          ·
            refine ⟨31108934438013684437466199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165914317002739650333153061 31108934438013684437466199)
            ·
              refine ⟨46663401657020526656199299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31108934438013684437466199 46663401657020526656199299)
              ·
                refine ⟨69995102485530789984298949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46663401657020526656199299 69995102485530789984298949)
                ·
                  refine ⟨13124081716037023122056053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69995102485530789984298949 13124081716037023122056053)
                  ·
                    refine ⟨1230382660878470917692755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13124081716037023122056053 1230382660878470917692755)
                    ·
                      rfl

theorem cell23_7188485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_7188485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188485 prefixEnd_7188485 := by exact prefixLift 7188485
  have htrace : WordTrace (prefixWord ++ tailWord_7188485) baseStart_7188485 baseEnd_7188485 := by
    simpa [prefixWord, tailWord_7188485, baseEnd_7188485] using wordTrace_append hprefix tailTrace_7188485
  have hstable : (prefixWord ++ tailWord_7188485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188485).length < 2 ^ (prefixWord ++ tailWord_7188485).sum := by decide
  have hdescent : baseEnd_7188485 < baseStart_7188485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188492 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 2, 5, 2]
def baseStart_7188492 : Nat := 118140960795 + 7188492 * 2 ^ 59
def prefixEnd_7188492 : Nat := 4983230072969 + 3 ^ 40 * 7188492 * 2
def baseEnd_7188492 : Nat := 3691151576999994225690733

theorem tailTrace_7188492 : CollatzResearch.WordTrace tailWord_7188492 prefixEnd_7188492 3691151576999994225690733 := by
  unfold tailWord_7188492
  simp only [CollatzResearch.WordTrace]
  refine ⟨131092921336664327768391865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174790561782219103691189153 131092921336664327768391865)
  ·
    refine ⟨98319691002498245826293899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131092921336664327768391865 98319691002498245826293899)
    ·
      refine ⟨147479536503747368739440849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98319691002498245826293899 147479536503747368739440849)
      ·
        refine ⟨110609652377810526554580637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147479536503747368739440849 110609652377810526554580637)
        ·
          refine ⟨41478619641678947457967739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110609652377810526554580637 41478619641678947457967739)
          ·
            refine ⟨62217929462518421186951609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41478619641678947457967739 62217929462518421186951609)
            ·
              refine ⟨46663447096888815890213707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62217929462518421186951609 46663447096888815890213707)
              ·
                refine ⟨69995170645333223835320561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46663447096888815890213707 69995170645333223835320561)
                ·
                  refine ⟨52496377983999917876490421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69995170645333223835320561 52496377983999917876490421)
                  ·
                    refine ⟨4921535435999992300920977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52496377983999917876490421 4921535435999992300920977)
                    ·
                      refine ⟨3691151576999994225690733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921535435999992300920977 3691151576999994225690733)
                      ·
                        rfl

theorem cell23_7188492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_7188492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188492 prefixEnd_7188492 := by exact prefixLift 7188492
  have htrace : WordTrace (prefixWord ++ tailWord_7188492) baseStart_7188492 baseEnd_7188492 := by
    simpa [prefixWord, tailWord_7188492, baseEnd_7188492] using wordTrace_append hprefix tailTrace_7188492
  have hstable : (prefixWord ++ tailWord_7188492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188492).length < 2 ^ (prefixWord ++ tailWord_7188492).sum := by decide
  have hdescent : baseEnd_7188492 < baseStart_7188492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188500 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7188500 : Nat := 118140960795 + 7188500 * 2 ^ 59
def prefixEnd_7188500 : Nat := 4983230072969 + 3 ^ 40 * 7188500 * 2
def baseEnd_7188500 : Nat := 3691155684845230194390697

theorem tailTrace_7188500 : CollatzResearch.WordTrace tailWord_7188500 prefixEnd_7188500 3691155684845230194390697 := by
  unfold tailWord_7188500
  simp only [CollatzResearch.WordTrace]
  refine ⟨131093067228649836451537477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174790756304866448602049969 131093067228649836451537477)
  ·
    refine ⟨24579950105371844334663277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131093067228649836451537477 24579950105371844334663277)
    ·
      refine ⟨9217481289514441625498729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24579950105371844334663277 9217481289514441625498729)
      ·
        refine ⟨6913110967135831219124047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9217481289514441625498729 6913110967135831219124047)
        ·
          refine ⟨10369666450703746828686071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6913110967135831219124047 10369666450703746828686071)
          ·
            refine ⟨15554499676055620243029107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10369666450703746828686071 15554499676055620243029107)
            ·
              refine ⟨23331749514083430364543661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15554499676055620243029107 23331749514083430364543661)
              ·
                refine ⟨8749406067781286386703873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23331749514083430364543661 8749406067781286386703873)
                ·
                  refine ⟨6562054550835964790027905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8749406067781286386703873 6562054550835964790027905)
                  ·
                    refine ⟨4921540913126973592520929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562054550835964790027905 4921540913126973592520929)
                    ·
                      refine ⟨3691155684845230194390697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921540913126973592520929 3691155684845230194390697)
                      ·
                        rfl

theorem cell23_7188500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7188500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188500 prefixEnd_7188500 := by exact prefixLift 7188500
  have htrace : WordTrace (prefixWord ++ tailWord_7188500) baseStart_7188500 baseEnd_7188500 := by
    simpa [prefixWord, tailWord_7188500, baseEnd_7188500] using wordTrace_append hprefix tailTrace_7188500
  have hstable : (prefixWord ++ tailWord_7188500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188500).length < 2 ^ (prefixWord ++ tailWord_7188500).sum := by decide
  have hdescent : baseEnd_7188500 < baseStart_7188500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188505 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_7188505 : Nat := 118140960795 + 7188505 * 2 ^ 59
def prefixEnd_7188505 : Nat := 4983230072969 + 3 ^ 40 * 7188505 * 2
def baseEnd_7188505 : Nat := 3691158252248502674828173

theorem tailTrace_7188505 : CollatzResearch.WordTrace tailWord_7188505 prefixEnd_7188505 3691158252248502674828173 := by
  unfold tailWord_7188505
  simp only [CollatzResearch.WordTrace]
  refine ⟨262186316822281558757006969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174790877881521039171337979 262186316822281558757006969)
  ·
    refine ⟨196639737616711169067755227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262186316822281558757006969 196639737616711169067755227)
    ·
      refine ⟨294959606425066753601632841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196639737616711169067755227 294959606425066753601632841)
      ·
        refine ⟨221219704818800065201224631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294959606425066753601632841 221219704818800065201224631)
        ·
          refine ⟨331829557228200097801836947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221219704818800065201224631 331829557228200097801836947)
          ·
            refine ⟨497744335842300146702755421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331829557228200097801836947 497744335842300146702755421)
            ·
              refine ⟨186654125940862555013533283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497744335842300146702755421 186654125940862555013533283)
              ·
                refine ⟨279981188911293832520299925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186654125940862555013533283 279981188911293832520299925)
                ·
                  refine ⟨13124118230216898399389059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 279981188911293832520299925 13124118230216898399389059)
                  ·
                    refine ⟨19686177345325347599083589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13124118230216898399389059 19686177345325347599083589)
                    ·
                      refine ⟨3691158252248502674828173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19686177345325347599083589 3691158252248502674828173)
                      ·
                        rfl

theorem cell23_7188505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_7188505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188505 prefixEnd_7188505 := by exact prefixLift 7188505
  have htrace : WordTrace (prefixWord ++ tailWord_7188505) baseStart_7188505 baseEnd_7188505 := by
    simpa [prefixWord, tailWord_7188505, baseEnd_7188505] using wordTrace_append hprefix tailTrace_7188505
  have hstable : (prefixWord ++ tailWord_7188505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188505).length < 2 ^ (prefixWord ++ tailWord_7188505).sum := by decide
  have hdescent : baseEnd_7188505 < baseStart_7188505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188566 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_7188566 : Nat := 118140960795 + 7188566 * 2 ^ 59
def prefixEnd_7188566 : Nat := 4983230072969 + 3 ^ 40 * 7188566 * 2
def baseEnd_7188566 : Nat := 1230396524856142312055131

theorem tailTrace_7188566 : CollatzResearch.WordTrace tailWord_7188566 prefixEnd_7188566 1230396524856142312055131 := by
  unfold tailWord_7188566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16386783854691285385936097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174792361116707044116651701 16386783854691285385936097)
  ·
    refine ⟨12290087891018464039452073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16386783854691285385936097 12290087891018464039452073)
    ·
      refine ⟨9217565918263848029589055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12290087891018464039452073 9217565918263848029589055)
      ·
        refine ⟨13826348877395772044383583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9217565918263848029589055 13826348877395772044383583)
        ·
          refine ⟨20739523316093658066575375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13826348877395772044383583 20739523316093658066575375)
          ·
            refine ⟨31109284974140487099863063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20739523316093658066575375 31109284974140487099863063)
            ·
              refine ⟨46663927461210730649794595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31109284974140487099863063 46663927461210730649794595)
              ·
                refine ⟨69995891191816095974691893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46663927461210730649794595 69995891191816095974691893)
                ·
                  refine ⟨6562114799232758997627365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69995891191816095974691893 6562114799232758997627365)
                  ·
                    refine ⟨1230396524856142312055131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6562114799232758997627365 1230396524856142312055131)
                    ·
                      rfl

theorem cell23_7188566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_7188566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188566 prefixEnd_7188566 := by exact prefixLift 7188566
  have htrace : WordTrace (prefixWord ++ tailWord_7188566) baseStart_7188566 baseEnd_7188566 := by
    simpa [prefixWord, tailWord_7188566, baseEnd_7188566] using wordTrace_append hprefix tailTrace_7188566
  have hstable : (prefixWord ++ tailWord_7188566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188566).length < 2 ^ (prefixWord ++ tailWord_7188566).sum := by decide
  have hdescent : baseEnd_7188566 < baseStart_7188566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188589 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_7188589 : Nat := 118140960795 + 7188589 * 2 ^ 59
def prefixEnd_7188589 : Nat := 4983230072969 + 3 ^ 40 * 7188589 * 2
def baseEnd_7188589 : Nat := 3691201384623480346177787

theorem tailTrace_7188589 : CollatzResearch.WordTrace tailWord_7188589 prefixEnd_7188589 3691201384623480346177787 := by
  unfold tailWord_7188589
  simp only [CollatzResearch.WordTrace]
  refine ⟨262189380553977241103064821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174792920369318160735376547 262189380553977241103064821)
  ·
    refine ⟨24580254426935366353412327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262189380553977241103064821 24580254426935366353412327)
    ·
      refine ⟨36870381640403049530118491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24580254426935366353412327 36870381640403049530118491)
      ·
        refine ⟨55305572460604574295177737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36870381640403049530118491 55305572460604574295177737)
        ·
          refine ⟨41479179345453430721383303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55305572460604574295177737 41479179345453430721383303)
          ·
            refine ⟨62218769018180146082074955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41479179345453430721383303 62218769018180146082074955)
            ·
              refine ⟨93328153527270219123112433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62218769018180146082074955 93328153527270219123112433)
              ·
                refine ⟨69996115145452664342334325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93328153527270219123112433 69996115145452664342334325)
                ·
                  refine ⟨6562135794886187282093843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69996115145452664342334325 6562135794886187282093843)
                  ·
                    refine ⟨9843203692329280923140765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6562135794886187282093843 9843203692329280923140765)
                    ·
                      refine ⟨3691201384623480346177787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9843203692329280923140765 3691201384623480346177787)
                      ·
                        rfl

theorem cell23_7188589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_7188589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188589 prefixEnd_7188589 := by exact prefixLift 7188589
  have htrace : WordTrace (prefixWord ++ tailWord_7188589) baseStart_7188589 baseEnd_7188589 := by
    simpa [prefixWord, tailWord_7188589, baseEnd_7188589] using wordTrace_append hprefix tailTrace_7188589
  have hstable : (prefixWord ++ tailWord_7188589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188589).length < 2 ^ (prefixWord ++ tailWord_7188589).sum := by decide
  have hdescent : baseEnd_7188589 < baseStart_7188589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188629 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_7188629 : Nat := 118140960795 + 7188629 * 2 ^ 59
def prefixEnd_7188629 : Nat := 4983230072969 + 3 ^ 40 * 7188629 * 2
def baseEnd_7188629 : Nat := 3691221923849660189677603

theorem tailTrace_7188629 : CollatzResearch.WordTrace tailWord_7188629 prefixEnd_7188629 3691221923849660189677603 := by
  unfold tailWord_7188629
  simp only [CollatzResearch.WordTrace]
  refine ⟨262190839473832327934520941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174793892982554885289680627 262190839473832327934520941)
  ·
    refine ⟨98321564802687122975445353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262190839473832327934520941 98321564802687122975445353)
    ·
      refine ⟨73741173602015342231584015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98321564802687122975445353 73741173602015342231584015)
      ·
        refine ⟨110611760403023013347376023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73741173602015342231584015 110611760403023013347376023)
        ·
          refine ⟨165917640604534520021064035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110611760403023013347376023 165917640604534520021064035)
          ·
            refine ⟨248876460906801780031596053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165917640604534520021064035 248876460906801780031596053)
            ·
              refine ⟨11666084105006333438981065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248876460906801780031596053 11666084105006333438981065)
              ·
                refine ⟨8749563078754750079235799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11666084105006333438981065 8749563078754750079235799)
                ·
                  refine ⟨13124344618132125118853699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8749563078754750079235799 13124344618132125118853699)
                  ·
                    refine ⟨19686516927198187678280549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13124344618132125118853699 19686516927198187678280549)
                    ·
                      refine ⟨3691221923849660189677603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19686516927198187678280549 3691221923849660189677603)
                      ·
                        rfl

theorem cell23_7188629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_7188629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188629 prefixEnd_7188629 := by exact prefixLift 7188629
  have htrace : WordTrace (prefixWord ++ tailWord_7188629) baseStart_7188629 baseEnd_7188629 := by
    simpa [prefixWord, tailWord_7188629, baseEnd_7188629] using wordTrace_append hprefix tailTrace_7188629
  have hstable : (prefixWord ++ tailWord_7188629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188629).length < 2 ^ (prefixWord ++ tailWord_7188629).sum := by decide
  have hdescent : baseEnd_7188629 < baseStart_7188629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188639 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 4, 4]
def baseStart_7188639 : Nat := 118140960795 + 7188639 * 2 ^ 59
def prefixEnd_7188639 : Nat := 4983230072969 + 3 ^ 40 * 7188639 * 2
def baseEnd_7188639 : Nat := 1230409019552068383517519

theorem tailTrace_7188639 : CollatzResearch.WordTrace tailWord_7188639 prefixEnd_7188639 1230409019552068383517519 := by
  unfold tailWord_7188639
  simp only [CollatzResearch.WordTrace]
  refine ⟨262191204203796099642384971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174794136135864066428256647 262191204203796099642384971)
  ·
    refine ⟨393286806305694149463577457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262191204203796099642384971 393286806305694149463577457)
    ·
      refine ⟨294965104729270612097683093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393286806305694149463577457 294965104729270612097683093)
      ·
        refine ⟨13826489284184559942078895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 294965104729270612097683093 13826489284184559942078895)
        ·
          refine ⟨20739733926276839913118343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13826489284184559942078895 20739733926276839913118343)
          ·
            refine ⟨31109600889415259869677515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20739733926276839913118343 31109600889415259869677515)
            ·
              refine ⟨46664401334122889804516273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31109600889415259869677515 46664401334122889804516273)
              ·
                refine ⟨34998301000592167353387205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46664401334122889804516273 34998301000592167353387205)
                ·
                  refine ⟨6562181437611031378760101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34998301000592167353387205 6562181437611031378760101)
                  ·
                    refine ⟨1230409019552068383517519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6562181437611031378760101 1230409019552068383517519)
                    ·
                      rfl

theorem cell23_7188639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 4].length) (baseStart_7188639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188639 prefixEnd_7188639 := by exact prefixLift 7188639
  have htrace : WordTrace (prefixWord ++ tailWord_7188639) baseStart_7188639 baseEnd_7188639 := by
    simpa [prefixWord, tailWord_7188639, baseEnd_7188639] using wordTrace_append hprefix tailTrace_7188639
  have hstable : (prefixWord ++ tailWord_7188639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188639).length < 2 ^ (prefixWord ++ tailWord_7188639).sum := by decide
  have hdescent : baseEnd_7188639 < baseStart_7188639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188663 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 3, 2, 2]
def baseStart_7188663 : Nat := 118140960795 + 7188663 * 2 ^ 59
def prefixEnd_7188663 : Nat := 4983230072969 + 3 ^ 40 * 7188663 * 2
def baseEnd_7188663 : Nat := 3691239382191913056652447

theorem tailTrace_7188663 : CollatzResearch.WordTrace tailWord_7188663 prefixEnd_7188663 3691239382191913056652447 := by
  unfold tailWord_7188663
  simp only [CollatzResearch.WordTrace]
  refine ⟨262192079555709151741258643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174794719703806101160839095 262192079555709151741258643)
  ·
    refine ⟨393288119333563727611887965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262192079555709151741258643 393288119333563727611887965)
    ·
      refine ⟨147483044750086397854457987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393288119333563727611887965 147483044750086397854457987)
      ·
        refine ⟨221224567125129596781686981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147483044750086397854457987 221224567125129596781686981)
        ·
          refine ⟨41479606335961799396566309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221224567125129596781686981 41479606335961799396566309)
          ·
            refine ⟨7777426187992837386856183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41479606335961799396566309 7777426187992837386856183)
            ·
              refine ⟨11666139281989256080284275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777426187992837386856183 11666139281989256080284275)
              ·
                refine ⟨17499208922983884120426413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11666139281989256080284275 17499208922983884120426413)
                ·
                  refine ⟨6562203346118956545159905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17499208922983884120426413 6562203346118956545159905)
                  ·
                    refine ⟨4921652509589217408869929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562203346118956545159905 4921652509589217408869929)
                    ·
                      refine ⟨3691239382191913056652447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921652509589217408869929 3691239382191913056652447)
                      ·
                        rfl

theorem cell23_7188663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_7188663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188663 prefixEnd_7188663 := by exact prefixLift 7188663
  have htrace : WordTrace (prefixWord ++ tailWord_7188663) baseStart_7188663 baseEnd_7188663 := by
    simpa [prefixWord, tailWord_7188663, baseEnd_7188663] using wordTrace_append hprefix tailTrace_7188663
  have hstable : (prefixWord ++ tailWord_7188663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188663).length < 2 ^ (prefixWord ++ tailWord_7188663).sum := by decide
  have hdescent : baseEnd_7188663 < baseStart_7188663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188673 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7188673 : Nat := 118140960795 + 7188673 * 2 ^ 59
def prefixEnd_7188673 : Nat := 4983230072969 + 3 ^ 40 * 7188673 * 2
def baseEnd_7188673 : Nat := 1230414838999486005842467

theorem tailTrace_7188673 : CollatzResearch.WordTrace tailWord_7188673 prefixEnd_7188673 1230414838999486005842467 := by
  unfold tailWord_7188673
  simp only [CollatzResearch.WordTrace]
  refine ⟨262192444285672923449122673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174794962857115282299415115 262192444285672923449122673)
  ·
    refine ⟨196644333214254692586842005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262192444285672923449122673 196644333214254692586842005)
    ·
      refine ⟨9217703119418188715008219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196644333214254692586842005 9217703119418188715008219)
      ·
        refine ⟨13826554679127283072512329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9217703119418188715008219 13826554679127283072512329)
        ·
          refine ⟨10369916009345462304384247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13826554679127283072512329 10369916009345462304384247)
          ·
            refine ⟨15554874014018193456576371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10369916009345462304384247 15554874014018193456576371)
            ·
              refine ⟨23332311021027290184864557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15554874014018193456576371 23332311021027290184864557)
              ·
                refine ⟨8749616632885233819324209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23332311021027290184864557 8749616632885233819324209)
                ·
                  refine ⟨6562212474663925364493157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8749616632885233819324209 6562212474663925364493157)
                  ·
                    refine ⟨1230414838999486005842467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6562212474663925364493157 1230414838999486005842467)
                    ·
                      rfl

theorem cell23_7188673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7188673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188673 prefixEnd_7188673 := by exact prefixLift 7188673
  have htrace : WordTrace (prefixWord ++ tailWord_7188673) baseStart_7188673 baseEnd_7188673 := by
    simpa [prefixWord, tailWord_7188673, baseEnd_7188673] using wordTrace_append hprefix tailTrace_7188673
  have hstable : (prefixWord ++ tailWord_7188673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188673).length < 2 ^ (prefixWord ++ tailWord_7188673).sum := by decide
  have hdescent : baseEnd_7188673 < baseStart_7188673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188700 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7188700 : Nat := 118140960795 + 7188700 * 2 ^ 59
def prefixEnd_7188700 : Nat := 4983230072969 + 3 ^ 40 * 7188700 * 2
def baseEnd_7188700 : Nat := 3691258380976129411889777

theorem tailTrace_7188700 : CollatzResearch.WordTrace tailWord_7188700 prefixEnd_7188700 3691258380976129411889777 := by
  unfold tailWord_7188700
  simp only [CollatzResearch.WordTrace]
  refine ⟨131096714528287553530177777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174795619371050071373570369 131096714528287553530177777)
  ·
    refine ⟨98322535896215665147633333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131096714528287553530177777 98322535896215665147633333)
    ·
      refine ⟨9217737740270218607590625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98322535896215665147633333 9217737740270218607590625)
      ·
        refine ⟨6913303305202663955692969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9217737740270218607590625 6913303305202663955692969)
        ·
          refine ⟨5184977478901997966769727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6913303305202663955692969 5184977478901997966769727)
          ·
            refine ⟨7777466218352996950154591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5184977478901997966769727 7777466218352996950154591)
            ·
              refine ⟨11666199327529495425231887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777466218352996950154591 11666199327529495425231887)
              ·
                refine ⟨17499298991294243137847831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11666199327529495425231887 17499298991294243137847831)
                ·
                  refine ⟨26248948486941364706771747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17499298991294243137847831 26248948486941364706771747)
                  ·
                    refine ⟨39373422730412047060157621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26248948486941364706771747 39373422730412047060157621)
                    ·
                      refine ⟨3691258380976129411889777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39373422730412047060157621 3691258380976129411889777)
                      ·
                        rfl

theorem cell23_7188700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7188700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188700 prefixEnd_7188700 := by exact prefixLift 7188700
  have htrace : WordTrace (prefixWord ++ tailWord_7188700) baseStart_7188700 baseEnd_7188700 := by
    simpa [prefixWord, tailWord_7188700, baseEnd_7188700] using wordTrace_append hprefix tailTrace_7188700
  have hstable : (prefixWord ++ tailWord_7188700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188700).length < 2 ^ (prefixWord ++ tailWord_7188700).sum := by decide
  have hdescent : baseEnd_7188700 < baseStart_7188700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188769 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_7188769 : Nat := 118140960795 + 7188769 * 2 ^ 59
def prefixEnd_7188769 : Nat := 4983230072969 + 3 ^ 40 * 7188769 * 2
def baseEnd_7188769 : Nat := 3691293811141289641926959

theorem tailTrace_7188769 : CollatzResearch.WordTrace tailWord_7188769 prefixEnd_7188769 3691293811141289641926959 := by
  unfold tailWord_7188769
  simp only [CollatzResearch.WordTrace]
  refine ⟨262195945693325131844617361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174797297128883421229744907 262195945693325131844617361)
  ·
    refine ⟨196646959269993848883463021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262195945693325131844617361 196646959269993848883463021)
    ·
      refine ⟨73742609726247693331298633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196646959269993848883463021 73742609726247693331298633)
      ·
        refine ⟨55306957294685769998473975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73742609726247693331298633 55306957294685769998473975)
        ·
          refine ⟨82960435942028654997710963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55306957294685769998473975 82960435942028654997710963)
          ·
            refine ⟨124440653913042982496566445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82960435942028654997710963 124440653913042982496566445)
            ·
              refine ⟨46665245217391118436212417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124440653913042982496566445 46665245217391118436212417)
              ·
                refine ⟨34998933913043338827159313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46665245217391118436212417 34998933913043338827159313)
                ·
                  refine ⟨26249200434782504120369485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34998933913043338827159313 26249200434782504120369485)
                  ·
                    refine ⟨9843450163043439045138557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26249200434782504120369485 9843450163043439045138557)
                    ·
                      refine ⟨3691293811141289641926959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9843450163043439045138557 3691293811141289641926959)
                      ·
                        rfl

theorem cell23_7188769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_7188769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188769 prefixEnd_7188769 := by exact prefixLift 7188769
  have htrace : WordTrace (prefixWord ++ tailWord_7188769) baseStart_7188769 baseEnd_7188769 := by
    simpa [prefixWord, tailWord_7188769, baseEnd_7188769] using wordTrace_append hprefix tailTrace_7188769
  have hstable : (prefixWord ++ tailWord_7188769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188769).length < 2 ^ (prefixWord ++ tailWord_7188769).sum := by decide
  have hdescent : baseEnd_7188769 < baseStart_7188769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188770 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_7188770 : Nat := 118140960795 + 7188770 * 2 ^ 59
def prefixEnd_7188770 : Nat := 4983230072969 + 3 ^ 40 * 7188770 * 2
def baseEnd_7188770 : Nat := 3691294324621944138014455

theorem tailTrace_7188770 : CollatzResearch.WordTrace tailWord_7188770 prefixEnd_7188770 3691294324621944138014455 := by
  unfold tailWord_7188770
  simp only [CollatzResearch.WordTrace]
  refine ⟨65548995541580377253850941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174797321444214339343602509 65548995541580377253850941)
  ·
    refine ⟨24580873328092641470194103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65548995541580377253850941 24580873328092641470194103)
    ·
      refine ⟨36871309992138962205291155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24580873328092641470194103 36871309992138962205291155)
      ·
        refine ⟨55306964988208443307936733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36871309992138962205291155 55306964988208443307936733)
        ·
          refine ⟨20740111870578166240476275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55306964988208443307936733 20740111870578166240476275)
          ·
            refine ⟨31110167805867249360714413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20740111870578166240476275 31110167805867249360714413)
            ·
              refine ⟨11666312927200218510267905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31110167805867249360714413 11666312927200218510267905)
              ·
                refine ⟨8749734695400163882700929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11666312927200218510267905 8749734695400163882700929)
                ·
                  refine ⟨6562301021550122912025697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8749734695400163882700929 6562301021550122912025697)
                  ·
                    refine ⟨4921725766162592184019273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562301021550122912025697 4921725766162592184019273)
                    ·
                      refine ⟨3691294324621944138014455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921725766162592184019273 3691294324621944138014455)
                      ·
                        rfl

theorem cell23_7188770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_7188770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188770 prefixEnd_7188770 := by exact prefixLift 7188770
  have htrace : WordTrace (prefixWord ++ tailWord_7188770) baseStart_7188770 baseEnd_7188770 := by
    simpa [prefixWord, tailWord_7188770, baseEnd_7188770] using wordTrace_append hprefix tailTrace_7188770
  have hstable : (prefixWord ++ tailWord_7188770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188770).length < 2 ^ (prefixWord ++ tailWord_7188770).sum := by decide
  have hdescent : baseEnd_7188770 < baseStart_7188770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188776 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 7]
def baseStart_7188776 : Nat := 118140960795 + 7188776 * 2 ^ 59
def prefixEnd_7188776 : Nat := 4983230072969 + 3 ^ 40 * 7188776 * 2
def baseEnd_7188776 : Nat := 410144156167319012726603

theorem tailTrace_7188776 : CollatzResearch.WordTrace tailWord_7188776 prefixEnd_7188776 410144156167319012726603 := by
  unfold tailWord_7188776
  simp only [CollatzResearch.WordTrace]
  refine ⟨131098100502149886020061091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174797467336199848026748121 131098100502149886020061091)
  ·
    refine ⟨196647150753224829030091637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131098100502149886020061091 196647150753224829030091637)
    ·
      refine ⟨18435670383114827721571091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196647150753224829030091637 18435670383114827721571091)
      ·
        refine ⟨27653505574672241582356637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18435670383114827721571091 27653505574672241582356637)
        ·
          refine ⟨10370064590502090593383739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27653505574672241582356637 10370064590502090593383739)
          ·
            refine ⟨15555096885753135890075609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10370064590502090593383739 15555096885753135890075609)
            ·
              refine ⟨11666322664314851917556707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15555096885753135890075609 11666322664314851917556707)
              ·
                refine ⟨17499483996472277876335061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11666322664314851917556707 17499483996472277876335061)
                ·
                  refine ⟨410144156167319012726603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17499483996472277876335061 410144156167319012726603)
                  ·
                    rfl

theorem cell23_7188776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 7].length) (baseStart_7188776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188776 prefixEnd_7188776 := by exact prefixLift 7188776
  have htrace : WordTrace (prefixWord ++ tailWord_7188776) baseStart_7188776 baseEnd_7188776 := by
    simpa [prefixWord, tailWord_7188776, baseEnd_7188776] using wordTrace_append hprefix tailTrace_7188776
  have hstable : (prefixWord ++ tailWord_7188776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188776).length < 2 ^ (prefixWord ++ tailWord_7188776).sum := by decide
  have hdescent : baseEnd_7188776 < baseStart_7188776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188809 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_7188809 : Nat := 118140960795 + 7188809 * 2 ^ 59
def prefixEnd_7188809 : Nat := 4983230072969 + 3 ^ 40 * 7188809 * 2
def baseEnd_7188809 : Nat := 3691314350367469485426775

theorem tailTrace_7188809 : CollatzResearch.WordTrace tailWord_7188809 prefixEnd_7188809 3691314350367469485426775 := by
  unfold tailWord_7188809
  simp only [CollatzResearch.WordTrace]
  refine ⟨262197404613180218676073481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174798269742120145784048987 262197404613180218676073481)
  ·
    refine ⟨196648053459885164007055111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262197404613180218676073481 196648053459885164007055111)
    ·
      refine ⟨294972080189827746010582667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196648053459885164007055111 294972080189827746010582667)
      ·
        refine ⟨442458120284741619015874001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294972080189827746010582667 442458120284741619015874001)
        ·
          refine ⟨331843590213556214261905501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442458120284741619015874001 331843590213556214261905501)
          ·
            refine ⟨124441346330083580348214563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331843590213556214261905501 124441346330083580348214563)
            ·
              refine ⟨186662019495125370522321845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124441346330083580348214563 186662019495125370522321845)
              ·
                refine ⟨17499564327668003486467673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186662019495125370522321845 17499564327668003486467673)
                ·
                  refine ⟨13124673245751002614850755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17499564327668003486467673 13124673245751002614850755)
                  ·
                    refine ⟨19687009868626503922276133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13124673245751002614850755 19687009868626503922276133)
                    ·
                      refine ⟨3691314350367469485426775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19687009868626503922276133 3691314350367469485426775)
                      ·
                        rfl

theorem cell23_7188809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_7188809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188809 prefixEnd_7188809 := by exact prefixLift 7188809
  have htrace : WordTrace (prefixWord ++ tailWord_7188809) baseStart_7188809 baseEnd_7188809 := by
    simpa [prefixWord, tailWord_7188809, baseEnd_7188809] using wordTrace_append hprefix tailTrace_7188809
  have hstable : (prefixWord ++ tailWord_7188809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188809).length < 2 ^ (prefixWord ++ tailWord_7188809).sum := by decide
  have hdescent : baseEnd_7188809 < baseStart_7188809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188926 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_7188926 : Nat := 118140960795 + 7188926 * 2 ^ 59
def prefixEnd_7188926 : Nat := 4983230072969 + 3 ^ 40 * 7188926 * 2
def baseEnd_7188926 : Nat := 1230458142534681842554579

theorem tailTrace_7188926 : CollatzResearch.WordTrace tailWord_7188926 prefixEnd_7188926 1230458142534681842554579 := by
  unfold tailWord_7188926
  simp only [CollatzResearch.WordTrace]
  refine ⟨32775208994219543457260329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174801114635837565105388421 32775208994219543457260329)
  ·
    refine ⟨24581406745664657592945247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32775208994219543457260329 24581406745664657592945247)
    ·
      refine ⟨36872110118496986389417871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24581406745664657592945247 36872110118496986389417871)
      ·
        refine ⟨55308165177745479584126807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36872110118496986389417871 55308165177745479584126807)
        ·
          refine ⟨82962247766618219376190211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55308165177745479584126807 82962247766618219376190211)
          ·
            refine ⟨124443371649927329064285317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82962247766618219376190211 124443371649927329064285317)
            ·
              refine ⟨23333132184361374199553497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124443371649927329064285317 23333132184361374199553497)
              ·
                refine ⟨17499849138271030649665123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23333132184361374199553497 17499849138271030649665123)
                ·
                  refine ⟨26249773707406545974497685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17499849138271030649665123 26249773707406545974497685)
                  ·
                    refine ⟨1230458142534681842554579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26249773707406545974497685 1230458142534681842554579)
                    ·
                      rfl

theorem cell23_7188926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_7188926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188926 prefixEnd_7188926 := by exact prefixLift 7188926
  have htrace : WordTrace (prefixWord ++ tailWord_7188926) baseStart_7188926 baseEnd_7188926 := by
    simpa [prefixWord, tailWord_7188926, baseEnd_7188926] using wordTrace_append hprefix tailTrace_7188926
  have hstable : (prefixWord ++ tailWord_7188926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188926).length < 2 ^ (prefixWord ++ tailWord_7188926).sum := by decide
  have hdescent : baseEnd_7188926 < baseStart_7188926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188970 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_7188970 : Nat := 118140960795 + 7188970 * 2 ^ 59
def prefixEnd_7188970 : Nat := 4983230072969 + 3 ^ 40 * 7188970 * 2
def baseEnd_7188970 : Nat := 3691397020752843355513535

theorem tailTrace_7188970 : CollatzResearch.WordTrace tailWord_7188970 prefixEnd_7188970 3691397020752843355513535 := by
  unfold tailWord_7188970
  simp only [CollatzResearch.WordTrace]
  refine ⟨65550819191399235793171091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174802184510397962115122909 65550819191399235793171091)
  ·
    refine ⟨98326228787098853689756637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65550819191399235793171091 98326228787098853689756637)
    ·
      refine ⟨36872335795162070133658739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98326228787098853689756637 36872335795162070133658739)
      ·
        refine ⟨55308503692743105200488109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36872335795162070133658739 55308503692743105200488109)
        ·
          refine ⟨20740688884778664450183041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55308503692743105200488109 20740688884778664450183041)
          ·
            refine ⟨15555516663583998337637281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20740688884778664450183041 15555516663583998337637281)
            ·
              refine ⟨11666637497687998753227961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15555516663583998337637281 11666637497687998753227961)
              ·
                refine ⟨8749978123265999064920971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11666637497687998753227961 8749978123265999064920971)
                ·
                  refine ⟨13124967184898998597381457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8749978123265999064920971 13124967184898998597381457)
                  ·
                    refine ⟨9843725388674248948036093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13124967184898998597381457 9843725388674248948036093)
                    ·
                      refine ⟨3691397020752843355513535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9843725388674248948036093 3691397020752843355513535)
                      ·
                        rfl

theorem cell23_7188970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_7188970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188970 prefixEnd_7188970 := by exact prefixLift 7188970
  have htrace : WordTrace (prefixWord ++ tailWord_7188970) baseStart_7188970 baseEnd_7188970 := by
    simpa [prefixWord, tailWord_7188970, baseEnd_7188970] using wordTrace_append hprefix tailTrace_7188970
  have hstable : (prefixWord ++ tailWord_7188970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188970).length < 2 ^ (prefixWord ++ tailWord_7188970).sum := by decide
  have hdescent : baseEnd_7188970 < baseStart_7188970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188973 : List Nat := [1, 5, 1, 3, 1, 1, 4, 7]
def baseStart_7188973 : Nat := 118140960795 + 7188973 * 2 ^ 59
def prefixEnd_7188973 : Nat := 4983230072969 + 3 ^ 40 * 7188973 * 2
def baseEnd_7188973 : Nat := 136718465229437290510223

theorem tailTrace_7188973 : CollatzResearch.WordTrace tailWord_7188973 prefixEnd_7188973 136718465229437290510223 := by
  unfold tailWord_7188973
  simp only [CollatzResearch.WordTrace]
  refine ⟨262203386184586074685043573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174802257456390716456695715 262203386184586074685043573)
  ·
    refine ⟨24581567454804944501722835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262203386184586074685043573 24581567454804944501722835)
    ·
      refine ⟨36872351182207416752584253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24581567454804944501722835 36872351182207416752584253)
      ·
        refine ⟨13827131693327781282219095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36872351182207416752584253 13827131693327781282219095)
        ·
          refine ⟨20740697539991671923328643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13827131693327781282219095 20740697539991671923328643)
          ·
            refine ⟨31111046309987507884992965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20740697539991671923328643 31111046309987507884992965)
            ·
              refine ⟨5833321183122657728436181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31111046309987507884992965 5833321183122657728436181)
              ·
                refine ⟨136718465229437290510223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5833321183122657728436181 136718465229437290510223)
                ·
                  rfl

theorem cell23_7188973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 7].length) (baseStart_7188973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188973 prefixEnd_7188973 := by exact prefixLift 7188973
  have htrace : WordTrace (prefixWord ++ tailWord_7188973) baseStart_7188973 baseEnd_7188973 := by
    simpa [prefixWord, tailWord_7188973, baseEnd_7188973] using wordTrace_append hprefix tailTrace_7188973
  have hstable : (prefixWord ++ tailWord_7188973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188973).length < 2 ^ (prefixWord ++ tailWord_7188973).sum := by decide
  have hdescent : baseEnd_7188973 < baseStart_7188973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7188979 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 5]
def baseStart_7188979 : Nat := 118140960795 + 7188979 * 2 ^ 59
def prefixEnd_7188979 : Nat := 4983230072969 + 3 ^ 40 * 7188979 * 2
def baseEnd_7188979 : Nat := 3691401642078733820300993

theorem tailTrace_7188979 : CollatzResearch.WordTrace tailWord_7188979 prefixEnd_7188979 3691401642078733820300993 := by
  unfold tailWord_7188979
  simp only [CollatzResearch.WordTrace]
  refine ⟨262203605022564337709761991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174802403348376225139841327 262203605022564337709761991)
  ·
    refine ⟨393305407533846506564642987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262203605022564337709761991 393305407533846506564642987)
    ·
      refine ⟨589958111300769759846964481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393305407533846506564642987 589958111300769759846964481)
      ·
        refine ⟨442468583475577319885223361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589958111300769759846964481 442468583475577319885223361)
        ·
          refine ⟨331851437606682989913917521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442468583475577319885223361 331851437606682989913917521)
          ·
            refine ⟨248888578205012242435438141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331851437606682989913917521 248888578205012242435438141)
            ·
              refine ⟨93333216826879590913289303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248888578205012242435438141 93333216826879590913289303)
              ·
                refine ⟨139999825240319386369933955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93333216826879590913289303 139999825240319386369933955)
                ·
                  refine ⟨209999737860479079554900933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139999825240319386369933955 209999737860479079554900933)
                  ·
                    refine ⟨39374950848839827416543925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209999737860479079554900933 39374950848839827416543925)
                    ·
                      refine ⟨3691401642078733820300993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39374950848839827416543925 3691401642078733820300993)
                      ·
                        rfl

theorem cell23_7188979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_7188979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7188979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7188979 prefixEnd_7188979 := by exact prefixLift 7188979
  have htrace : WordTrace (prefixWord ++ tailWord_7188979) baseStart_7188979 baseEnd_7188979 := by
    simpa [prefixWord, tailWord_7188979, baseEnd_7188979] using wordTrace_append hprefix tailTrace_7188979
  have hstable : (prefixWord ++ tailWord_7188979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7188979).length < 2 ^ (prefixWord ++ tailWord_7188979).sum := by decide
  have hdescent : baseEnd_7188979 < baseStart_7188979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7188979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189019 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6]
def baseStart_7189019 : Nat := 118140960795 + 7189019 * 2 ^ 59
def prefixEnd_7189019 : Nat := 4983230072969 + 3 ^ 40 * 7189019 * 2
def baseEnd_7189019 : Nat := 3691422181304913663800809

theorem tailTrace_7189019 : CollatzResearch.WordTrace tailWord_7189019 prefixEnd_7189019 3691422181304913663800809 := by
  unfold tailWord_7189019
  simp only [CollatzResearch.WordTrace]
  refine ⟨262205063942419424541218111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174803375961612949694145407 262205063942419424541218111)
  ·
    refine ⟨393307595913629136811827167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262205063942419424541218111 393307595913629136811827167)
    ·
      refine ⟨589961393870443705217740751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393307595913629136811827167 589961393870443705217740751)
      ·
        refine ⟨884942090805665557826611127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589961393870443705217740751 884942090805665557826611127)
        ·
          refine ⟨1327413136208498336739916691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884942090805665557826611127 1327413136208498336739916691)
          ·
            refine ⟨1991119704312747505109875037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327413136208498336739916691 1991119704312747505109875037)
            ·
              refine ⟨746669889117280314416203139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1991119704312747505109875037 746669889117280314416203139)
              ·
                refine ⟨1120004833675920471624304709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746669889117280314416203139 1120004833675920471624304709)
                ·
                  refine ⟨210000906314235088429557133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1120004833675920471624304709 210000906314235088429557133)
                  ·
                    refine ⟨78750339867838158161083925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210000906314235088429557133 78750339867838158161083925)
                    ·
                      refine ⟨3691422181304913663800809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78750339867838158161083925 3691422181304913663800809)
                      ·
                        rfl

theorem cell23_7189019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_7189019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189019 prefixEnd_7189019 := by exact prefixLift 7189019
  have htrace : WordTrace (prefixWord ++ tailWord_7189019) baseStart_7189019 baseEnd_7189019 := by
    simpa [prefixWord, tailWord_7189019, baseEnd_7189019] using wordTrace_append hprefix tailTrace_7189019
  have hstable : (prefixWord ++ tailWord_7189019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189019).length < 2 ^ (prefixWord ++ tailWord_7189019).sum := by decide
  have hdescent : baseEnd_7189019 < baseStart_7189019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189023 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 1, 4, 2]
def baseStart_7189023 : Nat := 118140960795 + 7189023 * 2 ^ 59
def prefixEnd_7189023 : Nat := 4983230072969 + 3 ^ 40 * 7189023 * 2
def baseEnd_7189023 : Nat := 3691424235227531648150791

theorem tailTrace_7189023 : CollatzResearch.WordTrace tailWord_7189023 prefixEnd_7189023 3691424235227531648150791 := by
  unfold tailWord_7189023
  simp only [CollatzResearch.WordTrace]
  refine ⟨262205209834404933224363723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174803473222936622149575815 262205209834404933224363723)
  ·
    refine ⟨393307814751607399836545585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262205209834404933224363723 393307814751607399836545585)
    ·
      refine ⟨294980861063705549877409189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393307814751607399836545585 294980861063705549877409189)
      ·
        refine ⟨55308911449444790602014223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294980861063705549877409189 55308911449444790602014223)
        ·
          refine ⟨82963367174167185903021335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55308911449444790602014223 82963367174167185903021335)
          ·
            refine ⟨124445050761250778854532003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82963367174167185903021335 124445050761250778854532003)
            ·
              refine ⟨186667576141876168281798005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124445050761250778854532003 186667576141876168281798005)
              ·
                refine ⟨17500085263300890776418563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186667576141876168281798005 17500085263300890776418563)
                ·
                  refine ⟨26250127894951336164627845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17500085263300890776418563 26250127894951336164627845)
                  ·
                    refine ⟨4921898980303375530867721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26250127894951336164627845 4921898980303375530867721)
                    ·
                      refine ⟨3691424235227531648150791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921898980303375530867721 3691424235227531648150791)
                      ·
                        rfl

theorem cell23_7189023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_7189023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189023 prefixEnd_7189023 := by exact prefixLift 7189023
  have htrace : WordTrace (prefixWord ++ tailWord_7189023) baseStart_7189023 baseEnd_7189023 := by
    simpa [prefixWord, tailWord_7189023, baseEnd_7189023] using wordTrace_append hprefix tailTrace_7189023
  have hstable : (prefixWord ++ tailWord_7189023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189023).length < 2 ^ (prefixWord ++ tailWord_7189023).sum := by decide
  have hdescent : baseEnd_7189023 < baseStart_7189023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189027 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 1, 3, 2]
def baseStart_7189027 : Nat := 118140960795 + 7189027 * 2 ^ 59
def prefixEnd_7189027 : Nat := 4983230072969 + 3 ^ 40 * 7189027 * 2
def baseEnd_7189027 : Nat := 3691426289150149632500773

theorem tailTrace_7189027 : CollatzResearch.WordTrace tailWord_7189027 prefixEnd_7189027 3691426289150149632500773 := by
  unfold tailWord_7189027
  simp only [CollatzResearch.WordTrace]
  refine ⟨262205355726390441907509335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174803570484260294605006223 262205355726390441907509335)
  ·
    refine ⟨393308033589585662861264003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262205355726390441907509335 393308033589585662861264003)
    ·
      refine ⟨589962050384378494291896005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393308033589585662861264003 589962050384378494291896005)
      ·
        refine ⟨110617884447070967679730501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 589962050384378494291896005 110617884447070967679730501)
        ·
          refine ⟨20740853333825806439949469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110617884447070967679730501 20740853333825806439949469)
          ·
            refine ⟨7777820000184677414981051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20740853333825806439949469 7777820000184677414981051)
            ·
              refine ⟨11666730000277016122471577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777820000184677414981051 11666730000277016122471577)
              ·
                refine ⟨8750047500207762091853683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11666730000277016122471577 8750047500207762091853683)
                ·
                  refine ⟨13125071250311643137780525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8750047500207762091853683 13125071250311643137780525)
                  ·
                    refine ⟨4921901718866866176667697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13125071250311643137780525 4921901718866866176667697)
                    ·
                      refine ⟨3691426289150149632500773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921901718866866176667697 3691426289150149632500773)
                      ·
                        rfl

theorem cell23_7189027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_7189027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189027 prefixEnd_7189027 := by exact prefixLift 7189027
  have htrace : WordTrace (prefixWord ++ tailWord_7189027) baseStart_7189027 baseEnd_7189027 := by
    simpa [prefixWord, tailWord_7189027, baseEnd_7189027] using wordTrace_append hprefix tailTrace_7189027
  have hstable : (prefixWord ++ tailWord_7189027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189027).length < 2 ^ (prefixWord ++ tailWord_7189027).sum := by decide
  have hdescent : baseEnd_7189027 < baseStart_7189027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189057 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_7189057 : Nat := 118140960795 + 7189057 * 2 ^ 59
def prefixEnd_7189057 : Nat := 4983230072969 + 3 ^ 40 * 7189057 * 2
def baseEnd_7189057 : Nat := 3691441693569784515125635

theorem tailTrace_7189057 : CollatzResearch.WordTrace tailWord_7189057 prefixEnd_7189057 3691441693569784515125635 := by
  unfold tailWord_7189057
  simp only [CollatzResearch.WordTrace]
  refine ⟨262206449916281757031101425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174804299944187838020734283 262206449916281757031101425)
  ·
    refine ⟨196654837437211317773326069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262206449916281757031101425 196654837437211317773326069)
    ·
      refine ⟨18436391009738561041249319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196654837437211317773326069 18436391009738561041249319)
      ·
        refine ⟨27654586514607841561873979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18436391009738561041249319 27654586514607841561873979)
        ·
          refine ⟨41481879771911762342810969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27654586514607841561873979 41481879771911762342810969)
          ·
            refine ⟨31111409828933821757108227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41481879771911762342810969 31111409828933821757108227)
            ·
              refine ⟨46667114743400732635662341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31111409828933821757108227 46667114743400732635662341)
              ·
                refine ⟨8750084014387637369186689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46667114743400732635662341 8750084014387637369186689)
                ·
                  refine ⟨6562563010790728026890017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8750084014387637369186689 6562563010790728026890017)
                  ·
                    refine ⟨4921922258093046020167513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562563010790728026890017 4921922258093046020167513)
                    ·
                      refine ⟨3691441693569784515125635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4921922258093046020167513 3691441693569784515125635)
                      ·
                        rfl

theorem cell23_7189057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_7189057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189057 prefixEnd_7189057 := by exact prefixLift 7189057
  have htrace : WordTrace (prefixWord ++ tailWord_7189057) baseStart_7189057 baseEnd_7189057 := by
    simpa [prefixWord, tailWord_7189057, baseEnd_7189057] using wordTrace_append hprefix tailTrace_7189057
  have hstable : (prefixWord ++ tailWord_7189057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189057).length < 2 ^ (prefixWord ++ tailWord_7189057).sum := by decide
  have hdescent : baseEnd_7189057 < baseStart_7189057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189073 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_7189073 : Nat := 118140960795 + 7189073 * 2 ^ 59
def prefixEnd_7189073 : Nat := 4983230072969 + 3 ^ 40 * 7189073 * 2
def baseEnd_7189073 : Nat := 3691449909260256452525561

theorem tailTrace_7189073 : CollatzResearch.WordTrace tailWord_7189073 prefixEnd_7189073 3691449909260256452525561 := by
  unfold tailWord_7189073
  simp only [CollatzResearch.WordTrace]
  refine ⟨262207033484223791763683873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174804688989482527842455915 262207033484223791763683873)
  ·
    refine ⟨196655275113167843822762905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262207033484223791763683873 196655275113167843822762905)
    ·
      refine ⟨147491456334875882867072179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196655275113167843822762905 147491456334875882867072179)
      ·
        refine ⟨221237184502313824300608269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147491456334875882867072179 221237184502313824300608269)
        ·
          refine ⟨82963944188367684112728101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221237184502313824300608269 82963944188367684112728101)
          ·
            refine ⟨15555739535318940771136519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82963944188367684112728101 15555739535318940771136519)
            ·
              refine ⟨23333609302978411156704779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15555739535318940771136519 23333609302978411156704779)
              ·
                refine ⟨35000413954467616735057169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23333609302978411156704779 35000413954467616735057169)
                ·
                  refine ⟨26250310465850712551292877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35000413954467616735057169 26250310465850712551292877)
                  ·
                    refine ⟨9843866424694017206734829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26250310465850712551292877 9843866424694017206734829)
                    ·
                      refine ⟨3691449909260256452525561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9843866424694017206734829 3691449909260256452525561)
                      ·
                        rfl

theorem cell23_7189073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_7189073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189073 prefixEnd_7189073 := by exact prefixLift 7189073
  have htrace : WordTrace (prefixWord ++ tailWord_7189073) baseStart_7189073 baseEnd_7189073 := by
    simpa [prefixWord, tailWord_7189073, baseEnd_7189073] using wordTrace_append hprefix tailTrace_7189073
  have hstable : (prefixWord ++ tailWord_7189073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189073).length < 2 ^ (prefixWord ++ tailWord_7189073).sum := by decide
  have hdescent : baseEnd_7189073 < baseStart_7189073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189093 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_7189093 : Nat := 118140960795 + 7189093 * 2 ^ 59
def prefixEnd_7189093 : Nat := 4983230072969 + 3 ^ 40 * 7189093 * 2
def baseEnd_7189093 : Nat := 1230486726291115458091823

theorem tailTrace_7189093 : CollatzResearch.WordTrace tailWord_7189093 prefixEnd_7189093 1230486726291115458091823 := by
  unfold tailWord_7189093
  simp only [CollatzResearch.WordTrace]
  refine ⟨262207762944151335179411933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174805175296100890119607955 262207762944151335179411933)
  ·
    refine ⟨98327911104056750692279475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262207762944151335179411933 98327911104056750692279475)
    ·
      refine ⟨147491866656085126038419213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98327911104056750692279475 147491866656085126038419213)
      ·
        refine ⟨55309449996031922264407205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147491866656085126038419213 55309449996031922264407205)
        ·
          refine ⟨10370521874255985424576351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55309449996031922264407205 10370521874255985424576351)
          ·
            refine ⟨15555782811383978136864527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10370521874255985424576351 15555782811383978136864527)
            ·
              refine ⟨23333674217075967205296791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15555782811383978136864527 23333674217075967205296791)
              ·
                refine ⟨35000511325613950807945187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23333674217075967205296791 35000511325613950807945187)
                ·
                  refine ⟨52500766988420926211917781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35000511325613950807945187 52500766988420926211917781)
                  ·
                    refine ⟨1230486726291115458091823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52500766988420926211917781 1230486726291115458091823)
                    ·
                      rfl

theorem cell23_7189093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_7189093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189093 prefixEnd_7189093 := by exact prefixLift 7189093
  have htrace : WordTrace (prefixWord ++ tailWord_7189093) baseStart_7189093 baseEnd_7189093 := by
    simpa [prefixWord, tailWord_7189093, baseEnd_7189093] using wordTrace_append hprefix tailTrace_7189093
  have hstable : (prefixWord ++ tailWord_7189093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189093).length < 2 ^ (prefixWord ++ tailWord_7189093).sum := by decide
  have hdescent : baseEnd_7189093 < baseStart_7189093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189116 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_7189116 : Nat := 118140960795 + 7189116 * 2 ^ 59
def prefixEnd_7189116 : Nat := 4983230072969 + 3 ^ 40 * 7189116 * 2
def baseEnd_7189116 : Nat := 3691471988928399784287863

theorem tailTrace_7189116 : CollatzResearch.WordTrace tailWord_7189116 prefixEnd_7189116 3691471988928399784287863 := by
  unfold tailWord_7189116
  simp only [CollatzResearch.WordTrace]
  refine ⟨131104300911534005053749601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174805734548712006738332801 131104300911534005053749601)
  ·
    refine ⟨98328225683650503790312201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131104300911534005053749601 98328225683650503790312201)
    ·
      refine ⟨73746169262737877842734151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98328225683650503790312201 73746169262737877842734151)
      ·
        refine ⟨110619253894106816764101227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73746169262737877842734151 110619253894106816764101227)
        ·
          refine ⟨165928880841160225146151841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110619253894106816764101227 165928880841160225146151841)
          ·
            refine ⟨124446660630870168859613881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165928880841160225146151841 124446660630870168859613881)
            ·
              refine ⟨93334995473152626644710411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124446660630870168859613881 93334995473152626644710411)
              ·
                refine ⟨140002493209728939967065617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93334995473152626644710411 140002493209728939967065617)
                ·
                  refine ⟨105001869907296704975299213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140002493209728939967065617 105001869907296704975299213)
                  ·
                    refine ⟨39375701215236264365737205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105001869907296704975299213 39375701215236264365737205)
                    ·
                      refine ⟨3691471988928399784287863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39375701215236264365737205 3691471988928399784287863)
                      ·
                        rfl

theorem cell23_7189116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_7189116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189116 prefixEnd_7189116 := by exact prefixLift 7189116
  have htrace : WordTrace (prefixWord ++ tailWord_7189116) baseStart_7189116 baseEnd_7189116 := by
    simpa [prefixWord, tailWord_7189116, baseEnd_7189116] using wordTrace_append hprefix tailTrace_7189116
  have hstable : (prefixWord ++ tailWord_7189116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189116).length < 2 ^ (prefixWord ++ tailWord_7189116).sum := by decide
  have hdescent : baseEnd_7189116 < baseStart_7189116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189123 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 3, 4]
def baseStart_7189123 : Nat := 118140960795 + 7189123 * 2 ^ 59
def prefixEnd_7189123 : Nat := 4983230072969 + 3 ^ 40 * 7189123 * 2
def baseEnd_7189123 : Nat := 1230491861097660418966777

theorem tailTrace_7189123 : CollatzResearch.WordTrace tailWord_7189123 prefixEnd_7189123 1230491861097660418966777 := by
  unfold tailWord_7189123
  simp only [CollatzResearch.WordTrace]
  refine ⟨262208857134042650303004023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174805904756028433535336015 262208857134042650303004023)
  ·
    refine ⟨393313285701063975454506035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262208857134042650303004023 393313285701063975454506035)
    ·
      refine ⟨589969928551595963181759053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393313285701063975454506035 589969928551595963181759053)
      ·
        refine ⟨221238723206848486193159645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589969928551595963181759053 221238723206848486193159645)
        ·
          refine ⟨82964521202568182322434867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221238723206848486193159645 82964521202568182322434867)
          ·
            refine ⟨124446781803852273483652301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82964521202568182322434867 124446781803852273483652301)
            ·
              refine ⟨46667543176444602556369613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124446781803852273483652301 46667543176444602556369613)
              ·
                refine ⟨17500328691166725958638605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46667543176444602556369613 17500328691166725958638605)
                ·
                  refine ⟨6562623259187522234489477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17500328691166725958638605 6562623259187522234489477)
                  ·
                    refine ⟨1230491861097660418966777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6562623259187522234489477 1230491861097660418966777)
                    ·
                      rfl

theorem cell23_7189123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 4].length) (baseStart_7189123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189123 prefixEnd_7189123 := by exact prefixLift 7189123
  have htrace : WordTrace (prefixWord ++ tailWord_7189123) baseStart_7189123 baseEnd_7189123 := by
    simpa [prefixWord, tailWord_7189123, baseEnd_7189123] using wordTrace_append hprefix tailTrace_7189123
  have hstable : (prefixWord ++ tailWord_7189123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189123).length < 2 ^ (prefixWord ++ tailWord_7189123).sum := by decide
  have hdescent : baseEnd_7189123 < baseStart_7189123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189150 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_7189150 : Nat := 118140960795 + 7189150 * 2 ^ 59
def prefixEnd_7189150 : Nat := 4983230072969 + 3 ^ 40 * 7189150 * 2
def baseEnd_7189150 : Nat := 3691489447270652651262707

theorem tailTrace_7189150 : CollatzResearch.WordTrace tailWord_7189150 prefixEnd_7189150 3691489447270652651262707 := by
  unfold tailWord_7189150
  simp only [CollatzResearch.WordTrace]
  refine ⟨32776230238118104239279613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174806561269963222609491269 32776230238118104239279613)
  ·
    refine ⟨12291086339294289089729855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32776230238118104239279613 12291086339294289089729855)
    ·
      refine ⟨18436629508941433634594783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12291086339294289089729855 18436629508941433634594783)
      ·
        refine ⟨27654944263412150451892175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18436629508941433634594783 27654944263412150451892175)
        ·
          refine ⟨41482416395118225677838263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27654944263412150451892175 41482416395118225677838263)
          ·
            refine ⟨62223624592677338516757395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41482416395118225677838263 62223624592677338516757395)
            ·
              refine ⟨93335436889016007775136093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62223624592677338516757395 93335436889016007775136093)
              ·
                refine ⟨35000788833381002915676035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93335436889016007775136093 35000788833381002915676035)
                ·
                  refine ⟨52501183250071504373514053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35000788833381002915676035 52501183250071504373514053)
                  ·
                    refine ⟨9843971859388407070033885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52501183250071504373514053 9843971859388407070033885)
                    ·
                      refine ⟨3691489447270652651262707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9843971859388407070033885 3691489447270652651262707)
                      ·
                        rfl

theorem cell23_7189150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_7189150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189150 prefixEnd_7189150 := by exact prefixLift 7189150
  have htrace : WordTrace (prefixWord ++ tailWord_7189150) baseStart_7189150 baseEnd_7189150 := by
    simpa [prefixWord, tailWord_7189150, baseEnd_7189150] using wordTrace_append hprefix tailTrace_7189150
  have hstable : (prefixWord ++ tailWord_7189150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189150).length < 2 ^ (prefixWord ++ tailWord_7189150).sum := by decide
  have hdescent : baseEnd_7189150 < baseStart_7189150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189176 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_7189176 : Nat := 118140960795 + 7189176 * 2 ^ 59
def prefixEnd_7189176 : Nat := 4983230072969 + 3 ^ 40 * 7189176 * 2
def baseEnd_7189176 : Nat := 3691502797767669549537587

theorem tailTrace_7189176 : CollatzResearch.WordTrace tailWord_7189176 prefixEnd_7189176 3691502797767669549537587 := by
  unfold tailWord_7189176
  simp only [CollatzResearch.WordTrace]
  refine ⟨131105395101425320177341691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174807193468567093569788921 131105395101425320177341691)
  ·
    refine ⟨196658092652137980266012537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131105395101425320177341691 196658092652137980266012537)
    ·
      refine ⟨147493569489103485199509403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196658092652137980266012537 147493569489103485199509403)
      ·
        refine ⟨221240354233655227799264105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147493569489103485199509403 221240354233655227799264105)
        ·
          refine ⟨165930265675241420849448079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221240354233655227799264105 165930265675241420849448079)
          ·
            refine ⟨248895398512862131274172119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165930265675241420849448079 248895398512862131274172119)
            ·
              refine ⟨373343097769293196911258179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248895398512862131274172119 373343097769293196911258179)
              ·
                refine ⟨560014646653939795366887269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373343097769293196911258179 560014646653939795366887269)
                ·
                  refine ⟨105002746247613711631291363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560014646653939795366887269 105002746247613711631291363)
                  ·
                    refine ⟨157504119371420567446937045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105002746247613711631291363 157504119371420567446937045)
                    ·
                      refine ⟨3691502797767669549537587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157504119371420567446937045 3691502797767669549537587)
                      ·
                        rfl

theorem cell23_7189176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_7189176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189176 prefixEnd_7189176 := by exact prefixLift 7189176
  have htrace : WordTrace (prefixWord ++ tailWord_7189176) baseStart_7189176 baseEnd_7189176 := by
    simpa [prefixWord, tailWord_7189176, baseEnd_7189176] using wordTrace_append hprefix tailTrace_7189176
  have hstable : (prefixWord ++ tailWord_7189176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189176).length < 2 ^ (prefixWord ++ tailWord_7189176).sum := by decide
  have hdescent : baseEnd_7189176 < baseStart_7189176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189207 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 2, 3, 2]
def baseStart_7189207 : Nat := 118140960795 + 7189207 * 2 ^ 59
def prefixEnd_7189207 : Nat := 4983230072969 + 3 ^ 40 * 7189207 * 2
def baseEnd_7189207 : Nat := 3691518715667958928249945

theorem tailTrace_7189207 : CollatzResearch.WordTrace tailWord_7189207 prefixEnd_7189207 3691518715667958928249945 := by
  unfold tailWord_7189207
  simp only [CollatzResearch.WordTrace]
  refine ⟨262211920865738332649061875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174807947243825555099374583 262211920865738332649061875)
  ·
    refine ⟨393317881298607498973592813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262211920865738332649061875 393317881298607498973592813)
    ·
      refine ⟨147494205486977812115097305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393317881298607498973592813 147494205486977812115097305)
      ·
        refine ⟨110620654115233359086322979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147494205486977812115097305 110620654115233359086322979)
        ·
          refine ⟨165930981172850038629484469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110620654115233359086322979 165930981172850038629484469)
          ·
            refine ⟨15556029484954691121514169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165930981172850038629484469 15556029484954691121514169)
            ·
              refine ⟨11667022113716018341135627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15556029484954691121514169 11667022113716018341135627)
              ·
                refine ⟨17500533170574027511703441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11667022113716018341135627 17500533170574027511703441)
                ·
                  refine ⟨13125399877930520633777581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17500533170574027511703441 13125399877930520633777581)
                  ·
                    refine ⟨4922024954223945237666593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13125399877930520633777581 4922024954223945237666593)
                    ·
                      refine ⟨3691518715667958928249945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922024954223945237666593 3691518715667958928249945)
                      ·
                        rfl

theorem cell23_7189207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_7189207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189207 prefixEnd_7189207 := by exact prefixLift 7189207
  have htrace : WordTrace (prefixWord ++ tailWord_7189207) baseStart_7189207 baseEnd_7189207 := by
    simpa [prefixWord, tailWord_7189207, baseEnd_7189207] using wordTrace_append hprefix tailTrace_7189207
  have hstable : (prefixWord ++ tailWord_7189207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189207).length < 2 ^ (prefixWord ++ tailWord_7189207).sum := by decide
  have hdescent : baseEnd_7189207 < baseStart_7189207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189217 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 1, 5]
def baseStart_7189217 : Nat := 118140960795 + 7189217 * 2 ^ 59
def prefixEnd_7189217 : Nat := 4983230072969 + 3 ^ 40 * 7189217 * 2
def baseEnd_7189217 : Nat := 1230507950158167963041633

theorem tailTrace_7189217 : CollatzResearch.WordTrace tailWord_7189217 prefixEnd_7189217 1230507950158167963041633 := by
  unfold tailWord_7189217
  simp only [CollatzResearch.WordTrace]
  refine ⟨262212285595702104356925905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174808190397134736237950603 262212285595702104356925905)
  ·
    refine ⟨196659214196776578267694429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262212285595702104356925905 196659214196776578267694429)
    ·
      refine ⟨73747205323791216850385411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196659214196776578267694429 73747205323791216850385411)
      ·
        refine ⟨110620807985686825275578117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73747205323791216850385411 110620807985686825275578117)
        ·
          refine ⟨20741401497316279739170897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110620807985686825275578117 20741401497316279739170897)
          ·
            refine ⟨15556051122987209804378173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20741401497316279739170897 15556051122987209804378173)
            ·
              refine ⟨5833519171120203676641815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15556051122987209804378173 5833519171120203676641815)
              ·
                refine ⟨8750278756680305514962723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833519171120203676641815 8750278756680305514962723)
                ·
                  refine ⟨13125418135020458272444085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8750278756680305514962723 13125418135020458272444085)
                  ·
                    refine ⟨1230507950158167963041633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13125418135020458272444085 1230507950158167963041633)
                    ·
                      rfl

theorem cell23_7189217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_7189217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189217 prefixEnd_7189217 := by exact prefixLift 7189217
  have htrace : WordTrace (prefixWord ++ tailWord_7189217) baseStart_7189217 baseEnd_7189217 := by
    simpa [prefixWord, tailWord_7189217, baseEnd_7189217] using wordTrace_append hprefix tailTrace_7189217
  have hstable : (prefixWord ++ tailWord_7189217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189217).length < 2 ^ (prefixWord ++ tailWord_7189217).sum := by decide
  have hdescent : baseEnd_7189217 < baseStart_7189217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189231 : List Nat := [1, 1, 2, 1, 5, 4, 2, 2, 1, 1, 3]
def baseStart_7189231 : Nat := 118140960795 + 7189231 * 2 ^ 59
def prefixEnd_7189231 : Nat := 4983230072969 + 3 ^ 40 * 7189231 * 2
def baseEnd_7189231 : Nat := 3691531039203666834349835

theorem tailTrace_7189231 : CollatzResearch.WordTrace tailWord_7189231 prefixEnd_7189231 3691531039203666834349835 := by
  unfold tailWord_7189231
  simp only [CollatzResearch.WordTrace]
  refine ⟨262212796217651384747935547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174808530811767589831957031 262212796217651384747935547)
  ·
    refine ⟨393319194326477077121903321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262212796217651384747935547 393319194326477077121903321)
    ·
      refine ⟨294989395744857807841427491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393319194326477077121903321 294989395744857807841427491)
      ·
        refine ⟨442484093617286711762141237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294989395744857807841427491 442484093617286711762141237)
        ·
          refine ⟨41482883776620629227700741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 442484093617286711762141237 41482883776620629227700741)
          ·
            refine ⟨7778040708116367980193889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41482883776620629227700741 7778040708116367980193889)
            ·
              refine ⟨5833530531087275985145417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7778040708116367980193889 5833530531087275985145417)
              ·
                refine ⟨4375147898315456988859063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5833530531087275985145417 4375147898315456988859063)
                ·
                  refine ⟨6562721847473185483288595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375147898315456988859063 6562721847473185483288595)
                  ·
                    refine ⟨9844082771209778224932893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6562721847473185483288595 9844082771209778224932893)
                    ·
                      refine ⟨3691531039203666834349835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9844082771209778224932893 3691531039203666834349835)
                      ·
                        rfl

theorem cell23_7189231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 1, 3].length) (baseStart_7189231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189231 prefixEnd_7189231 := by exact prefixLift 7189231
  have htrace : WordTrace (prefixWord ++ tailWord_7189231) baseStart_7189231 baseEnd_7189231 := by
    simpa [prefixWord, tailWord_7189231, baseEnd_7189231] using wordTrace_append hprefix tailTrace_7189231
  have hstable : (prefixWord ++ tailWord_7189231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189231).length < 2 ^ (prefixWord ++ tailWord_7189231).sum := by decide
  have hdescent : baseEnd_7189231 < baseStart_7189231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189233 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_7189233 : Nat := 118140960795 + 7189233 * 2 ^ 59
def prefixEnd_7189233 : Nat := 4983230072969 + 3 ^ 40 * 7189233 * 2
def baseEnd_7189233 : Nat := 3691532066164975826524825

theorem tailTrace_7189233 : CollatzResearch.WordTrace tailWord_7189233 prefixEnd_7189233 3691532066164975826524825 := by
  unfold tailWord_7189233
  simp only [CollatzResearch.WordTrace]
  refine ⟨262212869163644139089508353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174808579442429426059672235 262212869163644139089508353)
  ·
    refine ⟨196659651872733104317131265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262212869163644139089508353 196659651872733104317131265)
    ·
      refine ⟨147494738904549828237848449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196659651872733104317131265 147494738904549828237848449)
      ·
        refine ⟨110621054178412371178386337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147494738904549828237848449 110621054178412371178386337)
        ·
          refine ⟨82965790633809278383789753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110621054178412371178386337 82965790633809278383789753)
          ·
            refine ⟨62224342975356958787842315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82965790633809278383789753 62224342975356958787842315)
            ·
              refine ⟨93336514463035438181763473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62224342975356958787842315 93336514463035438181763473)
              ·
                refine ⟨70002385847276578636322605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93336514463035438181763473 70002385847276578636322605)
                ·
                  refine ⟨26250894692728716988620977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70002385847276578636322605 26250894692728716988620977)
                  ·
                    refine ⟨19688171019546537741465733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26250894692728716988620977 19688171019546537741465733)
                    ·
                      refine ⟨3691532066164975826524825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19688171019546537741465733 3691532066164975826524825)
                      ·
                        rfl

theorem cell23_7189233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_7189233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189233 prefixEnd_7189233 := by exact prefixLift 7189233
  have htrace : WordTrace (prefixWord ++ tailWord_7189233) baseStart_7189233 baseEnd_7189233 := by
    simpa [prefixWord, tailWord_7189233, baseEnd_7189233] using wordTrace_append hprefix tailTrace_7189233
  have hstable : (prefixWord ++ tailWord_7189233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189233).length < 2 ^ (prefixWord ++ tailWord_7189233).sum := by decide
  have hdescent : baseEnd_7189233 < baseStart_7189233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189271 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 1, 1, 4]
def baseStart_7189271 : Nat := 118140960795 + 7189271 * 2 ^ 59
def prefixEnd_7189271 : Nat := 4983230072969 + 3 ^ 40 * 7189271 * 2
def baseEnd_7189271 : Nat := 3691551578429846677849651

theorem tailTrace_7189271 : CollatzResearch.WordTrace tailWord_7189271 prefixEnd_7189271 3691551578429846677849651 := by
  unfold tailWord_7189271
  simp only [CollatzResearch.WordTrace]
  refine ⟨262214255137506471579391667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174809503425004314386261111 262214255137506471579391667)
  ·
    refine ⟨393321382706259707369087501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262214255137506471579391667 393321382706259707369087501)
    ·
      refine ⟨147495518514847390263407813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393321382706259707369087501 147495518514847390263407813)
      ·
        refine ⟨27655409721533885674388965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147495518514847390263407813 27655409721533885674388965)
        ·
          refine ⟨5185389322787603563947931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27655409721533885674388965 5185389322787603563947931)
          ·
            refine ⟨7778083984181405345921897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185389322787603563947931 7778083984181405345921897)
            ·
              refine ⟨5833562988136054009441423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7778083984181405345921897 5833562988136054009441423)
              ·
                refine ⟨8750344482204081014162135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833562988136054009441423 8750344482204081014162135)
                ·
                  refine ⟨13125516723306121521243203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8750344482204081014162135 13125516723306121521243203)
                  ·
                    refine ⟨19688275084959182281864805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13125516723306121521243203 19688275084959182281864805)
                    ·
                      refine ⟨3691551578429846677849651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19688275084959182281864805 3691551578429846677849651)
                      ·
                        rfl

theorem cell23_7189271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_7189271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189271 prefixEnd_7189271 := by exact prefixLift 7189271
  have htrace : WordTrace (prefixWord ++ tailWord_7189271) baseStart_7189271 baseEnd_7189271 := by
    simpa [prefixWord, tailWord_7189271, baseEnd_7189271] using wordTrace_append hprefix tailTrace_7189271
  have hstable : (prefixWord ++ tailWord_7189271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189271).length < 2 ^ (prefixWord ++ tailWord_7189271).sum := by decide
  have hdescent : baseEnd_7189271 < baseStart_7189271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189303 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 2, 6]
def baseStart_7189303 : Nat := 118140960795 + 7189303 * 2 ^ 59
def prefixEnd_7189303 : Nat := 4983230072969 + 3 ^ 40 * 7189303 * 2
def baseEnd_7189303 : Nat := 1230522669936930184216501

theorem tailTrace_7189303 : CollatzResearch.WordTrace tailWord_7189303 prefixEnd_7189303 1230522669936930184216501 := by
  unfold tailWord_7189303
  simp only [CollatzResearch.WordTrace]
  refine ⟨262215422273390541044556563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174810281515593694029704375 262215422273390541044556563)
  ·
    refine ⟨393323133410085811566834845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262215422273390541044556563 393323133410085811566834845)
    ·
      refine ⟨147496175028782179337563067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393323133410085811566834845 147496175028782179337563067)
      ·
        refine ⟨221244262543173269006344601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147496175028782179337563067 221244262543173269006344601)
        ·
          refine ⟨165933196907379951754758451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221244262543173269006344601 165933196907379951754758451)
          ·
            refine ⟨248899795361069927632137677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165933196907379951754758451 248899795361069927632137677)
            ·
              refine ⟨93337423260401222862051629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248899795361069927632137677 93337423260401222862051629)
              ·
                refine ⟨35001533722650458573269361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93337423260401222862051629 35001533722650458573269361)
                ·
                  refine ⟨26251150291987843929952021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35001533722650458573269361 26251150291987843929952021)
                  ·
                    refine ⟨1230522669936930184216501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26251150291987843929952021 1230522669936930184216501)
                    ·
                      rfl

theorem cell23_7189303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_7189303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189303 prefixEnd_7189303 := by exact prefixLift 7189303
  have htrace : WordTrace (prefixWord ++ tailWord_7189303) baseStart_7189303 baseEnd_7189303 := by
    simpa [prefixWord, tailWord_7189303, baseEnd_7189303] using wordTrace_append hprefix tailTrace_7189303
  have hstable : (prefixWord ++ tailWord_7189303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189303).length < 2 ^ (prefixWord ++ tailWord_7189303).sum := by decide
  have hdescent : baseEnd_7189303 < baseStart_7189303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189304 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 2, 1, 3]
def baseStart_7189304 : Nat := 118140960795 + 7189304 * 2 ^ 59
def prefixEnd_7189304 : Nat := 4983230072969 + 3 ^ 40 * 7189304 * 2
def baseEnd_7189304 : Nat := 3691568523291445048736999

theorem tailTrace_7189304 : CollatzResearch.WordTrace tailWord_7189304 prefixEnd_7189304 3691568523291445048736999 := by
  unfold tailWord_7189304
  simp only [CollatzResearch.WordTrace]
  refine ⟨131107729373193459107671483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174810305830924612143561977 131107729373193459107671483)
  ·
    refine ⟨196661594059790188661507225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131107729373193459107671483 196661594059790188661507225)
    ·
      refine ⟨147496195544842641496130419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196661594059790188661507225 147496195544842641496130419)
      ·
        refine ⟨221244293317263962244195629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147496195544842641496130419 221244293317263962244195629)
        ·
          refine ⟨82966609993973985841573361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221244293317263962244195629 82966609993973985841573361)
          ·
            refine ⟨62224957495480489381180021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82966609993973985841573361 62224957495480489381180021)
            ·
              refine ⟨5833589765201295879485627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62224957495480489381180021 5833589765201295879485627)
              ·
                refine ⟨8750384647801943819228441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833589765201295879485627 8750384647801943819228441)
                ·
                  refine ⟨6562788485851457864421331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8750384647801943819228441 6562788485851457864421331)
                  ·
                    refine ⟨9844182728777186796631997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6562788485851457864421331 9844182728777186796631997)
                    ·
                      refine ⟨3691568523291445048736999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9844182728777186796631997 3691568523291445048736999)
                      ·
                        rfl

theorem cell23_7189304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_7189304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189304 prefixEnd_7189304 := by exact prefixLift 7189304
  have htrace : WordTrace (prefixWord ++ tailWord_7189304) baseStart_7189304 baseEnd_7189304 := by
    simpa [prefixWord, tailWord_7189304, baseEnd_7189304] using wordTrace_append hprefix tailTrace_7189304
  have hstable : (prefixWord ++ tailWord_7189304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189304).length < 2 ^ (prefixWord ++ tailWord_7189304).sum := by decide
  have hdescent : baseEnd_7189304 < baseStart_7189304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189330 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_7189330 : Nat := 118140960795 + 7189330 * 2 ^ 59
def prefixEnd_7189330 : Nat := 4983230072969 + 3 ^ 40 * 7189330 * 2
def baseEnd_7189330 : Nat := 3691581873788461947011879

theorem tailTrace_7189330 : CollatzResearch.WordTrace tailWord_7189330 prefixEnd_7189330 3691581873788461947011879 := by
  unfold tailWord_7189330
  simp only [CollatzResearch.WordTrace]
  refine ⟨65554101761073181163947361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174810938029528483103859629 65554101761073181163947361)
  ·
    refine ⟨49165576320804885872960521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65554101761073181163947361 49165576320804885872960521)
    ·
      refine ⟨36874182240603664404720391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49165576320804885872960521 36874182240603664404720391)
      ·
        refine ⟨55311273360905496607080587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36874182240603664404720391 55311273360905496607080587)
        ·
          refine ⟨82966910041358244910620881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55311273360905496607080587 82966910041358244910620881)
          ·
            refine ⟨62225182531018683682965661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82966910041358244910620881 62225182531018683682965661)
            ·
              refine ⟨23334443449132006381112123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62225182531018683682965661 23334443449132006381112123)
              ·
                refine ⟨35001665173698009571668185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23334443449132006381112123 35001665173698009571668185)
                ·
                  refine ⟨26251248880273507178751139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35001665173698009571668185 26251248880273507178751139)
                  ·
                    refine ⟨39376873320410260768126709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26251248880273507178751139 39376873320410260768126709)
                    ·
                      refine ⟨3691581873788461947011879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39376873320410260768126709 3691581873788461947011879)
                      ·
                        rfl

theorem cell23_7189330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_7189330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189330 prefixEnd_7189330 := by exact prefixLift 7189330
  have htrace : WordTrace (prefixWord ++ tailWord_7189330) baseStart_7189330 baseEnd_7189330 := by
    simpa [prefixWord, tailWord_7189330, baseEnd_7189330] using wordTrace_append hprefix tailTrace_7189330
  have hstable : (prefixWord ++ tailWord_7189330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189330).length < 2 ^ (prefixWord ++ tailWord_7189330).sum := by decide
  have hdescent : baseEnd_7189330 < baseStart_7189330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189343 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_7189343 : Nat := 118140960795 + 7189343 * 2 ^ 59
def prefixEnd_7189343 : Nat := 4983230072969 + 3 ^ 40 * 7189343 * 2
def baseEnd_7189343 : Nat := 3691588549036970396149319

theorem tailTrace_7189343 : CollatzResearch.WordTrace tailWord_7189343 prefixEnd_7189343 3691588549036970396149319 := by
  unfold tailWord_7189343
  simp only [CollatzResearch.WordTrace]
  refine ⟨262216881193245627876012683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174811254128830418584008455 262216881193245627876012683)
  ·
    refine ⟨393325321789868441814019025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262216881193245627876012683 393325321789868441814019025)
    ·
      refine ⟨294993991342401331360514269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393325321789868441814019025 294993991342401331360514269)
      ·
        refine ⟨110622746753400499260192851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294993991342401331360514269 110622746753400499260192851)
        ·
          refine ⟨165934120130100748890289277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110622746753400499260192851 165934120130100748890289277)
          ·
            refine ⟨62225295048787780833858479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165934120130100748890289277 62225295048787780833858479)
            ·
              refine ⟨93337942573181671250787719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62225295048787780833858479 93337942573181671250787719)
              ·
                refine ⟨140006913859772506876181579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93337942573181671250787719 140006913859772506876181579)
                ·
                  refine ⟨210010370789658760314272369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140006913859772506876181579 210010370789658760314272369)
                  ·
                    refine ⟨157507778092244070235704277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210010370789658760314272369 157507778092244070235704277)
                    ·
                      refine ⟨3691588549036970396149319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157507778092244070235704277 3691588549036970396149319)
                      ·
                        rfl

theorem cell23_7189343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_7189343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189343 prefixEnd_7189343 := by exact prefixLift 7189343
  have htrace : WordTrace (prefixWord ++ tailWord_7189343) baseStart_7189343 baseEnd_7189343 := by
    simpa [prefixWord, tailWord_7189343, baseEnd_7189343] using wordTrace_append hprefix tailTrace_7189343
  have hstable : (prefixWord ++ tailWord_7189343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189343).length < 2 ^ (prefixWord ++ tailWord_7189343).sum := by decide
  have hdescent : baseEnd_7189343 < baseStart_7189343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189344 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 2, 2, 2]
def baseStart_7189344 : Nat := 118140960795 + 7189344 * 2 ^ 59
def prefixEnd_7189344 : Nat := 4983230072969 + 3 ^ 40 * 7189344 * 2
def baseEnd_7189344 : Nat := 3691589062517624892236815

theorem tailTrace_7189344 : CollatzResearch.WordTrace tailWord_7189344 prefixEnd_7189344 3691589062517624892236815 := by
  unfold tailWord_7189344
  simp only [CollatzResearch.WordTrace]
  refine ⟨131108458833121002523399543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174811278444161336697866057 131108458833121002523399543)
  ·
    refine ⟨196662688249681503785099315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131108458833121002523399543 196662688249681503785099315)
    ·
      refine ⟨294994032374522255677648973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196662688249681503785099315 294994032374522255677648973)
      ·
        refine ⟨110622762140445845879118365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294994032374522255677648973 110622762140445845879118365)
        ·
          refine ⟨41483535802667192204669387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110622762140445845879118365 41483535802667192204669387)
          ·
            refine ⟨62225303704000788307004081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41483535802667192204669387 62225303704000788307004081)
            ·
              refine ⟨46668977778000591230253061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62225303704000788307004081 46668977778000591230253061)
              ·
                refine ⟨8750433333375110855672449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46668977778000591230253061 8750433333375110855672449)
                ·
                  refine ⟨6562825000031333141754337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8750433333375110855672449 6562825000031333141754337)
                  ·
                    refine ⟨4922118750023499856315753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562825000031333141754337 4922118750023499856315753)
                    ·
                      refine ⟨3691589062517624892236815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922118750023499856315753 3691589062517624892236815)
                      ·
                        rfl

theorem cell23_7189344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_7189344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189344 prefixEnd_7189344 := by exact prefixLift 7189344
  have htrace : WordTrace (prefixWord ++ tailWord_7189344) baseStart_7189344 baseEnd_7189344 := by
    simpa [prefixWord, tailWord_7189344, baseEnd_7189344] using wordTrace_append hprefix tailTrace_7189344
  have hstable : (prefixWord ++ tailWord_7189344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189344).length < 2 ^ (prefixWord ++ tailWord_7189344).sum := by decide
  have hdescent : baseEnd_7189344 < baseStart_7189344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189360 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 3]
def baseStart_7189360 : Nat := 118140960795 + 7189360 * 2 ^ 59
def prefixEnd_7189360 : Nat := 4983230072969 + 3 ^ 40 * 7189360 * 2
def baseEnd_7189360 : Nat := 3691597278208096829636741

theorem tailTrace_7189360 : CollatzResearch.WordTrace tailWord_7189360 prefixEnd_7189360 3691597278208096829636741 := by
  unfold tailWord_7189360
  simp only [CollatzResearch.WordTrace]
  refine ⟨131108750617092019889690767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174811667489456026519587689 131108750617092019889690767)
  ·
    refine ⟨196663125925638029834536151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131108750617092019889690767 196663125925638029834536151)
    ·
      refine ⟨294994688888457044751804227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196663125925638029834536151 294994688888457044751804227)
      ·
        refine ⟨442492033332685567127706341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294994688888457044751804227 442492033332685567127706341)
        ·
          refine ⟨82967256249878543836444939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442492033332685567127706341 82967256249878543836444939)
          ·
            refine ⟨124450884374817815754667409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82967256249878543836444939 124450884374817815754667409)
            ·
              refine ⟨93338163281113361816000557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124450884374817815754667409 93338163281113361816000557)
              ·
                refine ⟨35001811230417510681000209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93338163281113361816000557 35001811230417510681000209)
                ·
                  refine ⟨26251358422813133010750157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35001811230417510681000209 26251358422813133010750157)
                  ·
                    refine ⟨9844259408554924879031309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26251358422813133010750157 9844259408554924879031309)
                    ·
                      refine ⟨3691597278208096829636741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9844259408554924879031309 3691597278208096829636741)
                      ·
                        rfl

theorem cell23_7189360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_7189360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189360 prefixEnd_7189360 := by exact prefixLift 7189360
  have htrace : WordTrace (prefixWord ++ tailWord_7189360) baseStart_7189360 baseEnd_7189360 := by
    simpa [prefixWord, tailWord_7189360, baseEnd_7189360] using wordTrace_append hprefix tailTrace_7189360
  have hstable : (prefixWord ++ tailWord_7189360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189360).length < 2 ^ (prefixWord ++ tailWord_7189360).sum := by decide
  have hdescent : baseEnd_7189360 < baseStart_7189360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189361 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 2, 2, 2]
def baseStart_7189361 : Nat := 118140960795 + 7189361 * 2 ^ 59
def prefixEnd_7189361 : Nat := 4983230072969 + 3 ^ 40 * 7189361 * 2
def baseEnd_7189361 : Nat := 3691597791688751325724237

theorem tailTrace_7189361 : CollatzResearch.WordTrace tailWord_7189361 prefixEnd_7189361 3691597791688751325724237 := by
  unfold tailWord_7189361
  simp only [CollatzResearch.WordTrace]
  refine ⟨262217537707180416950167937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174811691804786944633445291 262217537707180416950167937)
  ·
    refine ⟨196663153280385312712625953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262217537707180416950167937 196663153280385312712625953)
    ·
      refine ⟨147497364960288984534469465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196663153280385312712625953 147497364960288984534469465)
      ·
        refine ⟨110623023720216738400852099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147497364960288984534469465 110623023720216738400852099)
        ·
          refine ⟨165934535580325107601278149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110623023720216738400852099 165934535580325107601278149)
          ·
            refine ⟨31112725421310957675239653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165934535580325107601278149 31112725421310957675239653)
            ·
              refine ⟨5833636016495804564107435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31112725421310957675239653 5833636016495804564107435)
              ·
                refine ⟨8750454024743706846161153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833636016495804564107435 8750454024743706846161153)
                ·
                  refine ⟨6562840518557780134620865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8750454024743706846161153 6562840518557780134620865)
                  ·
                    refine ⟨4922130388918335100965649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562840518557780134620865 4922130388918335100965649)
                    ·
                      refine ⟨3691597791688751325724237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922130388918335100965649 3691597791688751325724237)
                      ·
                        rfl

theorem cell23_7189361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_7189361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189361 prefixEnd_7189361 := by exact prefixLift 7189361
  have htrace : WordTrace (prefixWord ++ tailWord_7189361) baseStart_7189361 baseEnd_7189361 := by
    simpa [prefixWord, tailWord_7189361, baseEnd_7189361] using wordTrace_append hprefix tailTrace_7189361
  have hstable : (prefixWord ++ tailWord_7189361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189361).length < 2 ^ (prefixWord ++ tailWord_7189361).sum := by decide
  have hdescent : baseEnd_7189361 < baseStart_7189361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189363 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 3, 7]
def baseStart_7189363 : Nat := 118140960795 + 7189363 * 2 ^ 59
def prefixEnd_7189363 : Nat := 4983230072969 + 3 ^ 40 * 7189363 * 2
def baseEnd_7189363 : Nat := 1230532939550020105966409

theorem tailTrace_7189363 : CollatzResearch.WordTrace tailWord_7189363 prefixEnd_7189363 1230532939550020105966409 := by
  unfold tailWord_7189363
  simp only [CollatzResearch.WordTrace]
  refine ⟨262217610653173171291740743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174811740435448780861160495 262217610653173171291740743)
  ·
    refine ⟨393326415979759756937611115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262217610653173171291740743 393326415979759756937611115)
    ·
      refine ⟨589989623969639635406416673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393326415979759756937611115 589989623969639635406416673)
      ·
        refine ⟨442492217977229726554812505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589989623969639635406416673 442492217977229726554812505)
        ·
          refine ⟨331869163482922294916109379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442492217977229726554812505 331869163482922294916109379)
          ·
            refine ⟨497803745224383442374164069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331869163482922294916109379 497803745224383442374164069)
            ·
              refine ⟨93338202229571895445155763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 497803745224383442374164069 93338202229571895445155763)
              ·
                refine ⟨140007303344357843167733645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93338202229571895445155763 140007303344357843167733645)
                ·
                  refine ⟨52502738754134191187900117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140007303344357843167733645 52502738754134191187900117)
                  ·
                    refine ⟨1230532939550020105966409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52502738754134191187900117 1230532939550020105966409)
                    ·
                      rfl

theorem cell23_7189363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 7].length) (baseStart_7189363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189363 prefixEnd_7189363 := by exact prefixLift 7189363
  have htrace : WordTrace (prefixWord ++ tailWord_7189363) baseStart_7189363 baseEnd_7189363 := by
    simpa [prefixWord, tailWord_7189363, baseEnd_7189363] using wordTrace_append hprefix tailTrace_7189363
  have hstable : (prefixWord ++ tailWord_7189363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189363).length < 2 ^ (prefixWord ++ tailWord_7189363).sum := by decide
  have hdescent : baseEnd_7189363 < baseStart_7189363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189378 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7189378 : Nat := 118140960795 + 7189378 * 2 ^ 59
def prefixEnd_7189378 : Nat := 4983230072969 + 3 ^ 40 * 7189378 * 2
def baseEnd_7189378 : Nat := 3691606520859877759211659

theorem tailTrace_7189378 : CollatzResearch.WordTrace tailWord_7189378 prefixEnd_7189378 3691606520859877759211659 := by
  unfold tailWord_7189378
  simp only [CollatzResearch.WordTrace]
  refine ⟨65554539437029707213384197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174812105165412552569024525 65554539437029707213384197)
  ·
    refine ⟨12291476144443070102509537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65554539437029707213384197 12291476144443070102509537)
    ·
      refine ⟨9218607108332302576882153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12291476144443070102509537 9218607108332302576882153)
      ·
        refine ⟨6913955331249226932661615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9218607108332302576882153 6913955331249226932661615)
        ·
          refine ⟨10370932996873840398992423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6913955331249226932661615 10370932996873840398992423)
          ·
            refine ⟨15556399495310760598488635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10370932996873840398992423 15556399495310760598488635)
            ·
              refine ⟨23334599242966140897732953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15556399495310760598488635 23334599242966140897732953)
              ·
                refine ⟨17500949432224605673299715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23334599242966140897732953 17500949432224605673299715)
                ·
                  refine ⟨26251424148336908509949573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17500949432224605673299715 26251424148336908509949573)
                  ·
                    refine ⟨4922142027813170345615545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26251424148336908509949573 4922142027813170345615545)
                    ·
                      refine ⟨3691606520859877759211659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922142027813170345615545 3691606520859877759211659)
                      ·
                        rfl

theorem cell23_7189378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7189378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189378 prefixEnd_7189378 := by exact prefixLift 7189378
  have htrace : WordTrace (prefixWord ++ tailWord_7189378) baseStart_7189378 baseEnd_7189378 := by
    simpa [prefixWord, tailWord_7189378, baseEnd_7189378] using wordTrace_append hprefix tailTrace_7189378
  have hstable : (prefixWord ++ tailWord_7189378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189378).length < 2 ^ (prefixWord ++ tailWord_7189378).sum := by decide
  have hdescent : baseEnd_7189378 < baseStart_7189378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189417 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 2, 4, 2]
def baseStart_7189417 : Nat := 118140960795 + 7189417 * 2 ^ 59
def prefixEnd_7189417 : Nat := 4983230072969 + 3 ^ 40 * 7189417 * 2
def baseEnd_7189417 : Nat := 3691626546605403106623979

theorem tailTrace_7189417 : CollatzResearch.WordTrace tailWord_7189417 prefixEnd_7189417 3691626546605403106623979 := by
  unfold tailWord_7189417
  simp only [CollatzResearch.WordTrace]
  refine ⟨262219580194977538514206505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174813053463318359009471003 262219580194977538514206505)
  ·
    refine ⟨196664685146233153885654879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262219580194977538514206505 196664685146233153885654879)
    ·
      refine ⟨294997027719349730828482319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196664685146233153885654879 294997027719349730828482319)
      ·
        refine ⟨442495541579024596242723479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294997027719349730828482319 442495541579024596242723479)
        ·
          refine ⟨663743312368536894364085219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442495541579024596242723479 663743312368536894364085219)
          ·
            refine ⟨995614968552805341546127829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663743312368536894364085219 995614968552805341546127829)
            ·
              refine ⟨23334725825456375192487371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 995614968552805341546127829 23334725825456375192487371)
              ·
                refine ⟨35002088738184562788731057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23334725825456375192487371 35002088738184562788731057)
                ·
                  refine ⟨26251566553638422091548293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35002088738184562788731057 26251566553638422091548293)
                  ·
                    refine ⟨4922168728807204142165305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26251566553638422091548293 4922168728807204142165305)
                    ·
                      refine ⟨3691626546605403106623979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922168728807204142165305 3691626546605403106623979)
                      ·
                        rfl

theorem cell23_7189417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 4, 2].length) (baseStart_7189417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189417 prefixEnd_7189417 := by exact prefixLift 7189417
  have htrace : WordTrace (prefixWord ++ tailWord_7189417) baseStart_7189417 baseEnd_7189417 := by
    simpa [prefixWord, tailWord_7189417, baseEnd_7189417] using wordTrace_append hprefix tailTrace_7189417
  have hstable : (prefixWord ++ tailWord_7189417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189417).length < 2 ^ (prefixWord ++ tailWord_7189417).sum := by decide
  have hdescent : baseEnd_7189417 < baseStart_7189417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189420 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_7189420 : Nat := 118140960795 + 7189420 * 2 ^ 59
def prefixEnd_7189420 : Nat := 4983230072969 + 3 ^ 40 * 7189420 * 2
def baseEnd_7189420 : Nat := 3691628087047366594886465

theorem tailTrace_7189420 : CollatzResearch.WordTrace tailWord_7189420 prefixEnd_7189420 3691628087047366594886465 := by
  unfold tailWord_7189420
  simp only [CollatzResearch.WordTrace]
  refine ⟨131109844806983335013282857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174813126409311113351043809 131109844806983335013282857)
  ·
    refine ⟨98332383605237501259962143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131109844806983335013282857 98332383605237501259962143)
    ·
      refine ⟨147498575407856251889943215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98332383605237501259962143 147498575407856251889943215)
      ·
        refine ⟨221247863111784377834914823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147498575407856251889943215 221247863111784377834914823)
        ·
          refine ⟨331871794667676566752372235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221247863111784377834914823 331871794667676566752372235)
          ·
            refine ⟨497807692001514850128558353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331871794667676566752372235 497807692001514850128558353)
            ·
              refine ⟨373355769001136137596418765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497807692001514850128558353 373355769001136137596418765)
              ·
                refine ⟨140008413375426051598657037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373355769001136137596418765 140008413375426051598657037)
                ·
                  refine ⟨52503155015784769349496389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140008413375426051598657037 52503155015784769349496389)
                  ·
                    refine ⟨9844341565459644253030573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52503155015784769349496389 9844341565459644253030573)
                    ·
                      refine ⟨3691628087047366594886465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9844341565459644253030573 3691628087047366594886465)
                      ·
                        rfl

theorem cell23_7189420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_7189420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189420 prefixEnd_7189420 := by exact prefixLift 7189420
  have htrace : WordTrace (prefixWord ++ tailWord_7189420) baseStart_7189420 baseEnd_7189420 := by
    simpa [prefixWord, tailWord_7189420, baseEnd_7189420] using wordTrace_append hprefix tailTrace_7189420
  have hstable : (prefixWord ++ tailWord_7189420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189420).length < 2 ^ (prefixWord ++ tailWord_7189420).sum := by decide
  have hdescent : baseEnd_7189420 < baseStart_7189420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189446 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7189446 : Nat := 118140960795 + 7189446 * 2 ^ 59
def prefixEnd_7189446 : Nat := 4983230072969 + 3 ^ 40 * 7189446 * 2
def baseEnd_7189446 : Nat := 3691641437544383493161347

theorem tailTrace_7189446 : CollatzResearch.WordTrace tailWord_7189446 prefixEnd_7189446 3691641437544383493161347 := by
  unfold tailWord_7189446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8194394934746014889594131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174813758607914984311341461 8194394934746014889594131)
  ·
    refine ⟨12291592402119022334391197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8194394934746014889594131 12291592402119022334391197)
    ·
      refine ⟨4609347150794633375396699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12291592402119022334391197 4609347150794633375396699)
      ·
        refine ⟨6914020726191950063095049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4609347150794633375396699 6914020726191950063095049)
        ·
          refine ⟨5185515544643962547321287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6914020726191950063095049 5185515544643962547321287)
          ·
            refine ⟨7778273316965943820981931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185515544643962547321287 7778273316965943820981931)
            ·
              refine ⟨11667409975448915731472897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7778273316965943820981931 11667409975448915731472897)
              ·
                refine ⟨8750557481586686798604673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11667409975448915731472897 8750557481586686798604673)
                ·
                  refine ⟨6562918111190015098953505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8750557481586686798604673 6562918111190015098953505)
                  ·
                    refine ⟨4922188583392511324215129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562918111190015098953505 4922188583392511324215129)
                    ·
                      refine ⟨3691641437544383493161347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922188583392511324215129 3691641437544383493161347)
                      ·
                        rfl

theorem cell23_7189446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7189446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189446 prefixEnd_7189446 := by exact prefixLift 7189446
  have htrace : WordTrace (prefixWord ++ tailWord_7189446) baseStart_7189446 baseEnd_7189446 := by
    simpa [prefixWord, tailWord_7189446, baseEnd_7189446] using wordTrace_append hprefix tailTrace_7189446
  have hstable : (prefixWord ++ tailWord_7189446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189446).length < 2 ^ (prefixWord ++ tailWord_7189446).sum := by decide
  have hdescent : baseEnd_7189446 < baseStart_7189446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189480 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7189480 : Nat := 118140960795 + 7189480 * 2 ^ 59
def prefixEnd_7189480 : Nat := 4983230072969 + 3 ^ 40 * 7189480 * 2
def baseEnd_7189480 : Nat := 3691658895886636360136189

theorem tailTrace_7189480 : CollatzResearch.WordTrace tailWord_7189480 prefixEnd_7189480 3691658895886636360136189 := by
  unfold tailWord_7189480
  simp only [CollatzResearch.WordTrace]
  refine ⟨131110938996874650136874947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174814585329166200182499929 131110938996874650136874947)
  ·
    refine ⟨196666408495311975205312421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131110938996874650136874947 196666408495311975205312421)
    ·
      refine ⟨36874951592870995350996079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196666408495311975205312421 36874951592870995350996079)
      ·
        refine ⟨55312427389306493026494119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36874951592870995350996079 55312427389306493026494119)
        ·
          refine ⟨82968641083959739539741179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55312427389306493026494119 82968641083959739539741179)
          ·
            refine ⟨124452961625939609309611769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82968641083959739539741179 124452961625939609309611769)
            ·
              refine ⟨93339721219454706982208827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124452961625939609309611769 93339721219454706982208827)
              ·
                refine ⟨140009581829182060473313241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93339721219454706982208827 140009581829182060473313241)
                ·
                  refine ⟨105007186371886545354984931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140009581829182060473313241 105007186371886545354984931)
                  ·
                    refine ⟨157510779557829818032477397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105007186371886545354984931 157510779557829818032477397)
                    ·
                      refine ⟨3691658895886636360136189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157510779557829818032477397 3691658895886636360136189)
                      ·
                        rfl

theorem cell23_7189480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7189480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189480 prefixEnd_7189480 := by exact prefixLift 7189480
  have htrace : WordTrace (prefixWord ++ tailWord_7189480) baseStart_7189480 baseEnd_7189480 := by
    simpa [prefixWord, tailWord_7189480, baseEnd_7189480] using wordTrace_append hprefix tailTrace_7189480
  have hstable : (prefixWord ++ tailWord_7189480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189480).length < 2 ^ (prefixWord ++ tailWord_7189480).sum := by decide
  have hdescent : baseEnd_7189480 < baseStart_7189480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189487 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 1, 5]
def baseStart_7189487 : Nat := 118140960795 + 7189487 * 2 ^ 59
def prefixEnd_7189487 : Nat := 4983230072969 + 3 ^ 40 * 7189487 * 2
def baseEnd_7189487 : Nat := 1230554163417072610916219

theorem tailTrace_7189487 : CollatzResearch.WordTrace tailWord_7189487 prefixEnd_7189487 1230554163417072610916219 := by
  unfold tailWord_7189487
  simp only [CollatzResearch.WordTrace]
  refine ⟨262222133304723940469254715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174814755536482626979503143 262222133304723940469254715)
  ·
    refine ⟨393333199957085910703882073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262222133304723940469254715 393333199957085910703882073)
    ·
      refine ⟨294999899967814433027911555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393333199957085910703882073 294999899967814433027911555)
      ·
        refine ⟨442499849951721649541867333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294999899967814433027911555 442499849951721649541867333)
        ·
          refine ⟨82968721865947809289100125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442499849951721649541867333 82968721865947809289100125)
          ·
            refine ⟨31113270699730428483412547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82968721865947809289100125 31113270699730428483412547)
            ·
              refine ⟨46669906049595642725118821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31113270699730428483412547 46669906049595642725118821)
              ·
                refine ⟨8750607384299183010959779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46669906049595642725118821 8750607384299183010959779)
                ·
                  refine ⟨13125911076448774516439669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8750607384299183010959779 13125911076448774516439669)
                  ·
                    refine ⟨1230554163417072610916219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13125911076448774516439669 1230554163417072610916219)
                    ·
                      rfl

theorem cell23_7189487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 5].length) (baseStart_7189487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189487 prefixEnd_7189487 := by exact prefixLift 7189487
  have htrace : WordTrace (prefixWord ++ tailWord_7189487) baseStart_7189487 baseEnd_7189487 := by
    simpa [prefixWord, tailWord_7189487, baseEnd_7189487] using wordTrace_append hprefix tailTrace_7189487
  have hstable : (prefixWord ++ tailWord_7189487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189487).length < 2 ^ (prefixWord ++ tailWord_7189487).sum := by decide
  have hdescent : baseEnd_7189487 < baseStart_7189487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189520 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_7189520 : Nat := 118140960795 + 7189520 * 2 ^ 59
def prefixEnd_7189520 : Nat := 4983230072969 + 3 ^ 40 * 7189520 * 2
def baseEnd_7189520 : Nat := 3691679435112816203636005

theorem tailTrace_7189520 : CollatzResearch.WordTrace tailWord_7189520 prefixEnd_7189520 3691679435112816203636005 := by
  unfold tailWord_7189520
  simp only [CollatzResearch.WordTrace]
  refine ⟨131111668456802193552603007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174815557942402924736804009 131111668456802193552603007)
  ·
    refine ⟨196667502685203290328904511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131111668456802193552603007 196667502685203290328904511)
    ·
      refine ⟨295001254027804935493356767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196667502685203290328904511 295001254027804935493356767)
      ·
        refine ⟨442501881041707403240035151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295001254027804935493356767 442501881041707403240035151)
        ·
          refine ⟨663752821562561104860052727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442501881041707403240035151 663752821562561104860052727)
          ·
            refine ⟨995629232343841657290079091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663752821562561104860052727 995629232343841657290079091)
            ·
              refine ⟨1493443848515762485935118637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995629232343841657290079091 1493443848515762485935118637)
              ·
                refine ⟨560041443193410932225669489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1493443848515762485935118637 560041443193410932225669489)
                ·
                  refine ⟨420031082395058199169252117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560041443193410932225669489 420031082395058199169252117)
                  ·
                    refine ⟨19688956987268353086058693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 420031082395058199169252117 19688956987268353086058693)
                    ·
                      refine ⟨3691679435112816203636005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19688956987268353086058693 3691679435112816203636005)
                      ·
                        rfl

theorem cell23_7189520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_7189520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189520 prefixEnd_7189520 := by exact prefixLift 7189520
  have htrace : WordTrace (prefixWord ++ tailWord_7189520) baseStart_7189520 baseEnd_7189520 := by
    simpa [prefixWord, tailWord_7189520, baseEnd_7189520] using wordTrace_append hprefix tailTrace_7189520
  have hstable : (prefixWord ++ tailWord_7189520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189520).length < 2 ^ (prefixWord ++ tailWord_7189520).sum := by decide
  have hdescent : baseEnd_7189520 < baseStart_7189520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189537 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7189537 : Nat := 118140960795 + 7189537 * 2 ^ 59
def prefixEnd_7189537 : Nat := 4983230072969 + 3 ^ 40 * 7189537 * 2
def baseEnd_7189537 : Nat := 3691688164283942637123427

theorem tailTrace_7189537 : CollatzResearch.WordTrace tailWord_7189537 prefixEnd_7189537 3691688164283942637123427 := by
  unfold tailWord_7189537
  simp only [CollatzResearch.WordTrace]
  refine ⟨262223956954542799008574865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174815971303028532672383243 262223956954542799008574865)
  ·
    refine ⟨196667967715907099256431149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262223956954542799008574865 196667967715907099256431149)
    ·
      refine ⟨73750487893465162221161681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196667967715907099256431149 73750487893465162221161681)
      ·
        refine ⟨55312865920098871665871261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73750487893465162221161681 55312865920098871665871261)
        ·
          refine ⟨20742324720037076874701723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55312865920098871665871261 20742324720037076874701723)
          ·
            refine ⟨31113487080055615312052585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20742324720037076874701723 31113487080055615312052585)
            ·
              refine ⟨23335115310041711484039439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31113487080055615312052585 23335115310041711484039439)
              ·
                refine ⟨35002672965062567226059159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23335115310041711484039439 35002672965062567226059159)
                ·
                  refine ⟨52504009447593850839088739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35002672965062567226059159 52504009447593850839088739)
                  ·
                    refine ⟨78756014171390776258633109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52504009447593850839088739 78756014171390776258633109)
                    ·
                      refine ⟨3691688164283942637123427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78756014171390776258633109 3691688164283942637123427)
                      ·
                        rfl

theorem cell23_7189537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7189537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189537 prefixEnd_7189537 := by exact prefixLift 7189537
  have htrace : WordTrace (prefixWord ++ tailWord_7189537) baseStart_7189537 baseEnd_7189537 := by
    simpa [prefixWord, tailWord_7189537, baseEnd_7189537] using wordTrace_append hprefix tailTrace_7189537
  have hstable : (prefixWord ++ tailWord_7189537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189537).length < 2 ^ (prefixWord ++ tailWord_7189537).sum := by decide
  have hdescent : baseEnd_7189537 < baseStart_7189537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189558 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_7189558 : Nat := 118140960795 + 7189558 * 2 ^ 59
def prefixEnd_7189558 : Nat := 4983230072969 + 3 ^ 40 * 7189558 * 2
def baseEnd_7189558 : Nat := 3691698947377687054960831

theorem tailTrace_7189558 : CollatzResearch.WordTrace tailWord_7189558 prefixEnd_7189558 3691698947377687054960831 := by
  unfold tailWord_7189558
  simp only [CollatzResearch.WordTrace]
  refine ⟨16389045180466669974693083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174816481924977813063392885 16389045180466669974693083)
  ·
    refine ⟨24583567770700004962039625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16389045180466669974693083 24583567770700004962039625)
    ·
      refine ⟨18437675828025003721529719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24583567770700004962039625 18437675828025003721529719)
      ·
        refine ⟨27656513742037505582294579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18437675828025003721529719 27656513742037505582294579)
        ·
          refine ⟨41484770613056258373441869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27656513742037505582294579 41484770613056258373441869)
          ·
            refine ⟨15556788979896096890040701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41484770613056258373441869 15556788979896096890040701)
            ·
              refine ⟨5833795867461036333765263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15556788979896096890040701 5833795867461036333765263)
              ·
                refine ⟨8750693801191554500647895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833795867461036333765263 8750693801191554500647895)
                ·
                  refine ⟨13126040701787331750971843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8750693801191554500647895 13126040701787331750971843)
                  ·
                    refine ⟨19689061052680997626457765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13126040701787331750971843 19689061052680997626457765)
                    ·
                      refine ⟨3691698947377687054960831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19689061052680997626457765 3691698947377687054960831)
                      ·
                        rfl

theorem cell23_7189558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_7189558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189558 prefixEnd_7189558 := by exact prefixLift 7189558
  have htrace : WordTrace (prefixWord ++ tailWord_7189558) baseStart_7189558 baseEnd_7189558 := by
    simpa [prefixWord, tailWord_7189558, baseEnd_7189558] using wordTrace_append hprefix tailTrace_7189558
  have hstable : (prefixWord ++ tailWord_7189558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189558).length < 2 ^ (prefixWord ++ tailWord_7189558).sum := by decide
  have hdescent : baseEnd_7189558 < baseStart_7189558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189575 : List Nat := [1, 1, 4, 1, 3, 2, 4, 2, 1, 2, 2]
def baseStart_7189575 : Nat := 118140960795 + 7189575 * 2 ^ 59
def prefixEnd_7189575 : Nat := 4983230072969 + 3 ^ 40 * 7189575 * 2
def baseEnd_7189575 : Nat := 3691707676548813488448253

theorem tailTrace_7189575 : CollatzResearch.WordTrace tailWord_7189575 prefixEnd_7189575 3691707676548813488448253 := by
  unfold tailWord_7189575
  simp only [CollatzResearch.WordTrace]
  refine ⟨262225342928405131498458179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174816895285603420998972119 262225342928405131498458179)
  ·
    refine ⟨393338014392607697247687269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262225342928405131498458179 393338014392607697247687269)
    ·
      refine ⟨73750877698613943233941363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393338014392607697247687269 73750877698613943233941363)
      ·
        refine ⟨110626316547920914850912045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73750877698613943233941363 110626316547920914850912045)
        ·
          refine ⟨41484868705470343069092017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110626316547920914850912045 41484868705470343069092017)
          ·
            refine ⟨31113651529102757301819013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41484868705470343069092017 31113651529102757301819013)
            ·
              refine ⟨5833809661706766994091065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31113651529102757301819013 5833809661706766994091065)
              ·
                refine ⟨4375357246280075245568299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5833809661706766994091065 4375357246280075245568299)
                ·
                  refine ⟨6563035869420112868352449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375357246280075245568299 6563035869420112868352449)
                  ·
                    refine ⟨4922276902065084651264337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6563035869420112868352449 4922276902065084651264337)
                    ·
                      refine ⟨3691707676548813488448253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922276902065084651264337 3691707676548813488448253)
                      ·
                        rfl

theorem cell23_7189575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_7189575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189575 prefixEnd_7189575 := by exact prefixLift 7189575
  have htrace : WordTrace (prefixWord ++ tailWord_7189575) baseStart_7189575 baseEnd_7189575 := by
    simpa [prefixWord, tailWord_7189575, baseEnd_7189575] using wordTrace_append hprefix tailTrace_7189575
  have hstable : (prefixWord ++ tailWord_7189575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189575).length < 2 ^ (prefixWord ++ tailWord_7189575).sum := by decide
  have hdescent : baseEnd_7189575 < baseStart_7189575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189598 : List Nat := [4, 4, 1, 1, 1, 2, 3, 7]
def baseStart_7189598 : Nat := 118140960795 + 7189598 * 2 ^ 59
def prefixEnd_7189598 : Nat := 4983230072969 + 3 ^ 40 * 7189598 * 2
def baseEnd_7189598 : Nat := 136730351355698774017061

theorem tailTrace_7189598 : CollatzResearch.WordTrace tailWord_7189598 prefixEnd_7189598 136730351355698774017061 := by
  unfold tailWord_7189598
  simp only [CollatzResearch.WordTrace]
  refine ⟨32778272725915225803318181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174817454538214537617696965 32778272725915225803318181)
  ·
    refine ⟨6145926136109104838122159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32778272725915225803318181 6145926136109104838122159)
    ·
      refine ⟨9218889204163657257183239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6145926136109104838122159 9218889204163657257183239)
      ·
        refine ⟨13828333806245485885774859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9218889204163657257183239 13828333806245485885774859)
        ·
          refine ⟨20742500709368228828662289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13828333806245485885774859 20742500709368228828662289)
          ·
            refine ⟨15556875532026171621496717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20742500709368228828662289 15556875532026171621496717)
            ·
              refine ⟨5833828324509814358061269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15556875532026171621496717 5833828324509814358061269)
              ·
                refine ⟨136730351355698774017061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5833828324509814358061269 136730351355698774017061)
                ·
                  rfl

theorem cell23_7189598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_7189598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189598 prefixEnd_7189598 := by exact prefixLift 7189598
  have htrace : WordTrace (prefixWord ++ tailWord_7189598) baseStart_7189598 baseEnd_7189598 := by
    simpa [prefixWord, tailWord_7189598, baseEnd_7189598] using wordTrace_append hprefix tailTrace_7189598
  have hstable : (prefixWord ++ tailWord_7189598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189598).length < 2 ^ (prefixWord ++ tailWord_7189598).sum := by decide
  have hdescent : baseEnd_7189598 < baseStart_7189598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189617 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_7189617 : Nat := 118140960795 + 7189617 * 2 ^ 59
def prefixEnd_7189617 : Nat := 4983230072969 + 3 ^ 40 * 7189617 * 2
def baseEnd_7189617 : Nat := 3691729242736302324123059

theorem tailTrace_7189617 : CollatzResearch.WordTrace tailWord_7189617 prefixEnd_7189617 3691729242736302324123059 := by
  unfold tailWord_7189617
  simp only [CollatzResearch.WordTrace]
  refine ⟨262226874794252972671487105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174817916529501981780991403 262226874794252972671487105)
  ·
    refine ⟨196670156095689729503615329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262226874794252972671487105 196670156095689729503615329)
    ·
      refine ⟨147502617071767297127711497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196670156095689729503615329 147502617071767297127711497)
      ·
        refine ⟨110626962803825472845783623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147502617071767297127711497 110626962803825472845783623)
        ·
          refine ⟨165940444205738209268675435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110626962803825472845783623 165940444205738209268675435)
          ·
            refine ⟨248910666308607313903013153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165940444205738209268675435 248910666308607313903013153)
            ·
              refine ⟨186682999731455485427259865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248910666308607313903013153 186682999731455485427259865)
              ·
                refine ⟨140012249798591614070444899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186682999731455485427259865 140012249798591614070444899)
                ·
                  refine ⟨210018374697887421105667349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140012249798591614070444899 210018374697887421105667349)
                  ·
                    refine ⟨9844611313963472864328157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 210018374697887421105667349 9844611313963472864328157)
                    ·
                      refine ⟨3691729242736302324123059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9844611313963472864328157 3691729242736302324123059)
                      ·
                        rfl

theorem cell23_7189617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_7189617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189617 prefixEnd_7189617 := by exact prefixLift 7189617
  have htrace : WordTrace (prefixWord ++ tailWord_7189617) baseStart_7189617 baseEnd_7189617 := by
    simpa [prefixWord, tailWord_7189617, baseEnd_7189617] using wordTrace_append hprefix tailTrace_7189617
  have hstable : (prefixWord ++ tailWord_7189617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189617).length < 2 ^ (prefixWord ++ tailWord_7189617).sum := by decide
  have hdescent : baseEnd_7189617 < baseStart_7189617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189625 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 2, 1, 3]
def baseStart_7189625 : Nat := 118140960795 + 7189625 * 2 ^ 59
def prefixEnd_7189625 : Nat := 4983230072969 + 3 ^ 40 * 7189625 * 2
def baseEnd_7189625 : Nat := 3691733350581538292823023

theorem tailTrace_7189625 : CollatzResearch.WordTrace tailWord_7189625 prefixEnd_7189625 3691733350581538292823023 := by
  unfold tailWord_7189625
  simp only [CollatzResearch.WordTrace]
  refine ⟨262227166578223990037778329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174818111052149326691852219 262227166578223990037778329)
  ·
    refine ⟨196670374933667992528333747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262227166578223990037778329 196670374933667992528333747)
    ·
      refine ⟨295005562400501988792500621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196670374933667992528333747 295005562400501988792500621)
      ·
        refine ⟨110627085900188245797187733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295005562400501988792500621 110627085900188245797187733)
        ·
          refine ⟨5185644651571324021743175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110627085900188245797187733 5185644651571324021743175)
          ·
            refine ⟨7778466977356986032614763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185644651571324021743175 7778466977356986032614763)
            ·
              refine ⟨11667700466035479048922145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7778466977356986032614763 11667700466035479048922145)
              ·
                refine ⟨8750775349526609286691609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11667700466035479048922145 8750775349526609286691609)
                ·
                  refine ⟨6563081512144956965018707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8750775349526609286691609 6563081512144956965018707)
                  ·
                    refine ⟨9844622268217435447528061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563081512144956965018707 9844622268217435447528061)
                    ·
                      refine ⟨3691733350581538292823023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9844622268217435447528061 3691733350581538292823023)
                      ·
                        rfl

theorem cell23_7189625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_7189625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189625 prefixEnd_7189625 := by exact prefixLift 7189625
  have htrace : WordTrace (prefixWord ++ tailWord_7189625) baseStart_7189625 baseEnd_7189625 := by
    simpa [prefixWord, tailWord_7189625, baseEnd_7189625] using wordTrace_append hprefix tailTrace_7189625
  have hstable : (prefixWord ++ tailWord_7189625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189625).length < 2 ^ (prefixWord ++ tailWord_7189625).sum := by decide
  have hdescent : baseEnd_7189625 < baseStart_7189625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189647 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 3]
def baseStart_7189647 : Nat := 118140960795 + 7189647 * 2 ^ 59
def prefixEnd_7189647 : Nat := 4983230072969 + 3 ^ 40 * 7189647 * 2
def baseEnd_7189647 : Nat := 3691744647155937206747921

theorem tailTrace_7189647 : CollatzResearch.WordTrace tailWord_7189647 prefixEnd_7189647 3691744647155937206747921 := by
  unfold tailWord_7189647
  simp only [CollatzResearch.WordTrace]
  refine ⟨262227968984144287795079195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174818645989429525196719463 262227968984144287795079195)
  ·
    refine ⟨393341953476216431692618793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262227968984144287795079195 393341953476216431692618793)
    ·
      refine ⟨295006465107162323769464095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393341953476216431692618793 295006465107162323769464095)
      ·
        refine ⟨442509697660743485654196143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295006465107162323769464095 442509697660743485654196143)
        ·
          refine ⟨663764546491115228481294215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442509697660743485654196143 663764546491115228481294215)
          ·
            refine ⟨995646819736672842721941323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663764546491115228481294215 995646819736672842721941323)
            ·
              refine ⟨1493470229605009264082911985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995646819736672842721941323 1493470229605009264082911985)
              ·
                refine ⟨1120102672203756948062183989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1493470229605009264082911985 1120102672203756948062183989)
                ·
                  refine ⟨105009625519102213880829749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1120102672203756948062183989 105009625519102213880829749)
                  ·
                    refine ⟨9844652392415832551327789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105009625519102213880829749 9844652392415832551327789)
                    ·
                      refine ⟨3691744647155937206747921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9844652392415832551327789 3691744647155937206747921)
                      ·
                        rfl

theorem cell23_7189647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_7189647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189647 prefixEnd_7189647 := by exact prefixLift 7189647
  have htrace : WordTrace (prefixWord ++ tailWord_7189647) baseStart_7189647 baseEnd_7189647 := by
    simpa [prefixWord, tailWord_7189647, baseEnd_7189647] using wordTrace_append hprefix tailTrace_7189647
  have hstable : (prefixWord ++ tailWord_7189647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189647).length < 2 ^ (prefixWord ++ tailWord_7189647).sum := by decide
  have hdescent : baseEnd_7189647 < baseStart_7189647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189667 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 6, 5]
def baseStart_7189667 : Nat := 118140960795 + 7189667 * 2 ^ 59
def prefixEnd_7189667 : Nat := 4983230072969 + 3 ^ 40 * 7189667 * 2
def baseEnd_7189667 : Nat := 1230584972256342376165943

theorem tailTrace_7189667 : CollatzResearch.WordTrace tailWord_7189667 prefixEnd_7189667 1230584972256342376165943 := by
  unfold tailWord_7189667
  simp only [CollatzResearch.WordTrace]
  refine ⟨262228698444071831210807255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174819132296047887473871503 262228698444071831210807255)
  ·
    refine ⟨393343047666107746816210883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262228698444071831210807255 393343047666107746816210883)
    ·
      refine ⟨590014571499161620224316325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393343047666107746816210883 590014571499161620224316325)
      ·
        refine ⟨110627732156092803792059311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 590014571499161620224316325 110627732156092803792059311)
        ·
          refine ⟨165941598234139205688088967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110627732156092803792059311 165941598234139205688088967)
          ·
            refine ⟨248912397351208808532133451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165941598234139205688088967 248912397351208808532133451)
            ·
              refine ⟨373368596026813212798200177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248912397351208808532133451 373368596026813212798200177)
              ·
                refine ⟨280026447020109909598650133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373368596026813212798200177 280026447020109909598650133)
                ·
                  refine ⟨13126239704067652012436725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 280026447020109909598650133 13126239704067652012436725)
                  ·
                    refine ⟨1230584972256342376165943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13126239704067652012436725 1230584972256342376165943)
                    ·
                      rfl

theorem cell23_7189667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 5].length) (baseStart_7189667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189667 prefixEnd_7189667 := by exact prefixLift 7189667
  have htrace : WordTrace (prefixWord ++ tailWord_7189667) baseStart_7189667 baseEnd_7189667 := by
    simpa [prefixWord, tailWord_7189667, baseEnd_7189667] using wordTrace_append hprefix tailTrace_7189667
  have hstable : (prefixWord ++ tailWord_7189667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189667).length < 2 ^ (prefixWord ++ tailWord_7189667).sum := by decide
  have hdescent : baseEnd_7189667 < baseStart_7189667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189694 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_7189694 : Nat := 118140960795 + 7189694 * 2 ^ 59
def prefixEnd_7189694 : Nat := 4983230072969 + 3 ^ 40 * 7189694 * 2
def baseEnd_7189694 : Nat := 3691768780746698522860205

theorem tailTrace_7189694 : CollatzResearch.WordTrace tailWord_7189694 prefixEnd_7189694 3691768780746698522860205 := by
  unfold tailWord_7189694
  simp only [CollatzResearch.WordTrace]
  refine ⟨32778710401871751852755017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174819788809982676548026757 32778710401871751852755017)
  ·
    refine ⟨24584032801403813889566263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32778710401871751852755017 24584032801403813889566263)
    ·
      refine ⟨36876049202105720834349395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24584032801403813889566263 36876049202105720834349395)
      ·
        refine ⟨55314073803158581251524093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36876049202105720834349395 55314073803158581251524093)
        ·
          refine ⟨20742777676184467969321535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55314073803158581251524093 20742777676184467969321535)
          ·
            refine ⟨31114166514276701953982303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20742777676184467969321535 31114166514276701953982303)
            ·
              refine ⟨46671249771415052930973455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31114166514276701953982303 46671249771415052930973455)
              ·
                refine ⟨70006874657122579396460183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46671249771415052930973455 70006874657122579396460183)
                ·
                  refine ⟨105010311985683869094690275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70006874657122579396460183 105010311985683869094690275)
                  ·
                    refine ⟨157515467978525803642035413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105010311985683869094690275 157515467978525803642035413)
                    ·
                      refine ⟨3691768780746698522860205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157515467978525803642035413 3691768780746698522860205)
                      ·
                        rfl

theorem cell23_7189694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_7189694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189694 prefixEnd_7189694 := by exact prefixLift 7189694
  have htrace : WordTrace (prefixWord ++ tailWord_7189694) baseStart_7189694 baseEnd_7189694 := by
    simpa [prefixWord, tailWord_7189694, baseEnd_7189694] using wordTrace_append hprefix tailTrace_7189694
  have hstable : (prefixWord ++ tailWord_7189694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189694).length < 2 ^ (prefixWord ++ tailWord_7189694).sum := by decide
  have hdescent : baseEnd_7189694 < baseStart_7189694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189727 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 10]
def baseStart_7189727 : Nat := 118140960795 + 7189727 * 2 ^ 59
def prefixEnd_7189727 : Nat := 4983230072969 + 3 ^ 40 * 7189727 * 2
def baseEnd_7189727 : Nat := 410198413956477432638617

theorem tailTrace_7189727 : CollatzResearch.WordTrace tailWord_7189727 prefixEnd_7189727 410198413956477432638617 := by
  unfold tailWord_7189727
  simp only [CollatzResearch.WordTrace]
  refine ⟨262230886823854461457991435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174820591215902974305327623 262230886823854461457991435)
  ·
    refine ⟨393346330235781692186987153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262230886823854461457991435 393346330235781692186987153)
    ·
      refine ⟨295009747676836269140240365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393346330235781692186987153 295009747676836269140240365)
      ·
        refine ⟨110628655378813600927590137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295009747676836269140240365 110628655378813600927590137)
        ·
          refine ⟨82971491534110200695692603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110628655378813600927590137 82971491534110200695692603)
          ·
            refine ⟨124457237301165301043538905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82971491534110200695692603 124457237301165301043538905)
            ·
              refine ⟨93342927975873975782654179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124457237301165301043538905 93342927975873975782654179)
              ·
                refine ⟨140014391963810963673981269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93342927975873975782654179 140014391963810963673981269)
                ·
                  refine ⟨410198413956477432638617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 140014391963810963673981269 410198413956477432638617)
                  ·
                    rfl

theorem cell23_7189727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 10].length) (baseStart_7189727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189727 prefixEnd_7189727 := by exact prefixLift 7189727
  have htrace : WordTrace (prefixWord ++ tailWord_7189727) baseStart_7189727 baseEnd_7189727 := by
    simpa [prefixWord, tailWord_7189727, baseEnd_7189727] using wordTrace_append hprefix tailTrace_7189727
  have hstable : (prefixWord ++ tailWord_7189727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189727).length < 2 ^ (prefixWord ++ tailWord_7189727).sum := by decide
  have hdescent : baseEnd_7189727 < baseStart_7189727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189771 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 3]
def baseStart_7189771 : Nat := 118140960795 + 7189771 * 2 ^ 59
def prefixEnd_7189771 : Nat := 4983230072969 + 3 ^ 40 * 7189771 * 2
def baseEnd_7189771 : Nat := 3691808318757094721597351

theorem tailTrace_7189771 : CollatzResearch.WordTrace tailWord_7189771 prefixEnd_7189771 3691808318757094721597351 := by
  unfold tailWord_7189771
  simp only [CollatzResearch.WordTrace]
  refine ⟨262232491635695056972593167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174821661090463371315062111 262232491635695056972593167)
  ·
    refine ⟨393348737453542585458889751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262232491635695056972593167 393348737453542585458889751)
    ·
      refine ⟨590023106180313878188334627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393348737453542585458889751 590023106180313878188334627)
      ·
        refine ⟨885034659270470817282501941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590023106180313878188334627 885034659270470817282501941)
        ·
          refine ⟨82971999306606639120234557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 885034659270470817282501941 82971999306606639120234557)
          ·
            refine ⟨31114499739977489670087959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82971999306606639120234557 31114499739977489670087959)
            ·
              refine ⟨46671749609966234505131939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31114499739977489670087959 46671749609966234505131939)
              ·
                refine ⟨70007624414949351757697909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46671749609966234505131939 70007624414949351757697909)
                ·
                  refine ⟨6563214788901501727284179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70007624414949351757697909 6563214788901501727284179)
                  ·
                    refine ⟨9844822183352252590926269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563214788901501727284179 9844822183352252590926269)
                    ·
                      refine ⟨3691808318757094721597351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9844822183352252590926269 3691808318757094721597351)
                      ·
                        rfl

theorem cell23_7189771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 3].length) (baseStart_7189771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189771 prefixEnd_7189771 := by exact prefixLift 7189771
  have htrace : WordTrace (prefixWord ++ tailWord_7189771) baseStart_7189771 baseEnd_7189771 := by
    simpa [prefixWord, tailWord_7189771, baseEnd_7189771] using wordTrace_append hprefix tailTrace_7189771
  have hstable : (prefixWord ++ tailWord_7189771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189771).length < 2 ^ (prefixWord ++ tailWord_7189771).sum := by decide
  have hdescent : baseEnd_7189771 < baseStart_7189771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189805 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_7189805 : Nat := 118140960795 + 7189805 * 2 ^ 59
def prefixEnd_7189805 : Nat := 4983230072969 + 3 ^ 40 * 7189805 * 2
def baseEnd_7189805 : Nat := 3691825777099347588572195

theorem tailTrace_7189805 : CollatzResearch.WordTrace tailWord_7189805 prefixEnd_7189805 3691825777099347588572195 := by
  unfold tailWord_7189805
  simp only [CollatzResearch.WordTrace]
  refine ⟨262233731717571880779330869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174822487811714587186220579 262233731717571880779330869)
  ·
    refine ⟨24584412348522363823062269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262233731717571880779330869 24584412348522363823062269)
    ·
      refine ⟨9219154630695886433648351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24584412348522363823062269 9219154630695886433648351)
      ·
        refine ⟨13828731946043829650472527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9219154630695886433648351 13828731946043829650472527)
        ·
          refine ⟨20743097919065744475708791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13828731946043829650472527 20743097919065744475708791)
          ·
            refine ⟨31114646878598616713563187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20743097919065744475708791 31114646878598616713563187)
            ·
              refine ⟨46671970317897925070344781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31114646878598616713563187 46671970317897925070344781)
              ·
                refine ⟨17501988869211721901379293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46671970317897925070344781 17501988869211721901379293)
                ·
                  refine ⟨6563245825954395713017235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17501988869211721901379293 6563245825954395713017235)
                  ·
                    refine ⟨9844868738931593569525853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563245825954395713017235 9844868738931593569525853)
                    ·
                      refine ⟨3691825777099347588572195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9844868738931593569525853 3691825777099347588572195)
                      ·
                        rfl

theorem cell23_7189805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_7189805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189805 prefixEnd_7189805 := by exact prefixLift 7189805
  have htrace : WordTrace (prefixWord ++ tailWord_7189805) baseStart_7189805 baseEnd_7189805 := by
    simpa [prefixWord, tailWord_7189805, baseEnd_7189805] using wordTrace_append hprefix tailTrace_7189805
  have hstable : (prefixWord ++ tailWord_7189805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189805).length < 2 ^ (prefixWord ++ tailWord_7189805).sum := by decide
  have hdescent : baseEnd_7189805 < baseStart_7189805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189824 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_7189824 : Nat := 118140960795 + 7189824 * 2 ^ 59
def prefixEnd_7189824 : Nat := 4983230072969 + 3 ^ 40 * 7189824 * 2
def baseEnd_7189824 : Nat := 3691835533231783014234607

theorem tailTrace_7189824 : CollatzResearch.WordTrace tailWord_7189824 prefixEnd_7189824 3691835533231783014234607 := by
  unfold tailWord_7189824
  simp only [CollatzResearch.WordTrace]
  refine ⟨131117212352251523512136263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174822949803002031349515017 131117212352251523512136263)
  ·
    refine ⟨196675818528377285268204395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131117212352251523512136263 196675818528377285268204395)
    ·
      refine ⟨295013727792565927902306593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196675818528377285268204395 295013727792565927902306593)
      ·
        refine ⟨221260295844424445926729945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295013727792565927902306593 221260295844424445926729945)
        ·
          refine ⟨165945221883318334445047459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221260295844424445926729945 165945221883318334445047459)
          ·
            refine ⟨248917832824977501667571189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165945221883318334445047459 248917832824977501667571189)
            ·
              refine ⟨23336046827341640781334799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248917832824977501667571189 23336046827341640781334799)
              ·
                refine ⟨35004070241012461172002199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23336046827341640781334799 35004070241012461172002199)
                ·
                  refine ⟨52506105361518691758003299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35004070241012461172002199 52506105361518691758003299)
                  ·
                    refine ⟨78759158042278037637004949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52506105361518691758003299 78759158042278037637004949)
                    ·
                      refine ⟨3691835533231783014234607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78759158042278037637004949 3691835533231783014234607)
                      ·
                        rfl

theorem cell23_7189824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_7189824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189824 prefixEnd_7189824 := by exact prefixLift 7189824
  have htrace : WordTrace (prefixWord ++ tailWord_7189824) baseStart_7189824 baseEnd_7189824 := by
    simpa [prefixWord, tailWord_7189824, baseEnd_7189824] using wordTrace_append hprefix tailTrace_7189824
  have hstable : (prefixWord ++ tailWord_7189824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189824).length < 2 ^ (prefixWord ++ tailWord_7189824).sum := by decide
  have hdescent : baseEnd_7189824 < baseStart_7189824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189912 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7189912 : Nat := 118140960795 + 7189912 * 2 ^ 59
def prefixEnd_7189912 : Nat := 4983230072969 + 3 ^ 40 * 7189912 * 2
def baseEnd_7189912 : Nat := 3691880719529378669934203

theorem tailTrace_7189912 : CollatzResearch.WordTrace tailWord_7189912 prefixEnd_7189912 3691880719529378669934203 := by
  unfold tailWord_7189912
  simp only [CollatzResearch.WordTrace]
  refine ⟨131118817164092119026737995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174825089552122825368983993 131118817164092119026737995)
  ·
    refine ⟨196678225746138178540106993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131118817164092119026737995 196678225746138178540106993)
    ·
      refine ⟨147508669309603633905080245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196678225746138178540106993 147508669309603633905080245)
      ·
        refine ⟨13828937747775340678601273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147508669309603633905080245 13828937747775340678601273)
        ·
          refine ⟨10371703310831505508950955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13828937747775340678601273 10371703310831505508950955)
          ·
            refine ⟨15557554966247258263426433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10371703310831505508950955 15557554966247258263426433)
            ·
              refine ⟨11668166224685443697569825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15557554966247258263426433 11668166224685443697569825)
              ·
                refine ⟨8751124668514082773177369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11668166224685443697569825 8751124668514082773177369)
                ·
                  refine ⟨6563343501385562079883027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8751124668514082773177369 6563343501385562079883027)
                  ·
                    refine ⟨9845015252078343119824541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563343501385562079883027 9845015252078343119824541)
                    ·
                      refine ⟨3691880719529378669934203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9845015252078343119824541 3691880719529378669934203)
                      ·
                        rfl

theorem cell23_7189912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7189912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189912 prefixEnd_7189912 := by exact prefixLift 7189912
  have htrace : WordTrace (prefixWord ++ tailWord_7189912) baseStart_7189912 baseEnd_7189912 := by
    simpa [prefixWord, tailWord_7189912, baseEnd_7189912] using wordTrace_append hprefix tailTrace_7189912
  have hstable : (prefixWord ++ tailWord_7189912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189912).length < 2 ^ (prefixWord ++ tailWord_7189912).sum := by decide
  have hdescent : baseEnd_7189912 < baseStart_7189912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189941 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 9]
def baseStart_7189941 : Nat := 118140960795 + 7189941 * 2 ^ 59
def prefixEnd_7189941 : Nat := 4983230072969 + 3 ^ 40 * 7189941 * 2
def baseEnd_7189941 : Nat := 410210623385373228496841

theorem tailTrace_7189941 : CollatzResearch.WordTrace tailWord_7189941 prefixEnd_7189941 410210623385373228496841 := by
  unfold tailWord_7189941
  simp only [CollatzResearch.WordTrace]
  refine ⟨262238692045079176006281677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174825794696719450670854451 262238692045079176006281677)
  ·
    refine ⟨98339509516904691002355629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262238692045079176006281677 98339509516904691002355629)
    ·
      refine ⟨36877316068839259125883361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98339509516904691002355629 36877316068839259125883361)
      ·
        refine ⟨27657987051629444344412521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36877316068839259125883361 27657987051629444344412521)
        ·
          refine ⟨20743490288722083258309391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27657987051629444344412521 20743490288722083258309391)
          ·
            refine ⟨31115235433083124887464087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20743490288722083258309391 31115235433083124887464087)
            ·
              refine ⟨46672853149624687331196131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31115235433083124887464087 46672853149624687331196131)
              ·
                refine ⟨70009279724437030996794197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46672853149624687331196131 70009279724437030996794197)
                ·
                  refine ⟨410210623385373228496841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70009279724437030996794197 410210623385373228496841)
                  ·
                    rfl

theorem cell23_7189941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_7189941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7189941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7189941 prefixEnd_7189941 := by exact prefixLift 7189941
  have htrace : WordTrace (prefixWord ++ tailWord_7189941) baseStart_7189941 baseEnd_7189941 := by
    simpa [prefixWord, tailWord_7189941, baseEnd_7189941] using wordTrace_append hprefix tailTrace_7189941
  have hstable : (prefixWord ++ tailWord_7189941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189941).length < 2 ^ (prefixWord ++ tailWord_7189941).sum := by decide
  have hdescent : baseEnd_7189941 < baseStart_7189941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190035 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 3, 4]
def baseStart_7190035 : Nat := 118140960795 + 7190035 * 2 ^ 59
def prefixEnd_7190035 : Nat := 4983230072969 + 3 ^ 40 * 7190035 * 2
def baseEnd_7190035 : Nat := 1230647959216627229565379

theorem tailTrace_7190035 : CollatzResearch.WordTrace tailWord_7190035 prefixEnd_7190035 1230647959216627229565379 := by
  unfold tailWord_7190035
  simp only [CollatzResearch.WordTrace]
  refine ⟨262242120506738630060203559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174828080337825753373469039 262242120506738630060203559)
  ·
    refine ⟨393363180760107945090305339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262242120506738630060203559 393363180760107945090305339)
    ·
      refine ⟨590044771140161917635458009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393363180760107945090305339 590044771140161917635458009)
      ·
        refine ⟨442533578355121438226593507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590044771140161917635458009 442533578355121438226593507)
        ·
          refine ⟨663800367532682157339890261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442533578355121438226593507 663800367532682157339890261)
          ·
            refine ⟨7778910557023619031326839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 663800367532682157339890261 7778910557023619031326839)
            ·
              refine ⟨11668365835535428546990259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7778910557023619031326839 11668365835535428546990259)
              ·
                refine ⟨17502548753303142820485389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11668365835535428546990259 17502548753303142820485389)
                ·
                  refine ⟨6563455782488678557682021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17502548753303142820485389 6563455782488678557682021)
                  ·
                    refine ⟨1230647959216627229565379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6563455782488678557682021 1230647959216627229565379)
                    ·
                      rfl

theorem cell23_7190035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 4].length) (baseStart_7190035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190035 prefixEnd_7190035 := by exact prefixLift 7190035
  have htrace : WordTrace (prefixWord ++ tailWord_7190035) baseStart_7190035 baseEnd_7190035 := by
    simpa [prefixWord, tailWord_7190035, baseEnd_7190035] using wordTrace_append hprefix tailTrace_7190035
  have hstable : (prefixWord ++ tailWord_7190035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190035).length < 2 ^ (prefixWord ++ tailWord_7190035).sum := by decide
  have hdescent : baseEnd_7190035 < baseStart_7190035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190062 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_7190062 : Nat := 118140960795 + 7190062 * 2 ^ 59
def prefixEnd_7190062 : Nat := 4983230072969 + 3 ^ 40 * 7190062 * 2
def baseEnd_7190062 : Nat := 3691957741627553083058513

theorem tailTrace_7190062 : CollatzResearch.WordTrace tailWord_7190062 prefixEnd_7190062 3691957741627553083058513 := by
  unfold tailWord_7190062
  simp only [CollatzResearch.WordTrace]
  refine ⟨32780388159705101708929555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174828736851760542447624293 32780388159705101708929555)
  ·
    refine ⟨49170582239557652563394333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32780388159705101708929555 49170582239557652563394333)
    ·
      refine ⟨18438968339834119711272875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49170582239557652563394333 18438968339834119711272875)
      ·
        refine ⟨27658452509751179566909313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18438968339834119711272875 27658452509751179566909313)
        ·
          refine ⟨20743839382313384675181985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27658452509751179566909313 20743839382313384675181985)
          ·
            refine ⟨15557879536735038506386489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20743839382313384675181985 15557879536735038506386489)
            ·
              refine ⟨11668409652551278879789867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15557879536735038506386489 11668409652551278879789867)
              ·
                refine ⟨17502614478826918319684801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11668409652551278879789867 17502614478826918319684801)
                ·
                  refine ⟨13126960859120188739763601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17502614478826918319684801 13126960859120188739763601)
                  ·
                    refine ⟨9845220644340141554822701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13126960859120188739763601 9845220644340141554822701)
                    ·
                      refine ⟨3691957741627553083058513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9845220644340141554822701 3691957741627553083058513)
                      ·
                        rfl

theorem cell23_7190062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_7190062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190062 prefixEnd_7190062 := by exact prefixLift 7190062
  have htrace : WordTrace (prefixWord ++ tailWord_7190062) baseStart_7190062 baseEnd_7190062 := by
    simpa [prefixWord, tailWord_7190062, baseEnd_7190062] using wordTrace_append hprefix tailTrace_7190062
  have hstable : (prefixWord ++ tailWord_7190062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190062).length < 2 ^ (prefixWord ++ tailWord_7190062).sum := by decide
  have hdescent : baseEnd_7190062 < baseStart_7190062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190085 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 2, 3, 2]
def baseStart_7190085 : Nat := 118140960795 + 7190085 * 2 ^ 59
def prefixEnd_7190085 : Nat := 4983230072969 + 3 ^ 40 * 7190085 * 2
def baseEnd_7190085 : Nat := 3691969551682606493070907

theorem tailTrace_7190085 : CollatzResearch.WordTrace tailWord_7190085 prefixEnd_7190085 3691969551682606493070907 := by
  unfold tailWord_7190085
  simp only [CollatzResearch.WordTrace]
  refine ⟨262243944156557488599523709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174829296104371659066349139 262243944156557488599523709)
  ·
    refine ⟨98341479058709058224821391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262243944156557488599523709 98341479058709058224821391)
    ·
      refine ⟨147512218588063587337232087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98341479058709058224821391 147512218588063587337232087)
      ·
        refine ⟨221268327882095381005848131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147512218588063587337232087 221268327882095381005848131)
        ·
          refine ⟨331902491823143071508772197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221268327882095381005848131 331902491823143071508772197)
          ·
            refine ⟨62231717216839325907894787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331902491823143071508772197 62231717216839325907894787)
            ·
              refine ⟨93347575825258988861842181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62231717216839325907894787 93347575825258988861842181)
              ·
                refine ⟨17502670467236060411595409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93347575825258988861842181 17502670467236060411595409)
                ·
                  refine ⟨13127002850427045308696557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17502670467236060411595409 13127002850427045308696557)
                  ·
                    refine ⟨4922626068910141990761209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13127002850427045308696557 4922626068910141990761209)
                    ·
                      refine ⟨3691969551682606493070907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922626068910141990761209 3691969551682606493070907)
                      ·
                        rfl

theorem cell23_7190085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_7190085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190085 prefixEnd_7190085 := by exact prefixLift 7190085
  have htrace : WordTrace (prefixWord ++ tailWord_7190085) baseStart_7190085 baseEnd_7190085 := by
    simpa [prefixWord, tailWord_7190085, baseEnd_7190085] using wordTrace_append hprefix tailTrace_7190085
  have hstable : (prefixWord ++ tailWord_7190085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190085).length < 2 ^ (prefixWord ++ tailWord_7190085).sum := by decide
  have hdescent : baseEnd_7190085 < baseStart_7190085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190086 : List Nat := [6, 1, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_7190086 : Nat := 118140960795 + 7190086 * 2 ^ 59
def prefixEnd_7190086 : Nat := 4983230072969 + 3 ^ 40 * 7190086 * 2
def baseEnd_7190086 : Nat := 1230656688387753663052801

theorem tailTrace_7190086 : CollatzResearch.WordTrace tailWord_7190086 prefixEnd_7190086 1230656688387753663052801 := by
  unfold tailWord_7190086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195124394673558305322191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174829320419702577180206741 8195124394673558305322191)
  ·
    refine ⟨12292686592010337457983287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195124394673558305322191 12292686592010337457983287)
    ·
      refine ⟨18439029888015506186974931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12292686592010337457983287 18439029888015506186974931)
      ·
        refine ⟨27658544832023259280462397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18439029888015506186974931 27658544832023259280462397)
        ·
          refine ⟨10371954312008722230173399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27658544832023259280462397 10371954312008722230173399)
          ·
            refine ⟨15557931468013083345260099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10371954312008722230173399 15557931468013083345260099)
            ·
              refine ⟨23336897202019625017890149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15557931468013083345260099 23336897202019625017890149)
              ·
                refine ⟨4375668225378679690854403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23336897202019625017890149 4375668225378679690854403)
                ·
                  refine ⟨6563502338068019536281605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375668225378679690854403 6563502338068019536281605)
                  ·
                    refine ⟨1230656688387753663052801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6563502338068019536281605 1230656688387753663052801)
                    ·
                      rfl

theorem cell23_7190086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_7190086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190086 prefixEnd_7190086 := by exact prefixLift 7190086
  have htrace : WordTrace (prefixWord ++ tailWord_7190086) baseStart_7190086 baseEnd_7190086 := by
    simpa [prefixWord, tailWord_7190086, baseEnd_7190086] using wordTrace_append hprefix tailTrace_7190086
  have hstable : (prefixWord ++ tailWord_7190086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190086).length < 2 ^ (prefixWord ++ tailWord_7190086).sum := by decide
  have hdescent : baseEnd_7190086 < baseStart_7190086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190091 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 5, 6]
def baseStart_7190091 : Nat := 118140960795 + 7190091 * 2 ^ 59
def prefixEnd_7190091 : Nat := 4983230072969 + 3 ^ 40 * 7190091 * 2
def baseEnd_7190091 : Nat := 1230657544188844489865293

theorem tailTrace_7190091 : CollatzResearch.WordTrace tailWord_7190091 prefixEnd_7190091 1230657544188844489865293 := by
  unfold tailWord_7190091
  simp only [CollatzResearch.WordTrace]
  refine ⟨262244162994535751624242127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174829441996357167749494751 262244162994535751624242127)
  ·
    refine ⟨393366244491803627436363191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262244162994535751624242127 393366244491803627436363191)
    ·
      refine ⟨590049366737705441154544787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393366244491803627436363191 590049366737705441154544787)
      ·
        refine ⟨885074050106558161731817181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590049366737705441154544787 885074050106558161731817181)
        ·
          refine ⟨331902768789959310649431443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 885074050106558161731817181 331902768789959310649431443)
          ·
            refine ⟨497854153184938965974147165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331902768789959310649431443 497854153184938965974147165)
            ·
              refine ⟨186695307444352112240305187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497854153184938965974147165 186695307444352112240305187)
              ·
                refine ⟨280042961166528168360457781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186695307444352112240305187 280042961166528168360457781)
                ·
                  refine ⟨26254027609362015783792917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280042961166528168360457781 26254027609362015783792917)
                  ·
                    refine ⟨1230657544188844489865293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26254027609362015783792917 1230657544188844489865293)
                    ·
                      rfl

theorem cell23_7190091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 6].length) (baseStart_7190091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190091 prefixEnd_7190091 := by exact prefixLift 7190091
  have htrace : WordTrace (prefixWord ++ tailWord_7190091) baseStart_7190091 baseEnd_7190091 := by
    simpa [prefixWord, tailWord_7190091, baseEnd_7190091] using wordTrace_append hprefix tailTrace_7190091
  have hstable : (prefixWord ++ tailWord_7190091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190091).length < 2 ^ (prefixWord ++ tailWord_7190091).sum := by decide
  have hdescent : baseEnd_7190091 < baseStart_7190091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190121 : List Nat := [1, 2, 1, 1, 1, 4, 2, 11]
def baseStart_7190121 : Nat := 118140960795 + 7190121 * 2 ^ 59
def prefixEnd_7190121 : Nat := 4983230072969 + 3 ^ 40 * 7190121 * 2
def baseEnd_7190121 : Nat := 136740297666154383415583

theorem tailTrace_7190121 : CollatzResearch.WordTrace tailWord_7190121 prefixEnd_7190121 136740297666154383415583 := by
  unfold tailWord_7190121
  simp only [CollatzResearch.WordTrace]
  refine ⟨262245257184427066747834217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174830171456284711165222811 262245257184427066747834217)
  ·
    refine ⟨196683942888320300060875663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262245257184427066747834217 196683942888320300060875663)
    ·
      refine ⟨295025914332480450091313495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196683942888320300060875663 295025914332480450091313495)
      ·
        refine ⟨442538871498720675136970243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295025914332480450091313495 442538871498720675136970243)
        ·
          refine ⟨663808307248081012705455365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442538871498720675136970243 663808307248081012705455365)
          ·
            refine ⟨124464057609015189882272881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 663808307248081012705455365 124464057609015189882272881)
            ·
              refine ⟨93348043206761392411704661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124464057609015189882272881 93348043206761392411704661)
              ·
                refine ⟨136740297666154383415583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93348043206761392411704661 136740297666154383415583)
                ·
                  rfl

theorem cell23_7190121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 11].length) (baseStart_7190121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190121 prefixEnd_7190121 := by exact prefixLift 7190121
  have htrace : WordTrace (prefixWord ++ tailWord_7190121) baseStart_7190121 baseEnd_7190121 := by
    simpa [prefixWord, tailWord_7190121, baseEnd_7190121] using wordTrace_append hprefix tailTrace_7190121
  have hstable : (prefixWord ++ tailWord_7190121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190121).length < 2 ^ (prefixWord ++ tailWord_7190121).sum := by decide
  have hdescent : baseEnd_7190121 < baseStart_7190121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190126 : List Nat := [4, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_7190126 : Nat := 118140960795 + 7190126 * 2 ^ 59
def prefixEnd_7190126 : Nat := 4983230072969 + 3 ^ 40 * 7190126 * 2
def baseEnd_7190126 : Nat := 3691990604389440832658219

theorem tailTrace_7190126 : CollatzResearch.WordTrace tailWord_7190126 prefixEnd_7190126 3691990604389440832658219 := by
  unfold tailWord_7190126
  simp only [CollatzResearch.WordTrace]
  refine ⟨32780679943676119075220779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174830293032939301734510821 32780679943676119075220779)
  ·
    refine ⟨49171019915514178612831169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32780679943676119075220779 49171019915514178612831169)
    ·
      refine ⟨36878264936635633959623377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49171019915514178612831169 36878264936635633959623377)
      ·
        refine ⟨27658698702476725469717533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36878264936635633959623377 27658698702476725469717533)
        ·
          refine ⟨10372012013428772051144075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27658698702476725469717533 10372012013428772051144075)
          ·
            refine ⟨15558018020143158076716113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10372012013428772051144075 15558018020143158076716113)
            ·
              refine ⟨11668513515107368557537085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15558018020143158076716113 11668513515107368557537085)
              ·
                refine ⟨4375692568165263209076407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11668513515107368557537085 4375692568165263209076407)
                ·
                  refine ⟨6563538852247894813614611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375692568165263209076407 6563538852247894813614611)
                  ·
                    refine ⟨9845308278371842220421917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563538852247894813614611 9845308278371842220421917)
                    ·
                      refine ⟨3691990604389440832658219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9845308278371842220421917 3691990604389440832658219)
                      ·
                        rfl

theorem cell23_7190126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_7190126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190126 prefixEnd_7190126 := by exact prefixLift 7190126
  have htrace : WordTrace (prefixWord ++ tailWord_7190126) baseStart_7190126 baseEnd_7190126 := by
    simpa [prefixWord, tailWord_7190126, baseEnd_7190126] using wordTrace_append hprefix tailTrace_7190126
  have hstable : (prefixWord ++ tailWord_7190126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190126).length < 2 ^ (prefixWord ++ tailWord_7190126).sum := by decide
  have hdescent : baseEnd_7190126 < baseStart_7190126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190131 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 7]
def baseStart_7190131 : Nat := 118140960795 + 7190131 * 2 ^ 59
def prefixEnd_7190131 : Nat := 4983230072969 + 3 ^ 40 * 7190131 * 2
def baseEnd_7190131 : Nat := 3691993171792713313095695

theorem tailTrace_7190131 : CollatzResearch.WordTrace tailWord_7190131 prefixEnd_7190131 3691993171792713313095695 := by
  unfold tailWord_7190131
  simp only [CollatzResearch.WordTrace]
  refine ⟨262245621914390838455698247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174830414609593892303798831 262245621914390838455698247)
  ·
    refine ⟨393368432871586257683547371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262245621914390838455698247 393368432871586257683547371)
    ·
      refine ⟨590052649307379386525321057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393368432871586257683547371 590052649307379386525321057)
      ·
        refine ⟨442539486980534539893990793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590052649307379386525321057 442539486980534539893990793)
        ·
          refine ⟨331904615235400904920493095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442539486980534539893990793 331904615235400904920493095)
          ·
            refine ⟨497856922853101357380739643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331904615235400904920493095 497856922853101357380739643)
            ·
              refine ⟨746785384279652036071109465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497856922853101357380739643 746785384279652036071109465)
              ·
                refine ⟨560089038209739027053332099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746785384279652036071109465 560089038209739027053332099)
                ·
                  refine ⟨840133557314608540579998149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560089038209739027053332099 840133557314608540579998149)
                  ·
                    refine ⟨157525041996489101358749653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840133557314608540579998149 157525041996489101358749653)
                    ·
                      refine ⟨3691993171792713313095695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157525041996489101358749653 3691993171792713313095695)
                      ·
                        rfl

theorem cell23_7190131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_7190131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190131 prefixEnd_7190131 := by exact prefixLift 7190131
  have htrace : WordTrace (prefixWord ++ tailWord_7190131) baseStart_7190131 baseEnd_7190131 := by
    simpa [prefixWord, tailWord_7190131, baseEnd_7190131] using wordTrace_append hprefix tailTrace_7190131
  have hstable : (prefixWord ++ tailWord_7190131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190131).length < 2 ^ (prefixWord ++ tailWord_7190131).sum := by decide
  have hdescent : baseEnd_7190131 < baseStart_7190131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190149 : List Nat := [1, 3, 1, 1, 4, 1, 1, 6, 1, 2, 2]
def baseStart_7190149 : Nat := 118140960795 + 7190149 * 2 ^ 59
def prefixEnd_7190149 : Nat := 4983230072969 + 3 ^ 40 * 7190149 * 2
def baseEnd_7190149 : Nat := 3692002414444494242670613

theorem tailTrace_7190149 : CollatzResearch.WordTrace tailWord_7190149 prefixEnd_7190149 3692002414444494242670613 := by
  unfold tailWord_7190149
  simp only [CollatzResearch.WordTrace]
  refine ⟨262246278428325627529853501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174830852285550418353235667 262246278428325627529853501)
  ·
    refine ⟨98342354410622110323695063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262246278428325627529853501 98342354410622110323695063)
    ·
      refine ⟨147513531615933165485542595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98342354410622110323695063 147513531615933165485542595)
      ·
        refine ⟨221270297423899748228313893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147513531615933165485542595 221270297423899748228313893)
        ·
          refine ⟨41488180766981202792808855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221270297423899748228313893 41488180766981202792808855)
          ·
            refine ⟨62232271150471804189213283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41488180766981202792808855 62232271150471804189213283)
            ·
              refine ⟨93348406725707706283819925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62232271150471804189213283 93348406725707706283819925)
              ·
                refine ⟨4375706565267548732054059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93348406725707706283819925 4375706565267548732054059)
                ·
                  refine ⟨6563559847901323098081089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375706565267548732054059 6563559847901323098081089)
                  ·
                    refine ⟨4922669885925992323560817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6563559847901323098081089 4922669885925992323560817)
                    ·
                      refine ⟨3692002414444494242670613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922669885925992323560817 3692002414444494242670613)
                      ·
                        rfl

theorem cell23_7190149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 2, 2].length) (baseStart_7190149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190149 prefixEnd_7190149 := by exact prefixLift 7190149
  have htrace : WordTrace (prefixWord ++ tailWord_7190149) baseStart_7190149 baseEnd_7190149 := by
    simpa [prefixWord, tailWord_7190149, baseEnd_7190149] using wordTrace_append hprefix tailTrace_7190149
  have hstable : (prefixWord ++ tailWord_7190149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190149).length < 2 ^ (prefixWord ++ tailWord_7190149).sum := by decide
  have hdescent : baseEnd_7190149 < baseStart_7190149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190152 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7190152 : Nat := 118140960795 + 7190152 * 2 ^ 59
def prefixEnd_7190152 : Nat := 4983230072969 + 3 ^ 40 * 7190152 * 2
def baseEnd_7190152 : Nat := 3692003954886457730933099

theorem tailTrace_7190152 : CollatzResearch.WordTrace tailWord_7190152 prefixEnd_7190152 3692003954886457730933099 := by
  unfold tailWord_7190152
  simp only [CollatzResearch.WordTrace]
  refine ⟨131123193923657379521106355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174830925231543172694808473 131123193923657379521106355)
  ·
    refine ⟨196684790885486069281659533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131123193923657379521106355 196684790885486069281659533)
    ·
      refine ⟨73756796582057275980622325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196684790885486069281659533 73756796582057275980622325)
      ·
        refine ⟨6914699679567869623183343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73756796582057275980622325 6914699679567869623183343)
        ·
          refine ⟨10372049519351804434775015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6914699679567869623183343 10372049519351804434775015)
          ·
            refine ⟨15558074279027706652162523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10372049519351804434775015 15558074279027706652162523)
            ·
              refine ⟨23337111418541559978243785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15558074279027706652162523 23337111418541559978243785)
              ·
                refine ⟨17502833563906169983682839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23337111418541559978243785 17502833563906169983682839)
                ·
                  refine ⟨26254250345859254975524259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17502833563906169983682839 26254250345859254975524259)
                  ·
                    refine ⟨39381375518788882463286389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26254250345859254975524259 39381375518788882463286389)
                    ·
                      refine ⟨3692003954886457730933099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39381375518788882463286389 3692003954886457730933099)
                      ·
                        rfl

theorem cell23_7190152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7190152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190152 prefixEnd_7190152 := by exact prefixLift 7190152
  have htrace : WordTrace (prefixWord ++ tailWord_7190152) baseStart_7190152 baseEnd_7190152 := by
    simpa [prefixWord, tailWord_7190152, baseEnd_7190152] using wordTrace_append hprefix tailTrace_7190152
  have hstable : (prefixWord ++ tailWord_7190152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190152).length < 2 ^ (prefixWord ++ tailWord_7190152).sum := by decide
  have hdescent : baseEnd_7190152 < baseStart_7190152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190172 : List Nat := [2, 2, 3, 2, 3, 2, 2, 7]
def baseStart_7190172 : Nat := 118140960795 + 7190172 * 2 ^ 59
def prefixEnd_7190172 : Nat := 4983230072969 + 3 ^ 40 * 7190172 * 2
def baseEnd_7190172 : Nat := 136741267574057320469741

theorem tailTrace_7190172 : CollatzResearch.WordTrace tailWord_7190172 prefixEnd_7190172 136741267574057320469741 := by
  unfold tailWord_7190172
  simp only [CollatzResearch.WordTrace]
  refine ⟨131123558653621151228970385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174831411538161534971960513 131123558653621151228970385)
  ·
    refine ⟨98342668990215863421727789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131123558653621151228970385 98342668990215863421727789)
    ·
      refine ⟨36878500871330948783147921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98342668990215863421727789 36878500871330948783147921)
      ·
        refine ⟨27658875653498211587360941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36878500871330948783147921 27658875653498211587360941)
        ·
          refine ⟨10372078370061829345260353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27658875653498211587360941 10372078370061829345260353)
          ·
            refine ⟨7779058777546372008945265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10372078370061829345260353 7779058777546372008945265)
            ·
              refine ⟨5834294083159779006708949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7779058777546372008945265 5834294083159779006708949)
              ·
                refine ⟨136741267574057320469741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5834294083159779006708949 136741267574057320469741)
                ·
                  rfl

theorem cell23_7190172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 7].length) (baseStart_7190172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190172 prefixEnd_7190172 := by exact prefixLift 7190172
  have htrace : WordTrace (prefixWord ++ tailWord_7190172) baseStart_7190172 baseEnd_7190172 := by
    simpa [prefixWord, tailWord_7190172, baseEnd_7190172] using wordTrace_append hprefix tailTrace_7190172
  have hstable : (prefixWord ++ tailWord_7190172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190172).length < 2 ^ (prefixWord ++ tailWord_7190172).sum := by decide
  have hdescent : baseEnd_7190172 < baseStart_7190172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190192 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 1, 3, 2]
def baseStart_7190192 : Nat := 118140960795 + 7190192 * 2 ^ 59
def prefixEnd_7190192 : Nat := 4983230072969 + 3 ^ 40 * 7190192 * 2
def baseEnd_7190192 : Nat := 3692024494112637574432915

theorem tailTrace_7190192 : CollatzResearch.WordTrace tailWord_7190192 prefixEnd_7190192 3692024494112637574432915 := by
  unfold tailWord_7190192
  simp only [CollatzResearch.WordTrace]
  refine ⟨131123923383584922936834415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174831897844779897249112553 131123923383584922936834415)
  ·
    refine ⟨196685885075377384405251623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131123923383584922936834415 196685885075377384405251623)
    ·
      refine ⟨295028827613066076607877435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196685885075377384405251623 295028827613066076607877435)
      ·
        refine ⟨442543241419599114911816153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295028827613066076607877435 442543241419599114911816153)
        ·
          refine ⟨331907431064699336183862115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442543241419599114911816153 331907431064699336183862115)
          ·
            refine ⟨497861146597049004275793173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331907431064699336183862115 497861146597049004275793173)
            ·
              refine ⟨23337241246736672075427805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 497861146597049004275793173 23337241246736672075427805)
              ·
                refine ⟨8751465467526252028285427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23337241246736672075427805 8751465467526252028285427)
                ·
                  refine ⟨13127198201289378042428141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8751465467526252028285427 13127198201289378042428141)
                  ·
                    refine ⟨4922699325483516765910553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13127198201289378042428141 4922699325483516765910553)
                    ·
                      refine ⟨3692024494112637574432915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922699325483516765910553 3692024494112637574432915)
                      ·
                        rfl

theorem cell23_7190192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 3, 2].length) (baseStart_7190192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190192 prefixEnd_7190192 := by exact prefixLift 7190192
  have htrace : WordTrace (prefixWord ++ tailWord_7190192) baseStart_7190192 baseEnd_7190192 := by
    simpa [prefixWord, tailWord_7190192, baseEnd_7190192] using wordTrace_append hprefix tailTrace_7190192
  have hstable : (prefixWord ++ tailWord_7190192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190192).length < 2 ^ (prefixWord ++ tailWord_7190192).sum := by decide
  have hdescent : baseEnd_7190192 < baseStart_7190192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190208 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_7190208 : Nat := 118140960795 + 7190208 * 2 ^ 59
def prefixEnd_7190208 : Nat := 4983230072969 + 3 ^ 40 * 7190208 * 2
def baseEnd_7190208 : Nat := 3692032709803109511832841

theorem tailTrace_7190208 : CollatzResearch.WordTrace tailWord_7190208 prefixEnd_7190208 3692032709803109511832841 := by
  unfold tailWord_7190208
  simp only [CollatzResearch.WordTrace]
  refine ⟨131124215167555940303125639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174832286890074587070834185 131124215167555940303125639)
  ·
    refine ⟨196686322751333910454688459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131124215167555940303125639 196686322751333910454688459)
    ·
      refine ⟨295029484127000865682032689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196686322751333910454688459 295029484127000865682032689)
      ·
        refine ⟨221272113095250649261524517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295029484127000865682032689 221272113095250649261524517)
        ·
          refine ⟨41488521205359496736535847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221272113095250649261524517 41488521205359496736535847)
          ·
            refine ⟨62232781808039245104803771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41488521205359496736535847 62232781808039245104803771)
            ·
              refine ⟨93349172712058867657205657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62232781808039245104803771 93349172712058867657205657)
              ·
                refine ⟨70011879534044150742904243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93349172712058867657205657 70011879534044150742904243)
                ·
                  refine ⟨105017819301066226114356365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70011879534044150742904243 105017819301066226114356365)
                  ·
                    refine ⟨39381682237899834792883637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105017819301066226114356365 39381682237899834792883637)
                    ·
                      refine ⟨3692032709803109511832841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39381682237899834792883637 3692032709803109511832841)
                      ·
                        rfl

theorem cell23_7190208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_7190208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190208 prefixEnd_7190208 := by exact prefixLift 7190208
  have htrace : WordTrace (prefixWord ++ tailWord_7190208) baseStart_7190208 baseEnd_7190208 := by
    simpa [prefixWord, tailWord_7190208, baseEnd_7190208] using wordTrace_append hprefix tailTrace_7190208
  have hstable : (prefixWord ++ tailWord_7190208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190208).length < 2 ^ (prefixWord ++ tailWord_7190208).sum := by decide
  have hdescent : baseEnd_7190208 < baseStart_7190208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190210 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_7190210 : Nat := 118140960795 + 7190210 * 2 ^ 59
def prefixEnd_7190210 : Nat := 4983230072969 + 3 ^ 40 * 7190210 * 2
def baseEnd_7190210 : Nat := 1230677912254806168002611

theorem tailTrace_7190210 : CollatzResearch.WordTrace tailWord_7190210 prefixEnd_7190210 1230677912254806168002611 := by
  unfold tailWord_7190210
  simp only [CollatzResearch.WordTrace]
  refine ⟨65562125820276158736956021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174832335520736423298549389 65562125820276158736956021)
  ·
    refine ⟨6146449295650889881589627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65562125820276158736956021 6146449295650889881589627)
    ·
      refine ⟨9219673943476334822384441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6146449295650889881589627 9219673943476334822384441)
      ·
        refine ⟨6914755457607251116788331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9219673943476334822384441 6914755457607251116788331)
        ·
          refine ⟨10372133186410876675182497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6914755457607251116788331 10372133186410876675182497)
          ·
            refine ⟨7779099889808157506386873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10372133186410876675182497 7779099889808157506386873)
            ·
              refine ⟨5834324917356118129790155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7779099889808157506386873 5834324917356118129790155)
              ·
                refine ⟨8751487376034177194685233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5834324917356118129790155 8751487376034177194685233)
                ·
                  refine ⟨6563615532025632896013925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8751487376034177194685233 6563615532025632896013925)
                  ·
                    refine ⟨1230677912254806168002611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6563615532025632896013925 1230677912254806168002611)
                    ·
                      rfl

theorem cell23_7190210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_7190210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190210 prefixEnd_7190210 := by exact prefixLift 7190210
  have htrace : WordTrace (prefixWord ++ tailWord_7190210) baseStart_7190210 baseEnd_7190210 := by
    simpa [prefixWord, tailWord_7190210, baseEnd_7190210] using wordTrace_append hprefix tailTrace_7190210
  have hstable : (prefixWord ++ tailWord_7190210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190210).length < 2 ^ (prefixWord ++ tailWord_7190210).sum := by decide
  have hdescent : baseEnd_7190210 < baseStart_7190210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190222 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_7190222 : Nat := 118140960795 + 7190222 * 2 ^ 59
def prefixEnd_7190222 : Nat := 4983230072969 + 3 ^ 40 * 7190222 * 2
def baseEnd_7190222 : Nat := 3692039898532272457057777

theorem tailTrace_7190222 : CollatzResearch.WordTrace tailWord_7190222 prefixEnd_7190222 3692039898532272457057777 := by
  unfold tailWord_7190222
  simp only [CollatzResearch.WordTrace]
  refine ⟨32781117619632645124657615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174832627304707440664840613 32781117619632645124657615)
  ·
    refine ⟨49171676429448967686986423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32781117619632645124657615 49171676429448967686986423)
    ·
      refine ⟨73757514644173451530479635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49171676429448967686986423 73757514644173451530479635)
      ·
        refine ⟨110636271966260177295719453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73757514644173451530479635 110636271966260177295719453)
        ·
          refine ⟨41488601987347566485894795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110636271966260177295719453 41488601987347566485894795)
          ·
            refine ⟨62232902981021349728842193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41488601987347566485894795 62232902981021349728842193)
            ·
              refine ⟨46674677235766012296631645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62232902981021349728842193 46674677235766012296631645)
              ·
                refine ⟨17503003963412254611236867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46674677235766012296631645 17503003963412254611236867)
                ·
                  refine ⟨26254505945118381916855301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17503003963412254611236867 26254505945118381916855301)
                  ·
                    refine ⟨4922719864709696609410369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26254505945118381916855301 4922719864709696609410369)
                    ·
                      refine ⟨3692039898532272457057777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922719864709696609410369 3692039898532272457057777)
                      ·
                        rfl

theorem cell23_7190222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_7190222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190222 prefixEnd_7190222 := by exact prefixLift 7190222
  have htrace : WordTrace (prefixWord ++ tailWord_7190222) baseStart_7190222 baseEnd_7190222 := by
    simpa [prefixWord, tailWord_7190222, baseEnd_7190222] using wordTrace_append hprefix tailTrace_7190222
  have hstable : (prefixWord ++ tailWord_7190222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190222).length < 2 ^ (prefixWord ++ tailWord_7190222).sum := by decide
  have hdescent : baseEnd_7190222 < baseStart_7190222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190226 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_7190226 : Nat := 118140960795 + 7190226 * 2 ^ 59
def prefixEnd_7190226 : Nat := 4983230072969 + 3 ^ 40 * 7190226 * 2
def baseEnd_7190226 : Nat := 3692041952454890441407759

theorem tailTrace_7190226 : CollatzResearch.WordTrace tailWord_7190226 prefixEnd_7190226 3692041952454890441407759 := by
  unfold tailWord_7190226
  simp only [CollatzResearch.WordTrace]
  refine ⟨65562271712261667420101633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174832724566031113120271021 65562271712261667420101633)
  ·
    refine ⟨49171703784196250565076225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65562271712261667420101633 49171703784196250565076225)
    ·
      refine ⟨36878777838147187923807169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49171703784196250565076225 36878777838147187923807169)
      ·
        refine ⟨27659083378610390942855377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36878777838147187923807169 27659083378610390942855377)
        ·
          refine ⟨20744312533957793207141533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27659083378610390942855377 20744312533957793207141533)
          ·
            refine ⟨7779117200234172452678075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20744312533957793207141533 7779117200234172452678075)
            ·
              refine ⟨11668675800351258679017113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779117200234172452678075 11668675800351258679017113)
              ·
                refine ⟨8751506850263444009262835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11668675800351258679017113 8751506850263444009262835)
                ·
                  refine ⟨13127260275395166013894253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8751506850263444009262835 13127260275395166013894253)
                  ·
                    refine ⟨4922722603273187255210345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13127260275395166013894253 4922722603273187255210345)
                    ·
                      refine ⟨3692041952454890441407759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922722603273187255210345 3692041952454890441407759)
                      ·
                        rfl

theorem cell23_7190226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_7190226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190226 prefixEnd_7190226 := by exact prefixLift 7190226
  have htrace : WordTrace (prefixWord ++ tailWord_7190226) baseStart_7190226 baseEnd_7190226 := by
    simpa [prefixWord, tailWord_7190226, baseEnd_7190226] using wordTrace_append hprefix tailTrace_7190226
  have hstable : (prefixWord ++ tailWord_7190226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190226).length < 2 ^ (prefixWord ++ tailWord_7190226).sum := by decide
  have hdescent : baseEnd_7190226 < baseStart_7190226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190255 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 3]
def baseStart_7190255 : Nat := 118140960795 + 7190255 * 2 ^ 59
def prefixEnd_7190255 : Nat := 4983230072969 + 3 ^ 40 * 7190255 * 2
def baseEnd_7190255 : Nat := 3692056843393870827945125

theorem tailTrace_7190255 : CollatzResearch.WordTrace tailWord_7190255 prefixEnd_7190255 3692056843393870827945125 := by
  unfold tailWord_7190255
  simp only [CollatzResearch.WordTrace]
  refine ⟨262250144565941607633212219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174833429710627738422141479 262250144565941607633212219)
  ·
    refine ⟨393375216848912411449818329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262250144565941607633212219 393375216848912411449818329)
    ·
      refine ⟨295031412636684308587363747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393375216848912411449818329 295031412636684308587363747)
      ·
        refine ⟨442547118955026462881045621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295031412636684308587363747 442547118955026462881045621)
        ·
          refine ⟨41488792402033730895098027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 442547118955026462881045621 41488792402033730895098027)
          ·
            refine ⟨62233188603050596342647041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41488792402033730895098027 62233188603050596342647041)
            ·
              refine ⟨46674891452287947256985281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62233188603050596342647041 46674891452287947256985281)
              ·
                refine ⟨35006168589215960442738961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46674891452287947256985281 35006168589215960442738961)
                ·
                  refine ⟨26254626441911970332054221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35006168589215960442738961 26254626441911970332054221)
                  ·
                    refine ⟨9845484915716988874520333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26254626441911970332054221 9845484915716988874520333)
                    ·
                      refine ⟨3692056843393870827945125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9845484915716988874520333 3692056843393870827945125)
                      ·
                        rfl

theorem cell23_7190255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_7190255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190255 prefixEnd_7190255 := by exact prefixLift 7190255
  have htrace : WordTrace (prefixWord ++ tailWord_7190255) baseStart_7190255 baseEnd_7190255 := by
    simpa [prefixWord, tailWord_7190255, baseEnd_7190255] using wordTrace_append hprefix tailTrace_7190255
  have hstable : (prefixWord ++ tailWord_7190255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190255).length < 2 ^ (prefixWord ++ tailWord_7190255).sum := by decide
  have hdescent : baseEnd_7190255 < baseStart_7190255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190322 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_7190322 : Nat := 118140960795 + 7190322 * 2 ^ 59
def prefixEnd_7190322 : Nat := 4983230072969 + 3 ^ 40 * 7190322 * 2
def baseEnd_7190322 : Nat := 1230697082199240688602439

theorem tailTrace_7190322 : CollatzResearch.WordTrace tailWord_7190322 prefixEnd_7190322 1230697082199240688602439 := by
  unfold tailWord_7190322
  simp only [CollatzResearch.WordTrace]
  refine ⟨65563147064174719518975305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174835058837799252050600813 65563147064174719518975305)
  ·
    refine ⟨49172360298131039639231479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65563147064174719518975305 49172360298131039639231479)
    ·
      refine ⟨73758540447196559458847219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49172360298131039639231479 73758540447196559458847219)
      ·
        refine ⟨110637810670794839188270829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73758540447196559458847219 110637810670794839188270829)
        ·
          refine ⟨41489179001548064695601561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110637810670794839188270829 41489179001548064695601561)
          ·
            refine ⟨31116884251161048521701171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41489179001548064695601561 31116884251161048521701171)
            ·
              refine ⟨46675326376741572782551757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31116884251161048521701171 46675326376741572782551757)
              ·
                refine ⟨17503247391278089793456909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46675326376741572782551757 17503247391278089793456909)
                ·
                  refine ⟨6563717771729283672546341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17503247391278089793456909 6563717771729283672546341)
                  ·
                    refine ⟨1230697082199240688602439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6563717771729283672546341 1230697082199240688602439)
                    ·
                      rfl

theorem cell23_7190322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_7190322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190322 prefixEnd_7190322 := by exact prefixLift 7190322
  have htrace : WordTrace (prefixWord ++ tailWord_7190322) baseStart_7190322 baseEnd_7190322 := by
    simpa [prefixWord, tailWord_7190322, baseEnd_7190322] using wordTrace_append hprefix tailTrace_7190322
  have hstable : (prefixWord ++ tailWord_7190322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190322).length < 2 ^ (prefixWord ++ tailWord_7190322).sum := by decide
  have hdescent : baseEnd_7190322 < baseStart_7190322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190345 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 3]
def baseStart_7190345 : Nat := 118140960795 + 7190345 * 2 ^ 59
def prefixEnd_7190345 : Nat := 4983230072969 + 3 ^ 40 * 7190345 * 2
def baseEnd_7190345 : Nat := 3692103056652775475819711

theorem tailTrace_7190345 : CollatzResearch.WordTrace tailWord_7190345 prefixEnd_7190345 3692103056652775475819711 := by
  unfold tailWord_7190345
  simp only [CollatzResearch.WordTrace]
  refine ⟨262253427135615553003988489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174835618090410368669325659 262253427135615553003988489)
  ·
    refine ⟨196690070351711664752991367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262253427135615553003988489 196690070351711664752991367)
    ·
      refine ⟨295035105527567497129487051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196690070351711664752991367 295035105527567497129487051)
      ·
        refine ⟨442552658291351245694230577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295035105527567497129487051 442552658291351245694230577)
        ·
          refine ⟨331914493718513434270672933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442552658291351245694230577 331914493718513434270672933)
          ·
            refine ⟨62233967572221268925751175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331914493718513434270672933 62233967572221268925751175)
            ·
              refine ⟨93350951358331903388626763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62233967572221268925751175 93350951358331903388626763)
              ·
                refine ⟨140026427037497855082940145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93350951358331903388626763 140026427037497855082940145)
                ·
                  refine ⟨105019820278123391312205109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140026427037497855082940145 105019820278123391312205109)
                  ·
                    refine ⟨9845608151074067935519229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105019820278123391312205109 9845608151074067935519229)
                    ·
                      refine ⟨3692103056652775475819711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9845608151074067935519229 3692103056652775475819711)
                      ·
                        rfl

theorem cell23_7190345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_7190345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190345 prefixEnd_7190345 := by exact prefixLift 7190345
  have htrace : WordTrace (prefixWord ++ tailWord_7190345) baseStart_7190345 baseEnd_7190345 := by
    simpa [prefixWord, tailWord_7190345, baseEnd_7190345] using wordTrace_append hprefix tailTrace_7190345
  have hstable : (prefixWord ++ tailWord_7190345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190345).length < 2 ^ (prefixWord ++ tailWord_7190345).sum := by decide
  have hdescent : baseEnd_7190345 < baseStart_7190345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190349 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_7190349 : Nat := 118140960795 + 7190349 * 2 ^ 59
def prefixEnd_7190349 : Nat := 4983230072969 + 3 ^ 40 * 7190349 * 2
def baseEnd_7190349 : Nat := 3692105110575393460169693

theorem tailTrace_7190349 : CollatzResearch.WordTrace tailWord_7190349 prefixEnd_7190349 3692105110575393460169693 := by
  unfold tailWord_7190349
  simp only [CollatzResearch.WordTrace]
  refine ⟨262253573027601061687134101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174835715351734041124756067 262253573027601061687134101)
  ·
    refine ⟨12293136235668799766584411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 262253573027601061687134101 12293136235668799766584411)
    ·
      refine ⟨18439704353503199649876617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12293136235668799766584411 18439704353503199649876617)
      ·
        refine ⟨13829778265127399737407463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18439704353503199649876617 13829778265127399737407463)
        ·
          refine ⟨20744667397691099606111195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13829778265127399737407463 20744667397691099606111195)
          ·
            refine ⟨31117001096536649409166793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20744667397691099606111195 31117001096536649409166793)
            ·
              refine ⟨23337750822402487056875095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31117001096536649409166793 23337750822402487056875095)
              ·
                refine ⟨35006626233603730585312643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23337750822402487056875095 35006626233603730585312643)
                ·
                  refine ⟨52509939350405595877968965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35006626233603730585312643 52509939350405595877968965)
                  ·
                    refine ⟨9845613628201049227119181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52509939350405595877968965 9845613628201049227119181)
                    ·
                      refine ⟨3692105110575393460169693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9845613628201049227119181 3692105110575393460169693)
                      ·
                        rfl

theorem cell23_7190349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_7190349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190349 prefixEnd_7190349 := by exact prefixLift 7190349
  have htrace : WordTrace (prefixWord ++ tailWord_7190349) baseStart_7190349 baseEnd_7190349 := by
    simpa [prefixWord, tailWord_7190349, baseEnd_7190349] using wordTrace_append hprefix tailTrace_7190349
  have hstable : (prefixWord ++ tailWord_7190349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190349).length < 2 ^ (prefixWord ++ tailWord_7190349).sum := by decide
  have hdescent : baseEnd_7190349 < baseStart_7190349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190356 : List Nat := [2, 4, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_7190356 : Nat := 118140960795 + 7190356 * 2 ^ 59
def prefixEnd_7190356 : Nat := 4983230072969 + 3 ^ 40 * 7190356 * 2
def baseEnd_7190356 : Nat := 1230702901646658310927387

theorem tailTrace_7190356 : CollatzResearch.WordTrace tailWord_7190356 prefixEnd_7190356 1230702901646658310927387 := by
  unfold tailWord_7190356
  simp only [CollatzResearch.WordTrace]
  refine ⟨131126914169287850941319461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174835885559050467921759281 131126914169287850941319461)
  ·
    refine ⟨24586296406741472051497399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131126914169287850941319461 24586296406741472051497399)
    ·
      refine ⟨36879444610112208077246099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24586296406741472051497399 36879444610112208077246099)
      ·
        refine ⟨55319166915168312115869149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36879444610112208077246099 55319166915168312115869149)
        ·
          refine ⟨20744687593188117043450931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55319166915168312115869149 20744687593188117043450931)
          ·
            refine ⟨31117031389782175565176397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20744687593188117043450931 31117031389782175565176397)
            ·
              refine ⟨11668886771168315836941149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31117031389782175565176397 11668886771168315836941149)
              ·
                refine ⟨4375832539188118438852931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11668886771168315836941149 4375832539188118438852931)
                ·
                  refine ⟨6563748808782177658279397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375832539188118438852931 6563748808782177658279397)
                  ·
                    refine ⟨1230702901646658310927387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6563748808782177658279397 1230702901646658310927387)
                    ·
                      rfl

theorem cell23_7190356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_7190356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190356 prefixEnd_7190356 := by exact prefixLift 7190356
  have htrace : WordTrace (prefixWord ++ tailWord_7190356) baseStart_7190356 baseEnd_7190356 := by
    simpa [prefixWord, tailWord_7190356, baseEnd_7190356] using wordTrace_append hprefix tailTrace_7190356
  have hstable : (prefixWord ++ tailWord_7190356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190356).length < 2 ^ (prefixWord ++ tailWord_7190356).sum := by decide
  have hdescent : baseEnd_7190356 < baseStart_7190356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190389 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_7190389 : Nat := 118140960795 + 7190389 * 2 ^ 59
def prefixEnd_7190389 : Nat := 4983230072969 + 3 ^ 40 * 7190389 * 2
def baseEnd_7190389 : Nat := 3692125649801573303669509

theorem tailTrace_7190389 : CollatzResearch.WordTrace tailWord_7190389 prefixEnd_7190389 3692125649801573303669509 := by
  unfold tailWord_7190389
  simp only [CollatzResearch.WordTrace]
  refine ⟨262255031947456148518590221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174836687964970765679060147 262255031947456148518590221)
  ·
    refine ⟨98345636980296055694471333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262255031947456148518590221 98345636980296055694471333)
    ·
      refine ⟨18439806933805510442713375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98345636980296055694471333 18439806933805510442713375)
      ·
        refine ⟨27659710400708265664070063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18439806933805510442713375 27659710400708265664070063)
        ·
          refine ⟨41489565601062398496105095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27659710400708265664070063 41489565601062398496105095)
          ·
            refine ⟨62234348401593597744157643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41489565601062398496105095 62234348401593597744157643)
            ·
              refine ⟨93351522602390396616236465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62234348401593597744157643 93351522602390396616236465)
              ·
                refine ⟨70013641951792797462177349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93351522602390396616236465 70013641951792797462177349)
                ·
                  refine ⟨13127557865961149524158253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70013641951792797462177349 13127557865961149524158253)
                  ·
                    refine ⟨4922834199735431071559345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13127557865961149524158253 4922834199735431071559345)
                    ·
                      refine ⟨3692125649801573303669509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922834199735431071559345 3692125649801573303669509)
                      ·
                        rfl

theorem cell23_7190389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_7190389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190389 prefixEnd_7190389 := by exact prefixLift 7190389
  have htrace : WordTrace (prefixWord ++ tailWord_7190389) baseStart_7190389 baseEnd_7190389 := by
    simpa [prefixWord, tailWord_7190389, baseEnd_7190389] using wordTrace_append hprefix tailTrace_7190389
  have hstable : (prefixWord ++ tailWord_7190389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190389).length < 2 ^ (prefixWord ++ tailWord_7190389).sum := by decide
  have hdescent : baseEnd_7190389 < baseStart_7190389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190395 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 1, 6]
def baseStart_7190395 : Nat := 118140960795 + 7190395 * 2 ^ 59
def prefixEnd_7190395 : Nat := 4983230072969 + 3 ^ 40 * 7190395 * 2
def baseEnd_7190395 : Nat := 1230709576895166760064827

theorem tailTrace_7190395 : CollatzResearch.WordTrace tailWord_7190395 prefixEnd_7190395 1230709576895166760064827 := by
  unfold tailWord_7190395
  simp only [CollatzResearch.WordTrace]
  refine ⟨262255250785434411543308639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174836833856956274362205759 262255250785434411543308639)
  ·
    refine ⟨393382876178151617314962959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262255250785434411543308639 393382876178151617314962959)
    ·
      refine ⟨590074314267227425972444439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393382876178151617314962959 590074314267227425972444439)
      ·
        refine ⟨885111471400841138958666659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590074314267227425972444439 885111471400841138958666659)
        ·
          refine ⟨1327667207101261708437999989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885111471400841138958666659 1327667207101261708437999989)
          ·
            refine ⟨124468800665743285166062499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1327667207101261708437999989 124468800665743285166062499)
            ·
              refine ⟨186703200998614927749093749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124468800665743285166062499 186703200998614927749093749)
              ·
                refine ⟨17503425093620149476477539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186703200998614927749093749 17503425093620149476477539)
                ·
                  refine ⟨26255137640430224214716309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17503425093620149476477539 26255137640430224214716309)
                  ·
                    refine ⟨1230709576895166760064827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26255137640430224214716309 1230709576895166760064827)
                    ·
                      rfl

theorem cell23_7190395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 6].length) (baseStart_7190395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190395 prefixEnd_7190395 := by exact prefixLift 7190395
  have htrace : WordTrace (prefixWord ++ tailWord_7190395) baseStart_7190395 baseEnd_7190395 := by
    simpa [prefixWord, tailWord_7190395, baseEnd_7190395] using wordTrace_append hprefix tailTrace_7190395
  have hstable : (prefixWord ++ tailWord_7190395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190395).length < 2 ^ (prefixWord ++ tailWord_7190395).sum := by decide
  have hdescent : baseEnd_7190395 < baseStart_7190395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190429 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_7190429 : Nat := 118140960795 + 7190429 * 2 ^ 59
def prefixEnd_7190429 : Nat := 4983230072969 + 3 ^ 40 * 7190429 * 2
def baseEnd_7190429 : Nat := 1230715396342584382389775

theorem tailTrace_7190429 : CollatzResearch.WordTrace tailWord_7190429 prefixEnd_7190429 1230715396342584382389775 := by
  unfold tailWord_7190429
  simp only [CollatzResearch.WordTrace]
  refine ⟨262256490867311235350046341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174837660578207490233364227 262256490867311235350046341)
  ·
    refine ⟨49173092037620856628133689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262256490867311235350046341 49173092037620856628133689)
    ·
      refine ⟨36879819028215642471100267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49173092037620856628133689 36879819028215642471100267)
      ·
        refine ⟨55319728542323463706650401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36879819028215642471100267 55319728542323463706650401)
        ·
          refine ⟨41489796406742597779987801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55319728542323463706650401 41489796406742597779987801)
          ·
            refine ⟨31117347305056948334990851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41489796406742597779987801 31117347305056948334990851)
            ·
              refine ⟨46676020957585422502486277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31117347305056948334990851 46676020957585422502486277)
              ·
                refine ⟨8751753929547266719216177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46676020957585422502486277 8751753929547266719216177)
                ·
                  refine ⟨6563815447160450039412133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8751753929547266719216177 6563815447160450039412133)
                  ·
                    refine ⟨1230715396342584382389775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6563815447160450039412133 1230715396342584382389775)
                    ·
                      rfl

theorem cell23_7190429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_7190429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190429 prefixEnd_7190429 := by exact prefixLift 7190429
  have htrace : WordTrace (prefixWord ++ tailWord_7190429) baseStart_7190429 baseEnd_7190429 := by
    simpa [prefixWord, tailWord_7190429, baseEnd_7190429] using wordTrace_append hprefix tailTrace_7190429
  have hstable : (prefixWord ++ tailWord_7190429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190429).length < 2 ^ (prefixWord ++ tailWord_7190429).sum := by decide
  have hdescent : baseEnd_7190429 < baseStart_7190429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190439 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_7190439 : Nat := 118140960795 + 7190439 * 2 ^ 59
def prefixEnd_7190439 : Nat := 4983230072969 + 3 ^ 40 * 7190439 * 2
def baseEnd_7190439 : Nat := 3692151323834298108044279

theorem tailTrace_7190439 : CollatzResearch.WordTrace tailWord_7190439 prefixEnd_7190439 3692151323834298108044279 := by
  unfold tailWord_7190439
  simp only [CollatzResearch.WordTrace]
  refine ⟨262256855597275007057910371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174837903731516671371940247 262256855597275007057910371)
  ·
    refine ⟨393385283395912510586865557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262256855597275007057910371 393385283395912510586865557)
    ·
      refine ⟨18439935159183398933759323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 393385283395912510586865557 18439935159183398933759323)
      ·
        refine ⟨27659902738775098400638985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18439935159183398933759323 27659902738775098400638985)
        ·
          refine ⟨20744927054081323800479239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27659902738775098400638985 20744927054081323800479239)
          ·
            refine ⟨31117390581121985700718859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20744927054081323800479239 31117390581121985700718859)
            ·
              refine ⟨46676085871682978551078289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31117390581121985700718859 46676085871682978551078289)
              ·
                refine ⟨35007064403762233913308717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46676085871682978551078289 35007064403762233913308717)
                ·
                  refine ⟨13127649151410837717490769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35007064403762233913308717 13127649151410837717490769)
                  ·
                    refine ⟨9845736863558128288118077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13127649151410837717490769 9845736863558128288118077)
                    ·
                      refine ⟨3692151323834298108044279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9845736863558128288118077 3692151323834298108044279)
                      ·
                        rfl

theorem cell23_7190439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_7190439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190439 prefixEnd_7190439 := by exact prefixLift 7190439
  have htrace : WordTrace (prefixWord ++ tailWord_7190439) baseStart_7190439 baseEnd_7190439 := by
    simpa [prefixWord, tailWord_7190439, baseEnd_7190439] using wordTrace_append hprefix tailTrace_7190439
  have hstable : (prefixWord ++ tailWord_7190439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190439).length < 2 ^ (prefixWord ++ tailWord_7190439).sum := by decide
  have hdescent : baseEnd_7190439 < baseStart_7190439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190449 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_7190449 : Nat := 118140960795 + 7190449 * 2 ^ 59
def prefixEnd_7190449 : Nat := 4983230072969 + 3 ^ 40 * 7190449 * 2
def baseEnd_7190449 : Nat := 3692156458640843068919233

theorem tailTrace_7190449 : CollatzResearch.WordTrace tailWord_7190449 prefixEnd_7190449 3692156458640843068919233 := by
  unfold tailWord_7190449
  simp only [CollatzResearch.WordTrace]
  refine ⟨262257220327238778765774401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174838146884825852510516267 262257220327238778765774401)
  ·
    refine ⟨196692915245429084074330801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262257220327238778765774401 196692915245429084074330801)
    ·
      refine ⟨147519686434071813055748101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196692915245429084074330801 147519686434071813055748101)
      ·
        refine ⟨27659941206388464947952769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147519686434071813055748101 27659941206388464947952769)
        ·
          refine ⟨20744955904791348710964577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27659941206388464947952769 20744955904791348710964577)
          ·
            refine ⟨15558716928593511533223433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20744955904791348710964577 15558716928593511533223433)
            ·
              refine ⟨11669037696445133649917575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15558716928593511533223433 11669037696445133649917575)
              ·
                refine ⟨17503556544667700474876363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11669037696445133649917575 17503556544667700474876363)
                ·
                  refine ⟨26255334817001550712314545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17503556544667700474876363 26255334817001550712314545)
                  ·
                    refine ⟨19691501112751163034235909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26255334817001550712314545 19691501112751163034235909)
                    ·
                      refine ⟨3692156458640843068919233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19691501112751163034235909 3692156458640843068919233)
                      ·
                        rfl

theorem cell23_7190449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_7190449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190449 prefixEnd_7190449 := by exact prefixLift 7190449
  have htrace : WordTrace (prefixWord ++ tailWord_7190449) baseStart_7190449 baseEnd_7190449 := by
    simpa [prefixWord, tailWord_7190449, baseEnd_7190449] using wordTrace_append hprefix tailTrace_7190449
  have hstable : (prefixWord ++ tailWord_7190449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190449).length < 2 ^ (prefixWord ++ tailWord_7190449).sum := by decide
  have hdescent : baseEnd_7190449 < baseStart_7190449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190455 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 4, 7]
def baseStart_7190455 : Nat := 118140960795 + 7190455 * 2 ^ 59
def prefixEnd_7190455 : Nat := 4983230072969 + 3 ^ 40 * 7190455 * 2
def baseEnd_7190455 : Nat := 1230719846508256681814735

theorem tailTrace_7190455 : CollatzResearch.WordTrace tailWord_7190455 prefixEnd_7190455 1230719846508256681814735 := by
  unfold tailWord_7190455
  simp only [CollatzResearch.WordTrace]
  refine ⟨262257439165217041790492819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174838292776811361193661879 262257439165217041790492819)
  ·
    refine ⟨393386158747825562685739229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262257439165217041790492819 393386158747825562685739229)
    ·
      refine ⟨147519809530434586007152211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393386158747825562685739229 147519809530434586007152211)
      ·
        refine ⟨221279714295651879010728317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147519809530434586007152211 221279714295651879010728317)
        ·
          refine ⟨82979892860869454629023119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221279714295651879010728317 82979892860869454629023119)
          ·
            refine ⟨124469839291304181943534679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82979892860869454629023119 124469839291304181943534679)
            ·
              refine ⟨186704758936956272915302019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124469839291304181943534679 186704758936956272915302019)
              ·
                refine ⟨280057138405434409372953029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186704758936956272915302019 280057138405434409372953029)
                ·
                  refine ⟨52510713451018951757428693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280057138405434409372953029 52510713451018951757428693)
                  ·
                    refine ⟨1230719846508256681814735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52510713451018951757428693 1230719846508256681814735)
                    ·
                      rfl

theorem cell23_7190455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_7190455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190455 prefixEnd_7190455 := by exact prefixLift 7190455
  have htrace : WordTrace (prefixWord ++ tailWord_7190455) baseStart_7190455 baseEnd_7190455 := by
    simpa [prefixWord, tailWord_7190455, baseEnd_7190455] using wordTrace_append hprefix tailTrace_7190455
  have hstable : (prefixWord ++ tailWord_7190455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190455).length < 2 ^ (prefixWord ++ tailWord_7190455).sum := by decide
  have hdescent : baseEnd_7190455 < baseStart_7190455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190503 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_7190503 : Nat := 118140960795 + 7190503 * 2 ^ 59
def prefixEnd_7190503 : Nat := 4983230072969 + 3 ^ 40 * 7190503 * 2
def baseEnd_7190503 : Nat := 3692184186596185857643985

theorem tailTrace_7190503 : CollatzResearch.WordTrace tailWord_7190503 prefixEnd_7190503 3692184186596185857643985 := by
  unfold tailWord_7190503
  simp only [CollatzResearch.WordTrace]
  refine ⟨262259189869043145988240163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174839459912695430658826775 262259189869043145988240163)
  ·
    refine ⟨393388784803564718982360245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262259189869043145988240163 393388784803564718982360245)
    ·
      refine ⟨36880198575334192404596273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 393388784803564718982360245 36880198575334192404596273)
      ·
        refine ⟨27660148931500644303447205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36880198575334192404596273 27660148931500644303447205)
        ·
          refine ⟨5186277924656370806896351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27660148931500644303447205 5186277924656370806896351)
          ·
            refine ⟨7779416886984556210344527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186277924656370806896351 7779416886984556210344527)
            ·
              refine ⟨11669125330476834315516791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779416886984556210344527 11669125330476834315516791)
              ·
                refine ⟨17503687995715251473275187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11669125330476834315516791 17503687995715251473275187)
                ·
                  refine ⟨26255531993572877209912781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17503687995715251473275187 26255531993572877209912781)
                  ·
                    refine ⟨9845824497589828953717293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26255531993572877209912781 9845824497589828953717293)
                    ·
                      refine ⟨3692184186596185857643985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9845824497589828953717293 3692184186596185857643985)
                      ·
                        rfl

theorem cell23_7190503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_7190503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190503 prefixEnd_7190503 := by exact prefixLift 7190503
  have htrace : WordTrace (prefixWord ++ tailWord_7190503) baseStart_7190503 baseEnd_7190503 := by
    simpa [prefixWord, tailWord_7190503, baseEnd_7190503] using wordTrace_append hprefix tailTrace_7190503
  have hstable : (prefixWord ++ tailWord_7190503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190503).length < 2 ^ (prefixWord ++ tailWord_7190503).sum := by decide
  have hdescent : baseEnd_7190503 < baseStart_7190503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190505 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_7190505 : Nat := 118140960795 + 7190505 * 2 ^ 59
def prefixEnd_7190505 : Nat := 4983230072969 + 3 ^ 40 * 7190505 * 2
def baseEnd_7190505 : Nat := 3692185213557494849818975

theorem tailTrace_7190505 : CollatzResearch.WordTrace tailWord_7190505 prefixEnd_7190505 3692185213557494849818975 := by
  unfold tailWord_7190505
  simp only [CollatzResearch.WordTrace]
  refine ⟨262259262815035900329812969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174839508543357266886541979 262259262815035900329812969)
  ·
    refine ⟨196694447111276925247359727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262259262815035900329812969 196694447111276925247359727)
    ·
      refine ⟨295041670666915387871039591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196694447111276925247359727 295041670666915387871039591)
      ·
        refine ⟨442562506000373081806559387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295041670666915387871039591 442562506000373081806559387)
        ·
          refine ⟨663843759000559622709839081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442562506000373081806559387 663843759000559622709839081)
          ·
            refine ⟨497882819250419717032379311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663843759000559622709839081 497882819250419717032379311)
            ·
              refine ⟨746824228875629575548568967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497882819250419717032379311 746824228875629575548568967)
              ·
                refine ⟨1120236343313444363322853451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746824228875629575548568967 1120236343313444363322853451)
                ·
                  refine ⟨1680354514970166544984280177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120236343313444363322853451 1680354514970166544984280177)
                  ·
                    refine ⟨1260265886227624908738210133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1680354514970166544984280177 1260265886227624908738210133)
                    ·
                      refine ⟨3692185213557494849818975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1260265886227624908738210133 3692185213557494849818975)
                      ·
                        rfl

theorem cell23_7190505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_7190505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190505 prefixEnd_7190505 := by exact prefixLift 7190505
  have htrace : WordTrace (prefixWord ++ tailWord_7190505) baseStart_7190505 baseEnd_7190505 := by
    simpa [prefixWord, tailWord_7190505, baseEnd_7190505] using wordTrace_append hprefix tailTrace_7190505
  have hstable : (prefixWord ++ tailWord_7190505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190505).length < 2 ^ (prefixWord ++ tailWord_7190505).sum := by decide
  have hdescent : baseEnd_7190505 < baseStart_7190505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190512 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 3]
def baseStart_7190512 : Nat := 118140960795 + 7190512 * 2 ^ 59
def prefixEnd_7190512 : Nat := 4983230072969 + 3 ^ 40 * 7190512 * 2
def baseEnd_7190512 : Nat := 3692188807922076322431443

theorem tailTrace_7190512 : CollatzResearch.WordTrace tailWord_7190512 prefixEnd_7190512 3692188807922076322431443 := by
  unfold tailWord_7190512
  simp only [CollatzResearch.WordTrace]
  refine ⟨131129759063005270262658895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174839678750673693683545193 131129759063005270262658895)
  ·
    refine ⟨196694638594507905393988343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131129759063005270262658895 196694638594507905393988343)
    ·
      refine ⟨295041957891761858090982515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196694638594507905393988343 295041957891761858090982515)
      ·
        refine ⟨442562936837642787136473773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295041957891761858090982515 442562936837642787136473773)
        ·
          refine ⟨165961101314116045176177665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442562936837642787136473773 165961101314116045176177665)
          ·
            refine ⟨124470825985587033882133249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165961101314116045176177665 124470825985587033882133249)
            ·
              refine ⟨93353119489190275411599937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124470825985587033882133249 93353119489190275411599937)
              ·
                refine ⟨70014839616892706558699953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93353119489190275411599937 70014839616892706558699953)
                ·
                  refine ⟨52511129712669529919024965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70014839616892706558699953 52511129712669529919024965)
                  ·
                    refine ⟨9845836821125536859817181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52511129712669529919024965 9845836821125536859817181)
                    ·
                      refine ⟨3692188807922076322431443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9845836821125536859817181 3692188807922076322431443)
                      ·
                        rfl

theorem cell23_7190512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_7190512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190512 prefixEnd_7190512 := by exact prefixLift 7190512
  have htrace : WordTrace (prefixWord ++ tailWord_7190512) baseStart_7190512 baseEnd_7190512 := by
    simpa [prefixWord, tailWord_7190512, baseEnd_7190512] using wordTrace_append hprefix tailTrace_7190512
  have hstable : (prefixWord ++ tailWord_7190512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190512).length < 2 ^ (prefixWord ++ tailWord_7190512).sum := by decide
  have hdescent : baseEnd_7190512 < baseStart_7190512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190513 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 1, 3, 2]
def baseStart_7190513 : Nat := 118140960795 + 7190513 * 2 ^ 59
def prefixEnd_7190513 : Nat := 4983230072969 + 3 ^ 40 * 7190513 * 2
def baseEnd_7190513 : Nat := 3692189321402730818518939

theorem tailTrace_7190513 : CollatzResearch.WordTrace tailWord_7190513 prefixEnd_7190513 3692189321402730818518939 := by
  unfold tailWord_7190513
  simp only [CollatzResearch.WordTrace]
  refine ⟨262259554599006917696104193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174839703066004611797402795 262259554599006917696104193)
  ·
    refine ⟨196694665949255188272078145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262259554599006917696104193 196694665949255188272078145)
    ·
      refine ⟨147520999461941391204058609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196694665949255188272078145 147520999461941391204058609)
      ·
        refine ⟨110640749596456043403043957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147520999461941391204058609 110640749596456043403043957)
        ·
          refine ⟨10372570274667754069035371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110640749596456043403043957 10372570274667754069035371)
          ·
            refine ⟨15558855412001631103553057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10372570274667754069035371 15558855412001631103553057)
            ·
              refine ⟨11669141559001223327664793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15558855412001631103553057 11669141559001223327664793)
              ·
                refine ⟨8751856169250917495748595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11669141559001223327664793 8751856169250917495748595)
                ·
                  refine ⟨13127784253876376243622893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8751856169250917495748595 13127784253876376243622893)
                  ·
                    refine ⟨4922919095203641091358585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13127784253876376243622893 4922919095203641091358585)
                    ·
                      refine ⟨3692189321402730818518939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922919095203641091358585 3692189321402730818518939)
                      ·
                        rfl

theorem cell23_7190513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_7190513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190513 prefixEnd_7190513 := by exact prefixLift 7190513
  have htrace : WordTrace (prefixWord ++ tailWord_7190513) baseStart_7190513 baseEnd_7190513 := by
    simpa [prefixWord, tailWord_7190513, baseEnd_7190513] using wordTrace_append hprefix tailTrace_7190513
  have hstable : (prefixWord ++ tailWord_7190513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190513).length < 2 ^ (prefixWord ++ tailWord_7190513).sum := by decide
  have hdescent : baseEnd_7190513 < baseStart_7190513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190542 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_7190542 : Nat := 118140960795 + 7190542 * 2 ^ 59
def prefixEnd_7190542 : Nat := 4983230072969 + 3 ^ 40 * 7190542 * 2
def baseEnd_7190542 : Nat := 3692204212341711205056305

theorem tailTrace_7190542 : CollatzResearch.WordTrace tailWord_7190542 prefixEnd_7190542 3692204212341711205056305 := by
  unfold tailWord_7190542
  simp only [CollatzResearch.WordTrace]
  refine ⟨32782576539487731956113735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174840408210601237099273253 32782576539487731956113735)
  ·
    refine ⟨49173864809231597934170603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32782576539487731956113735 49173864809231597934170603)
    ·
      refine ⟨73760797213847396901255905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49173864809231597934170603 73760797213847396901255905)
      ·
        refine ⟨55320597910385547675941929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73760797213847396901255905 55320597910385547675941929)
        ·
          refine ⟨41490448432789160756956447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55320597910385547675941929 41490448432789160756956447)
          ·
            refine ⟨62235672649183741135434671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41490448432789160756956447 62235672649183741135434671)
            ·
              refine ⟨93353508973775611703152007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62235672649183741135434671 93353508973775611703152007)
              ·
                refine ⟨140030263460663417554728011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93353508973775611703152007 140030263460663417554728011)
                ·
                  refine ⟨210045395190995126332092017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140030263460663417554728011 210045395190995126332092017)
                  ·
                    refine ⟨157534046393246344749069013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210045395190995126332092017 157534046393246344749069013)
                    ·
                      refine ⟨3692204212341711205056305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157534046393246344749069013 3692204212341711205056305)
                      ·
                        rfl

theorem cell23_7190542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_7190542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190542 prefixEnd_7190542 := by exact prefixLift 7190542
  have htrace : WordTrace (prefixWord ++ tailWord_7190542) baseStart_7190542 baseEnd_7190542 := by
    simpa [prefixWord, tailWord_7190542, baseEnd_7190542] using wordTrace_append hprefix tailTrace_7190542
  have hstable : (prefixWord ++ tailWord_7190542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190542).length < 2 ^ (prefixWord ++ tailWord_7190542).sum := by decide
  have hdescent : baseEnd_7190542 < baseStart_7190542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190599 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_7190599 : Nat := 118140960795 + 7190599 * 2 ^ 59
def prefixEnd_7190599 : Nat := 4983230072969 + 3 ^ 40 * 7190599 * 2
def baseEnd_7190599 : Nat := 3692233480739017482043543

theorem tailTrace_7190599 : CollatzResearch.WordTrace tailWord_7190599 prefixEnd_7190599 3692233480739017482043543 := by
  unfold tailWord_7190599
  simp only [CollatzResearch.WordTrace]
  refine ⟨262262691276695354383734851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174841794184463569589156567 262262691276695354383734851)
  ·
    refine ⟨393394036915043031575602277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262262691276695354383734851 393394036915043031575602277)
    ·
      refine ⟨73761381921570568420425427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393394036915043031575602277 73761381921570568420425427)
      ·
        refine ⟨110642072882355852630638141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73761381921570568420425427 110642072882355852630638141)
        ·
          refine ⟨41490777330883444736489303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110642072882355852630638141 41490777330883444736489303)
          ·
            refine ⟨62236165996325167104733955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41490777330883444736489303 62236165996325167104733955)
            ·
              refine ⟨93354248994487750657100933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62236165996325167104733955 93354248994487750657100933)
              ·
                refine ⟨17503921686466453248206425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93354248994487750657100933 17503921686466453248206425)
                ·
                  refine ⟨13127941264849839936154819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17503921686466453248206425 13127941264849839936154819)
                  ·
                    refine ⟨19691911897274759904232229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13127941264849839936154819 19691911897274759904232229)
                    ·
                      refine ⟨3692233480739017482043543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19691911897274759904232229 3692233480739017482043543)
                      ·
                        rfl

theorem cell23_7190599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_7190599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190599 prefixEnd_7190599 := by exact prefixLift 7190599
  have htrace : WordTrace (prefixWord ++ tailWord_7190599) baseStart_7190599 baseEnd_7190599 := by
    simpa [prefixWord, tailWord_7190599, baseEnd_7190599] using wordTrace_append hprefix tailTrace_7190599
  have hstable : (prefixWord ++ tailWord_7190599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190599).length < 2 ^ (prefixWord ++ tailWord_7190599).sum := by decide
  have hdescent : baseEnd_7190599 < baseStart_7190599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190602 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_7190602 : Nat := 118140960795 + 7190602 * 2 ^ 59
def prefixEnd_7190602 : Nat := 4983230072969 + 3 ^ 40 * 7190602 * 2
def baseEnd_7190602 : Nat := 3692235021180980970306029

theorem tailTrace_7190602 : CollatzResearch.WordTrace tailWord_7190602 prefixEnd_7190602 3692235021180980970306029 := by
  unfold tailWord_7190602
  simp only [CollatzResearch.WordTrace]
  refine ⟨65565700173921121474023515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174841867130456323930729373 65565700173921121474023515)
  ·
    refine ⟨98348550260881682211035273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65565700173921121474023515 98348550260881682211035273)
    ·
      refine ⟨73761412695661261658276455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98348550260881682211035273 73761412695661261658276455)
      ·
        refine ⟨110642119043491892487414683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73761412695661261658276455 110642119043491892487414683)
        ·
          refine ⟨165963178565237838731122025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110642119043491892487414683 165963178565237838731122025)
          ·
            refine ⟨124472383923928379048341519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165963178565237838731122025 124472383923928379048341519)
            ·
              refine ⟨186708575885892568572512279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124472383923928379048341519 186708575885892568572512279)
              ·
                refine ⟨280062863828838852858768419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186708575885892568572512279 280062863828838852858768419)
                ·
                  refine ⟨420094295743258279288152629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280062863828838852858768419 420094295743258279288152629)
                  ·
                    refine ⟨39383840225930463683264309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 420094295743258279288152629 39383840225930463683264309)
                    ·
                      refine ⟨3692235021180980970306029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39383840225930463683264309 3692235021180980970306029)
                      ·
                        rfl

theorem cell23_7190602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_7190602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190602 prefixEnd_7190602 := by exact prefixLift 7190602
  have htrace : WordTrace (prefixWord ++ tailWord_7190602) baseStart_7190602 baseEnd_7190602 := by
    simpa [prefixWord, tailWord_7190602, baseEnd_7190602] using wordTrace_append hprefix tailTrace_7190602
  have hstable : (prefixWord ++ tailWord_7190602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190602).length < 2 ^ (prefixWord ++ tailWord_7190602).sum := by decide
  have hdescent : baseEnd_7190602 < baseStart_7190602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190609 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 3, 4]
def baseStart_7190609 : Nat := 118140960795 + 7190609 * 2 ^ 59
def prefixEnd_7190609 : Nat := 4983230072969 + 3 ^ 40 * 7190609 * 2
def baseEnd_7190609 : Nat := 1230746205181854147639499

theorem tailTrace_7190609 : CollatzResearch.WordTrace tailWord_7190609 prefixEnd_7190609 1230746205181854147639499 := by
  unfold tailWord_7190609
  simp only [CollatzResearch.WordTrace]
  refine ⟨262263056006659126091598881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174842037337772750727732587 262263056006659126091598881)
  ·
    refine ⟨196697292004994344568699161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262263056006659126091598881 196697292004994344568699161)
    ·
      refine ⟨147522969003745758426524371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196697292004994344568699161 147522969003745758426524371)
      ·
        refine ⟨221284453505618637639786557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147522969003745758426524371 221284453505618637639786557)
        ·
          refine ⟨82981670064606989114919959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221284453505618637639786557 82981670064606989114919959)
          ·
            refine ⟨124472505096910483672379939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82981670064606989114919959 124472505096910483672379939)
            ·
              refine ⟨186708757645365725508569909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124472505096910483672379939 186708757645365725508569909)
              ·
                refine ⟨17503946029253036766428429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186708757645365725508569909 17503946029253036766428429)
                ·
                  refine ⟨6563979760969888787410661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17503946029253036766428429 6563979760969888787410661)
                  ·
                    refine ⟨1230746205181854147639499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6563979760969888787410661 1230746205181854147639499)
                    ·
                      rfl

theorem cell23_7190609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_7190609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190609 prefixEnd_7190609 := by exact prefixLift 7190609
  have htrace : WordTrace (prefixWord ++ tailWord_7190609) baseStart_7190609 baseEnd_7190609 := by
    simpa [prefixWord, tailWord_7190609, baseEnd_7190609] using wordTrace_append hprefix tailTrace_7190609
  have hstable : (prefixWord ++ tailWord_7190609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190609).length < 2 ^ (prefixWord ++ tailWord_7190609).sum := by decide
  have hdescent : baseEnd_7190609 < baseStart_7190609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190616 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 2, 4, 2]
def baseStart_7190616 : Nat := 118140960795 + 7190616 * 2 ^ 59
def prefixEnd_7190616 : Nat := 4983230072969 + 3 ^ 40 * 7190616 * 2
def baseEnd_7190616 : Nat := 3692242209910143915530965

theorem tailTrace_7190616 : CollatzResearch.WordTrace tailWord_7190616 prefixEnd_7190616 3692242209910143915530965 := by
  unfold tailWord_7190616
  simp only [CollatzResearch.WordTrace]
  refine ⟨131131655658816883143551851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174842207545089177524735801 131131655658816883143551851)
  ·
    refine ⟨196697483488225324715327777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131131655658816883143551851 196697483488225324715327777)
    ·
      refine ⟨147523112616168993536495833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196697483488225324715327777 147523112616168993536495833)
      ·
        refine ⟨110642334462126745152371875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147523112616168993536495833 110642334462126745152371875)
        ·
          refine ⟨165963501693190117728557813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110642334462126745152371875 165963501693190117728557813)
          ·
            refine ⟨15559078283736573537052295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165963501693190117728557813 15559078283736573537052295)
            ·
              refine ⟨23338617425604860305578443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15559078283736573537052295 23338617425604860305578443)
              ·
                refine ⟨35007926138407290458367665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23338617425604860305578443 35007926138407290458367665)
                ·
                  refine ⟨26255944603805467843775749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35007926138407290458367665 26255944603805467843775749)
                  ·
                    refine ⟨4922989613213525220707953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26255944603805467843775749 4922989613213525220707953)
                    ·
                      refine ⟨3692242209910143915530965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4922989613213525220707953 3692242209910143915530965)
                      ·
                        rfl

theorem cell23_7190616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_7190616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190616 prefixEnd_7190616 := by exact prefixLift 7190616
  have htrace : WordTrace (prefixWord ++ tailWord_7190616) baseStart_7190616 baseEnd_7190616 := by
    simpa [prefixWord, tailWord_7190616, baseEnd_7190616] using wordTrace_append hprefix tailTrace_7190616
  have hstable : (prefixWord ++ tailWord_7190616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190616).length < 2 ^ (prefixWord ++ tailWord_7190616).sum := by decide
  have hdescent : baseEnd_7190616 < baseStart_7190616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190636 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_7190636 : Nat := 118140960795 + 7190636 * 2 ^ 59
def prefixEnd_7190636 : Nat := 4983230072969 + 3 ^ 40 * 7190636 * 2
def baseEnd_7190636 : Nat := 3692252479523233837280873

theorem tailTrace_7190636 : CollatzResearch.WordTrace tailWord_7190636 prefixEnd_7190636 3692252479523233837280873 := by
  unfold tailWord_7190636
  simp only [CollatzResearch.WordTrace]
  refine ⟨131132020388780654851415881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174842693851707539801887841 131132020388780654851415881)
  ·
    refine ⟨98349015291585491138561911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131132020388780654851415881 98349015291585491138561911)
    ·
      refine ⟨147523522937378236707842867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98349015291585491138561911 147523522937378236707842867)
      ·
        refine ⟨221285284406067355061764301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147523522937378236707842867 221285284406067355061764301)
        ·
          refine ⟨82981981652275258148161613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221285284406067355061764301 82981981652275258148161613)
          ·
            refine ⟨31118243119603221805560605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82981981652275258148161613 31118243119603221805560605)
            ·
              refine ⟨11669341169851208177085227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31118243119603221805560605 11669341169851208177085227)
              ·
                refine ⟨17504011754776812265627841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11669341169851208177085227 17504011754776812265627841)
                ·
                  refine ⟨13128008816082609199220881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17504011754776812265627841 13128008816082609199220881)
                  ·
                    refine ⟨9846006612061956899415661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13128008816082609199220881 9846006612061956899415661)
                    ·
                      refine ⟨3692252479523233837280873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9846006612061956899415661 3692252479523233837280873)
                      ·
                        rfl

theorem cell23_7190636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_7190636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190636 prefixEnd_7190636 := by exact prefixLift 7190636
  have htrace : WordTrace (prefixWord ++ tailWord_7190636) baseStart_7190636 baseEnd_7190636 := by
    simpa [prefixWord, tailWord_7190636, baseEnd_7190636] using wordTrace_append hprefix tailTrace_7190636
  have hstable : (prefixWord ++ tailWord_7190636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190636).length < 2 ^ (prefixWord ++ tailWord_7190636).sum := by decide
  have hdescent : baseEnd_7190636 < baseStart_7190636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190706 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_7190706 : Nat := 118140960795 + 7190706 * 2 ^ 59
def prefixEnd_7190706 : Nat := 4983230072969 + 3 ^ 40 * 7190706 * 2
def baseEnd_7190706 : Nat := 3692288423169048563405551

theorem tailTrace_7190706 : CollatzResearch.WordTrace tailWord_7190706 prefixEnd_7190706 3692288423169048563405551 := by
  unfold tailWord_7190706
  simp only [CollatzResearch.WordTrace]
  refine ⟨65566648471826927914469993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174844395924871807771919981 65566648471826927914469993)
  ·
    refine ⟨49174986353870195935852495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65566648471826927914469993 49174986353870195935852495)
    ·
      refine ⟨73762479530805293903778743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49174986353870195935852495 73762479530805293903778743)
      ·
        refine ⟨110643719296207940855668115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73762479530805293903778743 110643719296207940855668115)
        ·
          refine ⟨165965578944311911283502173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110643719296207940855668115 165965578944311911283502173)
          ·
            refine ⟨62237092104116966731313315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165965578944311911283502173 62237092104116966731313315)
            ·
              refine ⟨93355638156175450096969973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62237092104116966731313315 93355638156175450096969973)
              ·
                refine ⟨8752091077141448446590935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93355638156175450096969973 8752091077141448446590935)
                ·
                  refine ⟨13128136615712172669886403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8752091077141448446590935 13128136615712172669886403)
                  ·
                    refine ⟨19692204923568259004829605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13128136615712172669886403 19692204923568259004829605)
                    ·
                      refine ⟨3692288423169048563405551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19692204923568259004829605 3692288423169048563405551)
                      ·
                        rfl

theorem cell23_7190706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_7190706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190706 prefixEnd_7190706 := by exact prefixLift 7190706
  have htrace : WordTrace (prefixWord ++ tailWord_7190706) baseStart_7190706 baseEnd_7190706 := by
    simpa [prefixWord, tailWord_7190706, baseEnd_7190706] using wordTrace_append hprefix tailTrace_7190706
  have hstable : (prefixWord ++ tailWord_7190706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190706).length < 2 ^ (prefixWord ++ tailWord_7190706).sum := by decide
  have hdescent : baseEnd_7190706 < baseStart_7190706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190754 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7190754 : Nat := 118140960795 + 7190754 * 2 ^ 59
def prefixEnd_7190754 : Nat := 4983230072969 + 3 ^ 40 * 7190754 * 2
def baseEnd_7190754 : Nat := 1230771023413488125201777

theorem tailTrace_7190754 : CollatzResearch.WordTrace tailWord_7190754 prefixEnd_7190754 1230771023413488125201777 := by
  unfold tailWord_7190754
  simp only [CollatzResearch.WordTrace]
  refine ⟨65567086147783453963906829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174845563060755877237084877 65567086147783453963906829)
  ·
    refine ⟨24587657305418795236465061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65567086147783453963906829 24587657305418795236465061)
    ·
      refine ⟨4610185744766024106837199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24587657305418795236465061 4610185744766024106837199)
      ·
        refine ⟨6915278617149036160255799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610185744766024106837199 6915278617149036160255799)
        ·
          refine ⟨10372917925723554240383699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915278617149036160255799 10372917925723554240383699)
          ·
            refine ⟨15559376888585331360575549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10372917925723554240383699 15559376888585331360575549)
            ·
              refine ⟨5834766333219499260215831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15559376888585331360575549 5834766333219499260215831)
              ·
                refine ⟨8752149499829248890323747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5834766333219499260215831 8752149499829248890323747)
                ·
                  refine ⟨13128224249743873335485621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8752149499829248890323747 13128224249743873335485621)
                  ·
                    refine ⟨1230771023413488125201777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13128224249743873335485621 1230771023413488125201777)
                    ·
                      rfl

theorem cell23_7190754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7190754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190754 prefixEnd_7190754 := by exact prefixLift 7190754
  have htrace : WordTrace (prefixWord ++ tailWord_7190754) baseStart_7190754 baseEnd_7190754 := by
    simpa [prefixWord, tailWord_7190754, baseEnd_7190754] using wordTrace_append hprefix tailTrace_7190754
  have hstable : (prefixWord ++ tailWord_7190754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190754).length < 2 ^ (prefixWord ++ tailWord_7190754).sum := by decide
  have hdescent : baseEnd_7190754 < baseStart_7190754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190760 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_7190760 : Nat := 118140960795 + 7190760 * 2 ^ 59
def prefixEnd_7190760 : Nat := 4983230072969 + 3 ^ 40 * 7190760 * 2
def baseEnd_7190760 : Nat := 3692316151124391352130303

theorem tailTrace_7190760 : CollatzResearch.WordTrace tailWord_7190760 prefixEnd_7190760 3692316151124391352130303 := by
  unfold tailWord_7190760
  simp only [CollatzResearch.WordTrace]
  refine ⟨131134281714556039440172867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174845708952741385920230489 131134281714556039440172867)
  ·
    refine ⟨196701422571834059160259301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131134281714556039440172867 196701422571834059160259301)
    ·
      refine ⟨36881516732218886092548619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196701422571834059160259301 36881516732218886092548619)
      ·
        refine ⟨55322275098328329138822929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36881516732218886092548619 55322275098328329138822929)
        ·
          refine ⟨41491706323746246854117197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55322275098328329138822929 41491706323746246854117197)
          ·
            refine ⟨15559389871404842570293949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41491706323746246854117197 15559389871404842570293949)
            ·
              refine ⟨5834771201776815963860231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15559389871404842570293949 5834771201776815963860231)
              ·
                refine ⟨8752156802665223945790347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5834771201776815963860231 8752156802665223945790347)
                ·
                  refine ⟨13128235203997835918685521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8752156802665223945790347 13128235203997835918685521)
                  ·
                    refine ⟨9846176402998376939014141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13128235203997835918685521 9846176402998376939014141)
                    ·
                      refine ⟨3692316151124391352130303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9846176402998376939014141 3692316151124391352130303)
                      ·
                        rfl

theorem cell23_7190760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_7190760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190760 prefixEnd_7190760 := by exact prefixLift 7190760
  have htrace : WordTrace (prefixWord ++ tailWord_7190760) baseStart_7190760 baseEnd_7190760 := by
    simpa [prefixWord, tailWord_7190760, baseEnd_7190760] using wordTrace_append hprefix tailTrace_7190760
  have hstable : (prefixWord ++ tailWord_7190760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190760).length < 2 ^ (prefixWord ++ tailWord_7190760).sum := by decide
  have hdescent : baseEnd_7190760 < baseStart_7190760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190769 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_7190769 : Nat := 118140960795 + 7190769 * 2 ^ 59
def prefixEnd_7190769 : Nat := 4983230072969 + 3 ^ 40 * 7190769 * 2
def baseEnd_7190769 : Nat := 3692320772450281816917761

theorem tailTrace_7190769 : CollatzResearch.WordTrace tailWord_7190769 prefixEnd_7190769 3692320772450281816917761 := by
  unfold tailWord_7190769
  simp only [CollatzResearch.WordTrace]
  refine ⟨262268891686079473417423361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174845927790719648944948907 262268891686079473417423361)
  ·
    refine ⟨196701668764559605063067521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262268891686079473417423361 196701668764559605063067521)
    ·
      refine ⟨147526251573419703797300641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196701668764559605063067521 147526251573419703797300641)
      ·
        refine ⟨110644688680064777847975481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147526251573419703797300641 110644688680064777847975481)
        ·
          refine ⟨82983516510048583385981611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110644688680064777847975481 82983516510048583385981611)
          ·
            refine ⟨124475274765072875078972417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82983516510048583385981611 124475274765072875078972417)
            ·
              refine ⟨93356456073804656309229313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124475274765072875078972417 93356456073804656309229313)
              ·
                refine ⟨70017342055353492231921985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93356456073804656309229313 70017342055353492231921985)
                ·
                  refine ⟨52513006541515119173941489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70017342055353492231921985 52513006541515119173941489)
                  ·
                    refine ⟨39384754906136339380456117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52513006541515119173941489 39384754906136339380456117)
                    ·
                      refine ⟨3692320772450281816917761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39384754906136339380456117 3692320772450281816917761)
                      ·
                        rfl

theorem cell23_7190769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_7190769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190769 prefixEnd_7190769 := by exact prefixLift 7190769
  have htrace : WordTrace (prefixWord ++ tailWord_7190769) baseStart_7190769 baseEnd_7190769 := by
    simpa [prefixWord, tailWord_7190769, baseEnd_7190769] using wordTrace_append hprefix tailTrace_7190769
  have hstable : (prefixWord ++ tailWord_7190769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190769).length < 2 ^ (prefixWord ++ tailWord_7190769).sum := by decide
  have hdescent : baseEnd_7190769 < baseStart_7190769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190774 : List Nat := [5, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_7190774 : Nat := 118140960795 + 7190774 * 2 ^ 59
def prefixEnd_7190774 : Nat := 4983230072969 + 3 ^ 40 * 7190774 * 2
def baseEnd_7190774 : Nat := 3692323339853554297355239

theorem tailTrace_7190774 : CollatzResearch.WordTrace tailWord_7190774 prefixEnd_7190774 3692323339853554297355239 := by
  unfold tailWord_7190774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16391817128191334954459711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174846049367374239514236917 16391817128191334954459711)
  ·
    refine ⟨24587725692287002431689567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16391817128191334954459711 24587725692287002431689567)
    ·
      refine ⟨36881588538430503647534351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24587725692287002431689567 36881588538430503647534351)
      ·
        refine ⟨55322382807645755471301527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36881588538430503647534351 55322382807645755471301527)
        ·
          refine ⟨82983574211468633206952291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55322382807645755471301527 82983574211468633206952291)
          ·
            refine ⟨124475361317202949810428437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82983574211468633206952291 124475361317202949810428437)
            ·
              refine ⟨5834782561743888272363833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124475361317202949810428437 5834782561743888272363833)
              ·
                refine ⟨4376086921307916204272875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834782561743888272363833 4376086921307916204272875)
                ·
                  refine ⟨6564130381961874306409313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376086921307916204272875 6564130381961874306409313)
                  ·
                    refine ⟨4923097786471405729806985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6564130381961874306409313 4923097786471405729806985)
                    ·
                      refine ⟨3692323339853554297355239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923097786471405729806985 3692323339853554297355239)
                      ·
                        rfl

theorem cell23_7190774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_7190774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190774 prefixEnd_7190774 := by exact prefixLift 7190774
  have htrace : WordTrace (prefixWord ++ tailWord_7190774) baseStart_7190774 baseEnd_7190774 := by
    simpa [prefixWord, tailWord_7190774, baseEnd_7190774] using wordTrace_append hprefix tailTrace_7190774
  have hstable : (prefixWord ++ tailWord_7190774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190774).length < 2 ^ (prefixWord ++ tailWord_7190774).sum := by decide
  have hdescent : baseEnd_7190774 < baseStart_7190774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190799 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_7190799 : Nat := 118140960795 + 7190799 * 2 ^ 59
def prefixEnd_7190799 : Nat := 4983230072969 + 3 ^ 40 * 7190799 * 2
def baseEnd_7190799 : Nat := 3692336176869916699542623

theorem tailTrace_7190799 : CollatzResearch.WordTrace tailWord_7190799 prefixEnd_7190799 3692336176869916699542623 := by
  unfold tailWord_7190799
  simp only [CollatzResearch.WordTrace]
  refine ⟨262269985875970788541015451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174846657250647192360676967 262269985875970788541015451)
  ·
    refine ⟨393404978813956182811523177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262269985875970788541015451 393404978813956182811523177)
    ·
      refine ⟨295053734110467137108642383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393404978813956182811523177 295053734110467137108642383)
      ·
        refine ⟨442580601165700705662963575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295053734110467137108642383 442580601165700705662963575)
        ·
          refine ⟨663870901748551058494445363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442580601165700705662963575 663870901748551058494445363)
          ·
            refine ⟨995806352622826587741668045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663870901748551058494445363 995806352622826587741668045)
            ·
              refine ⟨373427382233559970403125517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 995806352622826587741668045 373427382233559970403125517)
              ·
                refine ⟨140035268337584988901172069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373427382233559970403125517 140035268337584988901172069)
                ·
                  refine ⟨26256612813297185418969763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140035268337584988901172069 26256612813297185418969763)
                  ·
                    refine ⟨39384919219945778128454645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26256612813297185418969763 39384919219945778128454645)
                    ·
                      refine ⟨3692336176869916699542623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39384919219945778128454645 3692336176869916699542623)
                      ·
                        rfl

theorem cell23_7190799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_7190799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190799 prefixEnd_7190799 := by exact prefixLift 7190799
  have htrace : WordTrace (prefixWord ++ tailWord_7190799) baseStart_7190799 baseEnd_7190799 := by
    simpa [prefixWord, tailWord_7190799, baseEnd_7190799] using wordTrace_append hprefix tailTrace_7190799
  have hstable : (prefixWord ++ tailWord_7190799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190799).length < 2 ^ (prefixWord ++ tailWord_7190799).sum := by decide
  have hdescent : baseEnd_7190799 < baseStart_7190799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190819 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 9]
def baseStart_7190819 : Nat := 118140960795 + 7190819 * 2 ^ 59
def prefixEnd_7190819 : Nat := 4983230072969 + 3 ^ 40 * 7190819 * 2
def baseEnd_7190819 : Nat := 410260716275889624588059

theorem tailTrace_7190819 : CollatzResearch.WordTrace tailWord_7190819 prefixEnd_7190819 410260716275889624588059 := by
  unfold tailWord_7190819
  simp only [CollatzResearch.WordTrace]
  refine ⟨262270715335898331956743511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174847143557265554637829007 262270715335898331956743511)
  ·
    refine ⟨393406073003847497935115267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262270715335898331956743511 393406073003847497935115267)
    ·
      refine ⟨590109109505771246902672901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393406073003847497935115267 590109109505771246902672901)
      ·
        refine ⟨110645458032332108794251169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 590109109505771246902672901 110645458032332108794251169)
        ·
          refine ⟨82984093524249081595688377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110645458032332108794251169 82984093524249081595688377)
          ·
            refine ⟨62238070143186811196766283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82984093524249081595688377 62238070143186811196766283)
            ·
              refine ⟨93357105214780216795149425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62238070143186811196766283 93357105214780216795149425)
              ·
                refine ⟨70017828911085162596362069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93357105214780216795149425 70017828911085162596362069)
                ·
                  refine ⟨410260716275889624588059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70017828911085162596362069 410260716275889624588059)
                  ·
                    rfl

theorem cell23_7190819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 9].length) (baseStart_7190819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190819 prefixEnd_7190819 := by exact prefixLift 7190819
  have htrace : WordTrace (prefixWord ++ tailWord_7190819) baseStart_7190819 baseEnd_7190819 := by
    simpa [prefixWord, tailWord_7190819, baseEnd_7190819] using wordTrace_append hprefix tailTrace_7190819
  have hstable : (prefixWord ++ tailWord_7190819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190819).length < 2 ^ (prefixWord ++ tailWord_7190819).sum := by decide
  have hdescent : baseEnd_7190819 < baseStart_7190819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190824 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_7190824 : Nat := 118140960795 + 7190824 * 2 ^ 59
def prefixEnd_7190824 : Nat := 4983230072969 + 3 ^ 40 * 7190824 * 2
def baseEnd_7190824 : Nat := 3692349013886279101730009

theorem tailTrace_7190824 : CollatzResearch.WordTrace tailWord_7190824 prefixEnd_7190824 3692349013886279101730009 := by
  unfold tailWord_7190824
  simp only [CollatzResearch.WordTrace]
  refine ⟨131135448850440108905337763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174847265133920145207117017 131135448850440108905337763)
  ·
    refine ⟨196703173275660163358006645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131135448850440108905337763 196703173275660163358006645)
    ·
      refine ⟨18440922494593140314813123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196703173275660163358006645 18440922494593140314813123)
      ·
        refine ⟨27661383741889710472219685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18440922494593140314813123 27661383741889710472219685)
        ·
          refine ⟨5186509451604320713541191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27661383741889710472219685 5186509451604320713541191)
          ·
            refine ⟨7779764177406481070311787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186509451604320713541191 7779764177406481070311787)
            ·
              refine ⟨11669646266109721605467681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779764177406481070311787 11669646266109721605467681)
              ·
                refine ⟨8752234699582291204100761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11669646266109721605467681 8752234699582291204100761)
                ·
                  refine ⟨6564176024686718403075571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8752234699582291204100761 6564176024686718403075571)
                  ·
                    refine ⟨9846264037030077604613357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564176024686718403075571 9846264037030077604613357)
                    ·
                      refine ⟨3692349013886279101730009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9846264037030077604613357 3692349013886279101730009)
                      ·
                        rfl

theorem cell23_7190824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_7190824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190824 prefixEnd_7190824 := by exact prefixLift 7190824
  have htrace : WordTrace (prefixWord ++ tailWord_7190824) baseStart_7190824 baseEnd_7190824 := by
    simpa [prefixWord, tailWord_7190824, baseEnd_7190824] using wordTrace_append hprefix tailTrace_7190824
  have hstable : (prefixWord ++ tailWord_7190824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190824).length < 2 ^ (prefixWord ++ tailWord_7190824).sum := by decide
  have hdescent : baseEnd_7190824 < baseStart_7190824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190847 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 2, 2, 2]
def baseStart_7190847 : Nat := 118140960795 + 7190847 * 2 ^ 59
def prefixEnd_7190847 : Nat := 4983230072969 + 3 ^ 40 * 7190847 * 2
def baseEnd_7190847 : Nat := 3692360823941332511742403

theorem tailTrace_7190847 : CollatzResearch.WordTrace tailWord_7190847 prefixEnd_7190847 3692360823941332511742403 := by
  unfold tailWord_7190847
  simp only [CollatzResearch.WordTrace]
  refine ⟨262271736579796892738762795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174847824386531261825841863 262271736579796892738762795)
  ·
    refine ⟨393407604869695339108144193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262271736579796892738762795 393407604869695339108144193)
    ·
      refine ⟨295055703652271504331108145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393407604869695339108144193 295055703652271504331108145)
      ·
        refine ⟨221291777739203628248331109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295055703652271504331108145 221291777739203628248331109)
        ·
          refine ⟨41492208326100680296562083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221291777739203628248331109 41492208326100680296562083)
          ·
            refine ⟨62238312489151020444843125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41492208326100680296562083 62238312489151020444843125)
            ·
              refine ⟨5834841795857908166704043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62238312489151020444843125 5834841795857908166704043)
              ·
                refine ⟨8752262693786862250056065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5834841795857908166704043 8752262693786862250056065)
                ·
                  refine ⟨6564197020340146687542049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8752262693786862250056065 6564197020340146687542049)
                  ·
                    refine ⟨4923147765255110015656537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6564197020340146687542049 4923147765255110015656537)
                    ·
                      refine ⟨3692360823941332511742403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923147765255110015656537 3692360823941332511742403)
                      ·
                        rfl

theorem cell23_7190847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_7190847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190847 prefixEnd_7190847 := by exact prefixLift 7190847
  have htrace : WordTrace (prefixWord ++ tailWord_7190847) baseStart_7190847 baseEnd_7190847 := by
    simpa [prefixWord, tailWord_7190847, baseEnd_7190847] using wordTrace_append hprefix tailTrace_7190847
  have hstable : (prefixWord ++ tailWord_7190847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190847).length < 2 ^ (prefixWord ++ tailWord_7190847).sum := by decide
  have hdescent : baseEnd_7190847 < baseStart_7190847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190859 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 7]
def baseStart_7190859 : Nat := 118140960795 + 7190859 * 2 ^ 59
def prefixEnd_7190859 : Nat := 4983230072969 + 3 ^ 40 * 7190859 * 2
def baseEnd_7190859 : Nat := 3692366985709186464792347

theorem tailTrace_7190859 : CollatzResearch.WordTrace tailWord_7190859 prefixEnd_7190859 3692366985709186464792347 := by
  unfold tailWord_7190859
  simp only [CollatzResearch.WordTrace]
  refine ⟨262272174255753418788199631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174848116170502279192133087 262272174255753418788199631)
  ·
    refine ⟨393408261383630128182299447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262272174255753418788199631 393408261383630128182299447)
    ·
      refine ⟨590112392075445192273449171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393408261383630128182299447 590112392075445192273449171)
      ·
        refine ⟨885168588113167788410173757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590112392075445192273449171 885168588113167788410173757)
        ·
          refine ⟨331938220542437920653815159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 885168588113167788410173757 331938220542437920653815159)
          ·
            refine ⟨497907330813656880980722739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331938220542437920653815159 497907330813656880980722739)
            ·
              refine ⟨746860996220485321471084109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497907330813656880980722739 746860996220485321471084109)
              ·
                refine ⟨280072873582681995551656541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746860996220485321471084109 280072873582681995551656541)
                ·
                  refine ⟨105027327593505748331871203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280072873582681995551656541 105027327593505748331871203)
                  ·
                    refine ⟨157540991390258622497806805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105027327593505748331871203 157540991390258622497806805)
                    ·
                      refine ⟨3692366985709186464792347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157540991390258622497806805 3692366985709186464792347)
                      ·
                        rfl

theorem cell23_7190859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_7190859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190859 prefixEnd_7190859 := by exact prefixLift 7190859
  have htrace : WordTrace (prefixWord ++ tailWord_7190859) baseStart_7190859 baseEnd_7190859 := by
    simpa [prefixWord, tailWord_7190859, baseEnd_7190859] using wordTrace_append hprefix tailTrace_7190859
  have hstable : (prefixWord ++ tailWord_7190859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190859).length < 2 ^ (prefixWord ++ tailWord_7190859).sum := by decide
  have hdescent : baseEnd_7190859 < baseStart_7190859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190866 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_7190866 : Nat := 118140960795 + 7190866 * 2 ^ 59
def prefixEnd_7190866 : Nat := 4983230072969 + 3 ^ 40 * 7190866 * 2
def baseEnd_7190866 : Nat := 1230790193357922645801605

theorem tailTrace_7190866 : CollatzResearch.WordTrace tailWord_7190866 prefixEnd_7190866 1230790193357922645801605 := by
  unfold tailWord_7190866
  simp only [CollatzResearch.WordTrace]
  refine ⟨65568107391682014745926113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174848286377818705989136301 65568107391682014745926113)
  ·
    refine ⟨49176080543761511059444585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65568107391682014745926113 49176080543761511059444585)
    ·
      refine ⟨36882060407821133294583439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49176080543761511059444585 36882060407821133294583439)
      ·
        refine ⟨55323090611731699941875159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36882060407821133294583439 55323090611731699941875159)
        ·
          refine ⟨82984635917597549912812739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55323090611731699941875159 82984635917597549912812739)
          ·
            refine ⟨124476953876396324869219109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82984635917597549912812739 124476953876396324869219109)
            ·
              refine ⟨23339428851824310912978583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124476953876396324869219109 23339428851824310912978583)
              ·
                refine ⟨35009143277736466369467875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23339428851824310912978583 35009143277736466369467875)
                ·
                  refine ⟨52513714916604699554201813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35009143277736466369467875 52513714916604699554201813)
                  ·
                    refine ⟨1230790193357922645801605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52513714916604699554201813 1230790193357922645801605)
                    ·
                      rfl

theorem cell23_7190866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_7190866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190866 prefixEnd_7190866 := by exact prefixLift 7190866
  have htrace : WordTrace (prefixWord ++ tailWord_7190866) baseStart_7190866 baseEnd_7190866 := by
    simpa [prefixWord, tailWord_7190866, baseEnd_7190866] using wordTrace_append hprefix tailTrace_7190866
  have hstable : (prefixWord ++ tailWord_7190866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190866).length < 2 ^ (prefixWord ++ tailWord_7190866).sum := by decide
  have hdescent : baseEnd_7190866 < baseStart_7190866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190923 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 3]
def baseStart_7190923 : Nat := 118140960795 + 7190923 * 2 ^ 59
def prefixEnd_7190923 : Nat := 4983230072969 + 3 ^ 40 * 7190923 * 2
def baseEnd_7190923 : Nat := 3692399848471074214392053

theorem tailTrace_7190923 : CollatzResearch.WordTrace tailWord_7190923 prefixEnd_7190923 3692399848471074214392053 := by
  unfold tailWord_7190923
  simp only [CollatzResearch.WordTrace]
  refine ⟨262274508527521557718529423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174849672351681038479019615 262274508527521557718529423)
  ·
    refine ⟨393411762791282336577794135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262274508527521557718529423 393411762791282336577794135)
    ·
      refine ⟨590117644186923504866691203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393411762791282336577794135 590117644186923504866691203)
      ·
        refine ⟨885176466280385257300036805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590117644186923504866691203 885176466280385257300036805)
        ·
          refine ⟨165970587427572235743756901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 885176466280385257300036805 165970587427572235743756901)
          ·
            refine ⟨31119485142669794201954419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165970587427572235743756901 31119485142669794201954419)
            ·
              refine ⟨46679227714004691302931629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31119485142669794201954419 46679227714004691302931629)
              ·
                refine ⟨17504710392751759238599361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46679227714004691302931629 17504710392751759238599361)
                ·
                  refine ⟨13128532794563819428949521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17504710392751759238599361 13128532794563819428949521)
                  ·
                    refine ⟨9846399595922864571712141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13128532794563819428949521 9846399595922864571712141)
                    ·
                      refine ⟨3692399848471074214392053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9846399595922864571712141 3692399848471074214392053)
                      ·
                        rfl

theorem cell23_7190923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 3].length) (baseStart_7190923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190923 prefixEnd_7190923 := by exact prefixLift 7190923
  have htrace : WordTrace (prefixWord ++ tailWord_7190923) baseStart_7190923 baseEnd_7190923 := by
    simpa [prefixWord, tailWord_7190923, baseEnd_7190923] using wordTrace_append hprefix tailTrace_7190923
  have hstable : (prefixWord ++ tailWord_7190923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190923).length < 2 ^ (prefixWord ++ tailWord_7190923).sum := by decide
  have hdescent : baseEnd_7190923 < baseStart_7190923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190943 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 6]
def baseStart_7190943 : Nat := 118140960795 + 7190943 * 2 ^ 59
def prefixEnd_7190943 : Nat := 4983230072969 + 3 ^ 40 * 7190943 * 2
def baseEnd_7190943 : Nat := 410267790898240459571329

theorem tailTrace_7190943 : CollatzResearch.WordTrace tailWord_7190943 prefixEnd_7190943 410267790898240459571329 := by
  unfold tailWord_7190943
  simp only [CollatzResearch.WordTrace]
  refine ⟨262275237987449101134257483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174850158658299400756171655 262275237987449101134257483)
  ·
    refine ⟨393412856981173651701386225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262275237987449101134257483 393412856981173651701386225)
    ·
      refine ⟨295059642735880238776039669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393412856981173651701386225 295059642735880238776039669)
      ·
        refine ⟨27661841506488772385253719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295059642735880238776039669 27661841506488772385253719)
        ·
          refine ⟨41492762259733158577880579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27661841506488772385253719 41492762259733158577880579)
          ·
            refine ⟨62239143389599737866820869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41492762259733158577880579 62239143389599737866820869)
            ·
              refine ⟨11669839385549950850028913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62239143389599737866820869 11669839385549950850028913)
              ·
                refine ⟨8752379539162463137521685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11669839385549950850028913 8752379539162463137521685)
                ·
                  refine ⟨410267790898240459571329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8752379539162463137521685 410267790898240459571329)
                  ·
                    rfl

theorem cell23_7190943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 6].length) (baseStart_7190943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190943 prefixEnd_7190943 := by exact prefixLift 7190943
  have htrace : WordTrace (prefixWord ++ tailWord_7190943) baseStart_7190943 baseEnd_7190943 := by
    simpa [prefixWord, tailWord_7190943, baseEnd_7190943] using wordTrace_append hprefix tailTrace_7190943
  have hstable : (prefixWord ++ tailWord_7190943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190943).length < 2 ^ (prefixWord ++ tailWord_7190943).sum := by decide
  have hdescent : baseEnd_7190943 < baseStart_7190943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190947 : List Nat := [1, 1, 1, 4, 1, 4, 4, 2, 1, 4]
def baseStart_7190947 : Nat := 118140960795 + 7190947 * 2 ^ 59
def prefixEnd_7190947 : Nat := 4983230072969 + 3 ^ 40 * 7190947 * 2
def baseEnd_7190947 : Nat := 1230804057335594040163981

theorem tailTrace_7190947 : CollatzResearch.WordTrace tailWord_7190947 prefixEnd_7190947 1230804057335594040163981 := by
  unfold tailWord_7190947
  simp only [CollatzResearch.WordTrace]
  refine ⟨262275383879434609817403095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174850255919623073211602063 262275383879434609817403095)
  ·
    refine ⟨393413075819151914726104643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262275383879434609817403095 393413075819151914726104643)
    ·
      refine ⟨590119613728727872089156965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393413075819151914726104643 590119613728727872089156965)
      ·
        refine ⟨110647427574136476016716931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 590119613728727872089156965 110647427574136476016716931)
        ·
          refine ⟨165971141361204714025075397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110647427574136476016716931 165971141361204714025075397)
          ·
            refine ⟨31119589005225883879701637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165971141361204714025075397 31119589005225883879701637)
            ·
              refine ⟨5834922938479853227444057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31119589005225883879701637 5834922938479853227444057)
              ·
                refine ⟨4376192203859889920583043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834922938479853227444057 4376192203859889920583043)
                ·
                  refine ⟨6564288305789834880874565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376192203859889920583043 6564288305789834880874565)
                  ·
                    refine ⟨1230804057335594040163981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6564288305789834880874565 1230804057335594040163981)
                    ·
                      rfl

theorem cell23_7190947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 4].length) (baseStart_7190947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190947 prefixEnd_7190947 := by exact prefixLift 7190947
  have htrace : WordTrace (prefixWord ++ tailWord_7190947) baseStart_7190947 baseEnd_7190947 := by
    simpa [prefixWord, tailWord_7190947, baseEnd_7190947] using wordTrace_append hprefix tailTrace_7190947
  have hstable : (prefixWord ++ tailWord_7190947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190947).length < 2 ^ (prefixWord ++ tailWord_7190947).sum := by decide
  have hdescent : baseEnd_7190947 < baseStart_7190947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190953 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 3]
def baseStart_7190953 : Nat := 118140960795 + 7190953 * 2 ^ 59
def prefixEnd_7190953 : Nat := 4983230072969 + 3 ^ 40 * 7190953 * 2
def baseEnd_7190953 : Nat := 3692415252890709097016915

theorem tailTrace_7190953 : CollatzResearch.WordTrace tailWord_7190953 prefixEnd_7190953 3692415252890709097016915 := by
  unfold tailWord_7190953
  simp only [CollatzResearch.WordTrace]
  refine ⟨262275602717412872842121513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174850401811608581894747675 262275602717412872842121513)
  ·
    refine ⟨196706702038059654631591135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262275602717412872842121513 196706702038059654631591135)
    ·
      refine ⟨295060053057089481947386703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196706702038059654631591135 295060053057089481947386703)
      ·
        refine ⟨442590079585634222921080055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295060053057089481947386703 442590079585634222921080055)
        ·
          refine ⟨663885119378451334381620083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442590079585634222921080055 663885119378451334381620083)
          ·
            refine ⟨995827679067677001572430125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663885119378451334381620083 995827679067677001572430125)
            ·
              refine ⟨373435379650378875589661297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 995827679067677001572430125 373435379650378875589661297)
              ·
                refine ⟨280076534737784156692245973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373435379650378875589661297 280076534737784156692245973)
                ·
                  refine ⟨6564293782916816172474515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 280076534737784156692245973 6564293782916816172474515)
                  ·
                    refine ⟨9846440674375224258711773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564293782916816172474515 9846440674375224258711773)
                    ·
                      refine ⟨3692415252890709097016915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9846440674375224258711773 3692415252890709097016915)
                      ·
                        rfl

theorem cell23_7190953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 3].length) (baseStart_7190953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190953 prefixEnd_7190953 := by exact prefixLift 7190953
  have htrace : WordTrace (prefixWord ++ tailWord_7190953) baseStart_7190953 baseEnd_7190953 := by
    simpa [prefixWord, tailWord_7190953, baseEnd_7190953] using wordTrace_append hprefix tailTrace_7190953
  have hstable : (prefixWord ++ tailWord_7190953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190953).length < 2 ^ (prefixWord ++ tailWord_7190953).sum := by decide
  have hdescent : baseEnd_7190953 < baseStart_7190953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190964 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_7190964 : Nat := 118140960795 + 7190964 * 2 ^ 59
def prefixEnd_7190964 : Nat := 4983230072969 + 3 ^ 40 * 7190964 * 2
def baseEnd_7190964 : Nat := 1230806967059302851326455

theorem tailTrace_7190964 : CollatzResearch.WordTrace tailWord_7190964 prefixEnd_7190964 1230806967059302851326455 := by
  unfold tailWord_7190964
  simp only [CollatzResearch.WordTrace]
  refine ⟨131138001960186510860385973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174850669280248681147181297 131138001960186510860385973)
  ·
    refine ⟨12294187683767485393161185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131138001960186510860385973 12294187683767485393161185)
    ·
      refine ⟨9220640762825614044870889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12294187683767485393161185 9220640762825614044870889)
      ·
        refine ⟨6915480572119210533653167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9220640762825614044870889 6915480572119210533653167)
        ·
          refine ⟨10373220858178815800479751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915480572119210533653167 10373220858178815800479751)
          ·
            refine ⟨15559831287268223700719627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10373220858178815800479751 15559831287268223700719627)
            ·
              refine ⟨23339746930902335551079441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15559831287268223700719627 23339746930902335551079441)
              ·
                refine ⟨17504810198176751663309581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23339746930902335551079441 17504810198176751663309581)
                ·
                  refine ⟨6564303824316281873741093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17504810198176751663309581 6564303824316281873741093)
                  ·
                    refine ⟨1230806967059302851326455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6564303824316281873741093 1230806967059302851326455)
                    ·
                      rfl

theorem cell23_7190964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_7190964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190964 prefixEnd_7190964 := by exact prefixLift 7190964
  have htrace : WordTrace (prefixWord ++ tailWord_7190964) baseStart_7190964 baseEnd_7190964 := by
    simpa [prefixWord, tailWord_7190964, baseEnd_7190964] using wordTrace_append hprefix tailTrace_7190964
  have hstable : (prefixWord ++ tailWord_7190964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190964).length < 2 ^ (prefixWord ++ tailWord_7190964).sum := by decide
  have hdescent : baseEnd_7190964 < baseStart_7190964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190973 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_7190973 : Nat := 118140960795 + 7190973 * 2 ^ 59
def prefixEnd_7190973 : Nat := 4983230072969 + 3 ^ 40 * 7190973 * 2
def baseEnd_7190973 : Nat := 1230808507501266339588941

theorem tailTrace_7190973 : CollatzResearch.WordTrace tailWord_7190973 prefixEnd_7190973 1230808507501266339588941 := by
  unfold tailWord_7190973
  simp only [CollatzResearch.WordTrace]
  refine ⟨262276332177340416257849573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174850888118226944171899715 262276332177340416257849573)
  ·
    refine ⟨49176812283251328048346795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262276332177340416257849573 49176812283251328048346795)
    ·
      refine ⟨73765218424876992072520193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49176812283251328048346795 73765218424876992072520193)
      ·
        refine ⟨55323913818657744054390145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73765218424876992072520193 55323913818657744054390145)
        ·
          refine ⟨41492935363993308040792609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55323913818657744054390145 41492935363993308040792609)
          ·
            refine ⟨31119701522994981030594457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41492935363993308040792609 31119701522994981030594457)
            ·
              refine ⟨23339776142246235772945843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31119701522994981030594457 23339776142246235772945843)
              ·
                refine ⟨35009664213369353659418765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23339776142246235772945843 35009664213369353659418765)
                ·
                  refine ⟨13128624080013507622282037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35009664213369353659418765 13128624080013507622282037)
                  ·
                    refine ⟨1230808507501266339588941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13128624080013507622282037 1230808507501266339588941)
                    ·
                      rfl

theorem cell23_7190973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_7190973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190973 prefixEnd_7190973 := by exact prefixLift 7190973
  have htrace : WordTrace (prefixWord ++ tailWord_7190973) baseStart_7190973 baseEnd_7190973 := by
    simpa [prefixWord, tailWord_7190973, baseEnd_7190973] using wordTrace_append hprefix tailTrace_7190973
  have hstable : (prefixWord ++ tailWord_7190973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190973).length < 2 ^ (prefixWord ++ tailWord_7190973).sum := by decide
  have hdescent : baseEnd_7190973 < baseStart_7190973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190993 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 1, 8, 2]
def baseStart_7190993 : Nat := 118140960795 + 7190993 * 2 ^ 59
def prefixEnd_7190993 : Nat := 4983230072969 + 3 ^ 40 * 7190993 * 2
def baseEnd_7190993 : Nat := 3692435792116888940516731

theorem tailTrace_7190993 : CollatzResearch.WordTrace tailWord_7190993 prefixEnd_7190993 3692435792116888940516731 := by
  unfold tailWord_7190993
  simp only [CollatzResearch.WordTrace]
  refine ⟨262277061637267959673577633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174851374424845306449051755 262277061637267959673577633)
  ·
    refine ⟨196707796227950969755183225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262277061637267959673577633 196707796227950969755183225)
    ·
      refine ⟨147530847170963227316387419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196707796227950969755183225 147530847170963227316387419)
      ·
        refine ⟨221296270756444840974581129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147530847170963227316387419 221296270756444840974581129)
        ·
          refine ⟨165972203067333630730935847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221296270756444840974581129 165972203067333630730935847)
          ·
            refine ⟨248958304601000446096403771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165972203067333630730935847 248958304601000446096403771)
            ·
              refine ⟨373437456901500669144605657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248958304601000446096403771 373437456901500669144605657)
              ·
                refine ⟨280078092676125501858454243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373437456901500669144605657 280078092676125501858454243)
                ·
                  refine ⟨420117139014188252787681365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280078092676125501858454243 420117139014188252787681365)
                  ·
                    refine ⟨4923247722822518587355641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 420117139014188252787681365 4923247722822518587355641)
                    ·
                      refine ⟨3692435792116888940516731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923247722822518587355641 3692435792116888940516731)
                      ·
                        rfl

theorem cell23_7190993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_7190993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190993 prefixEnd_7190993 := by exact prefixLift 7190993
  have htrace : WordTrace (prefixWord ++ tailWord_7190993) baseStart_7190993 baseEnd_7190993 := by
    simpa [prefixWord, tailWord_7190993, baseEnd_7190993] using wordTrace_append hprefix tailTrace_7190993
  have hstable : (prefixWord ++ tailWord_7190993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190993).length < 2 ^ (prefixWord ++ tailWord_7190993).sum := by decide
  have hdescent : baseEnd_7190993 < baseStart_7190993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7190994 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 6]
def baseStart_7190994 : Nat := 118140960795 + 7190994 * 2 ^ 59
def prefixEnd_7190994 : Nat := 4983230072969 + 3 ^ 40 * 7190994 * 2
def baseEnd_7190994 : Nat := 410270700621949270733803

theorem tailTrace_7190994 : CollatzResearch.WordTrace tailWord_7190994 prefixEnd_7190994 410270700621949270733803 := by
  unfold tailWord_7190994
  simp only [CollatzResearch.WordTrace]
  refine ⟨65569274527566084211091009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174851398740176224562909357 65569274527566084211091009)
  ·
    refine ⟨49176955895674563158318257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65569274527566084211091009 49176955895674563158318257)
    ·
      refine ⟨36882716921755922368738693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49176955895674563158318257 36882716921755922368738693)
      ·
        refine ⟨6915509422829235444138505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36882716921755922368738693 6915509422829235444138505)
        ·
          refine ⟨5186632067121926583103879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6915509422829235444138505 5186632067121926583103879)
          ·
            refine ⟨7779948100682889874655819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186632067121926583103879 7779948100682889874655819)
            ·
              refine ⟨11669922151024334811983729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779948100682889874655819 11669922151024334811983729)
              ·
                refine ⟨8752441613268251108987797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11669922151024334811983729 8752441613268251108987797)
                ·
                  refine ⟨410270700621949270733803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8752441613268251108987797 410270700621949270733803)
                  ·
                    rfl

theorem cell23_7190994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_7190994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7190994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7190994 prefixEnd_7190994 := by exact prefixLift 7190994
  have htrace : WordTrace (prefixWord ++ tailWord_7190994) baseStart_7190994 baseEnd_7190994 := by
    simpa [prefixWord, tailWord_7190994, baseEnd_7190994] using wordTrace_append hprefix tailTrace_7190994
  have hstable : (prefixWord ++ tailWord_7190994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7190994).length < 2 ^ (prefixWord ++ tailWord_7190994).sum := by decide
  have hdescent : baseEnd_7190994 < baseStart_7190994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7190994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191033 : List Nat := [1, 2, 1, 3, 1, 2, 6, 7]
def baseStart_7191033 : Nat := 118140960795 + 7191033 * 2 ^ 59
def prefixEnd_7191033 : Nat := 4983230072969 + 3 ^ 40 * 7191033 * 2
def baseEnd_7191033 : Nat := 136757641901595140148761

theorem tailTrace_7191033 : CollatzResearch.WordTrace tailWord_7191033 prefixEnd_7191033 136757641901595140148761 := by
  unfold tailWord_7191033
  simp only [CollatzResearch.WordTrace]
  refine ⟨262278520557123046505033753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174852347038082031003355835 262278520557123046505033753)
  ·
    refine ⟨196708890417842284878775315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262278520557123046505033753 196708890417842284878775315)
    ·
      refine ⟨295063335626763427318162973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196708890417842284878775315 295063335626763427318162973)
      ·
        refine ⟨110648750860036285244311115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295063335626763427318162973 110648750860036285244311115)
        ·
          refine ⟨165973126290054427866466673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110648750860036285244311115 165973126290054427866466673)
          ·
            refine ⟨124479844717540820899850005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165973126290054427866466673 124479844717540820899850005)
            ·
              refine ⟨5834992721134725979680469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124479844717540820899850005 5834992721134725979680469)
              ·
                refine ⟨136757641901595140148761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5834992721134725979680469 136757641901595140148761)
                ·
                  rfl

theorem cell23_7191033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 7].length) (baseStart_7191033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191033 prefixEnd_7191033 := by exact prefixLift 7191033
  have htrace : WordTrace (prefixWord ++ tailWord_7191033) baseStart_7191033 baseEnd_7191033 := by
    simpa [prefixWord, tailWord_7191033, baseEnd_7191033] using wordTrace_append hprefix tailTrace_7191033
  have hstable : (prefixWord ++ tailWord_7191033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191033).length < 2 ^ (prefixWord ++ tailWord_7191033).sum := by decide
  have hdescent : baseEnd_7191033 < baseStart_7191033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191043 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 3]
def baseStart_7191043 : Nat := 118140960795 + 7191043 * 2 ^ 59
def prefixEnd_7191043 : Nat := 4983230072969 + 3 ^ 40 * 7191043 * 2
def baseEnd_7191043 : Nat := 3692461466149613744891501

theorem tailTrace_7191043 : CollatzResearch.WordTrace tailWord_7191043 prefixEnd_7191043 3692461466149613744891501 := by
  unfold tailWord_7191043
  simp only [CollatzResearch.WordTrace]
  refine ⟨262278885287086818212897783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174852590191391212141931855 262278885287086818212897783)
  ·
    refine ⟨393418327930630227319346675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262278885287086818212897783 393418327930630227319346675)
    ·
      refine ⟨590127491895945340979020013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393418327930630227319346675 590127491895945340979020013)
      ·
        refine ⟨221297809460979502867132505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 590127491895945340979020013 221297809460979502867132505)
        ·
          refine ⟨165973357095734627150349379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221297809460979502867132505 165973357095734627150349379)
          ·
            refine ⟨248960035643601940725524069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165973357095734627150349379 248960035643601940725524069)
            ·
              refine ⟨46680006683175363886035763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248960035643601940725524069 46680006683175363886035763)
              ·
                refine ⟨70020010024763045829053645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46680006683175363886035763 70020010024763045829053645)
                ·
                  refine ⟨26257503759286142185895117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70020010024763045829053645 26257503759286142185895117)
                  ·
                    refine ⟨9846563909732303319710669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26257503759286142185895117 9846563909732303319710669)
                    ·
                      refine ⟨3692461466149613744891501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9846563909732303319710669 3692461466149613744891501)
                      ·
                        rfl

theorem cell23_7191043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_7191043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191043 prefixEnd_7191043 := by exact prefixLift 7191043
  have htrace : WordTrace (prefixWord ++ tailWord_7191043) baseStart_7191043 baseEnd_7191043 := by
    simpa [prefixWord, tailWord_7191043, baseEnd_7191043] using wordTrace_append hprefix tailTrace_7191043
  have hstable : (prefixWord ++ tailWord_7191043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191043).length < 2 ^ (prefixWord ++ tailWord_7191043).sum := by decide
  have hdescent : baseEnd_7191043 < baseStart_7191043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191061 : List Nat := [1, 3, 2, 1, 3, 1, 5, 2, 1, 2, 2]
def baseStart_7191061 : Nat := 118140960795 + 7191061 * 2 ^ 59
def prefixEnd_7191061 : Nat := 4983230072969 + 3 ^ 40 * 7191061 * 2
def baseEnd_7191061 : Nat := 3692470708801394674466419

theorem tailTrace_7191061 : CollatzResearch.WordTrace tailWord_7191061 prefixEnd_7191061 3692470708801394674466419 := by
  unfold tailWord_7191061
  simp only [CollatzResearch.WordTrace]
  refine ⟨262279541801021607287053037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174853027867347738191368691 262279541801021607287053037)
  ·
    refine ⟨98354828175383102732644889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262279541801021607287053037 98354828175383102732644889)
    ·
      refine ⟨73766121131537327049483667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98354828175383102732644889 73766121131537327049483667)
      ·
        refine ⟨110649181697305990574225501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73766121131537327049483667 110649181697305990574225501)
        ·
          refine ⟨41493443136489746465334563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110649181697305990574225501 41493443136489746465334563)
          ·
            refine ⟨62240164704734619698001845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41493443136489746465334563 62240164704734619698001845)
            ·
              refine ⟨5835015441068870596687673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62240164704734619698001845 5835015441068870596687673)
              ·
                refine ⟨4376261580801652947515755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5835015441068870596687673 4376261580801652947515755)
                ·
                  refine ⟨6564392371202479421273633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376261580801652947515755 6564392371202479421273633)
                  ·
                    refine ⟨4923294278401859565955225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6564392371202479421273633 4923294278401859565955225)
                    ·
                      refine ⟨3692470708801394674466419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923294278401859565955225 3692470708801394674466419)
                      ·
                        rfl

theorem cell23_7191061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_7191061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191061 prefixEnd_7191061 := by exact prefixLift 7191061
  have htrace : WordTrace (prefixWord ++ tailWord_7191061) baseStart_7191061 baseEnd_7191061 := by
    simpa [prefixWord, tailWord_7191061, baseEnd_7191061] using wordTrace_append hprefix tailTrace_7191061
  have hstable : (prefixWord ++ tailWord_7191061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191061).length < 2 ^ (prefixWord ++ tailWord_7191061).sum := by decide
  have hdescent : baseEnd_7191061 < baseStart_7191061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191103 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_7191103 : Nat := 118140960795 + 7191103 * 2 ^ 59
def prefixEnd_7191103 : Nat := 4983230072969 + 3 ^ 40 * 7191103 * 2
def baseEnd_7191103 : Nat := 3692492274988883510141225

theorem tailTrace_7191103 : CollatzResearch.WordTrace tailWord_7191103 prefixEnd_7191103 3692492274988883510141225 := by
  unfold tailWord_7191103
  simp only [CollatzResearch.WordTrace]
  refine ⟨262281073666869448460081963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174854049111246298973387975 262281073666869448460081963)
  ·
    refine ⟨393421610500304172690122945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262281073666869448460081963 393421610500304172690122945)
    ·
      refine ⟨295066207875228129517592209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393421610500304172690122945 295066207875228129517592209)
      ·
        refine ⟨221299655906421097138194157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295066207875228129517592209 221299655906421097138194157)
        ·
          refine ⟨82987370964907911426822809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221299655906421097138194157 82987370964907911426822809)
          ·
            refine ⟨62240528223680933570117107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82987370964907911426822809 62240528223680933570117107)
            ·
              refine ⟨93360792335521400355175661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62240528223680933570117107 93360792335521400355175661)
              ·
                refine ⟨35010297125820525133190873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93360792335521400355175661 35010297125820525133190873)
                ·
                  refine ⟨26257722844365393849893155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35010297125820525133190873 26257722844365393849893155)
                  ·
                    refine ⟨39386584266548090774839733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26257722844365393849893155 39386584266548090774839733)
                    ·
                      refine ⟨3692492274988883510141225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39386584266548090774839733 3692492274988883510141225)
                      ·
                        rfl

theorem cell23_7191103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_7191103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191103 prefixEnd_7191103 := by exact prefixLift 7191103
  have htrace : WordTrace (prefixWord ++ tailWord_7191103) baseStart_7191103 baseEnd_7191103 := by
    simpa [prefixWord, tailWord_7191103, baseEnd_7191103] using wordTrace_append hprefix tailTrace_7191103
  have hstable : (prefixWord ++ tailWord_7191103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191103).length < 2 ^ (prefixWord ++ tailWord_7191103).sum := by decide
  have hdescent : baseEnd_7191103 < baseStart_7191103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191160 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 4, 5, 2]
def baseStart_7191160 : Nat := 118140960795 + 7191160 * 2 ^ 59
def prefixEnd_7191160 : Nat := 4983230072969 + 3 ^ 40 * 7191160 * 2
def baseEnd_7191160 : Nat := 3692521543386189787128463

theorem tailTrace_7191160 : CollatzResearch.WordTrace tailWord_7191160 prefixEnd_7191160 3692521543386189787128463 := by
  unfold tailWord_7191160
  simp only [CollatzResearch.WordTrace]
  refine ⟨131141576313831473597453467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174855435085108631463271289 131141576313831473597453467)
  ·
    refine ⟨196712364470747210396180201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131141576313831473597453467 196712364470747210396180201)
    ·
      refine ⟨147534273353060407797135151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196712364470747210396180201 147534273353060407797135151)
      ·
        refine ⟨221301410029590611695702727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147534273353060407797135151 221301410029590611695702727)
        ·
          refine ⟨331952115044385917543554091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221301410029590611695702727 331952115044385917543554091)
          ·
            refine ⟨497928172566578876315331137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331952115044385917543554091 497928172566578876315331137)
            ·
              refine ⟨373446129424934157236498353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497928172566578876315331137 373446129424934157236498353)
              ·
                refine ⟨280084597068700617927373765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373446129424934157236498353 280084597068700617927373765)
                ·
                  refine ⟨52515861950381365861382581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280084597068700617927373765 52515861950381365861382581)
                  ·
                    refine ⟨4923362057848253049504617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52515861950381365861382581 4923362057848253049504617)
                    ·
                      refine ⟨3692521543386189787128463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923362057848253049504617 3692521543386189787128463)
                      ·
                        rfl

theorem cell23_7191160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_7191160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191160 prefixEnd_7191160 := by exact prefixLift 7191160
  have htrace : WordTrace (prefixWord ++ tailWord_7191160) baseStart_7191160 baseEnd_7191160 := by
    simpa [prefixWord, tailWord_7191160, baseEnd_7191160] using wordTrace_append hprefix tailTrace_7191160
  have hstable : (prefixWord ++ tailWord_7191160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191160).length < 2 ^ (prefixWord ++ tailWord_7191160).sum := by decide
  have hdescent : baseEnd_7191160 < baseStart_7191160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191163 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 5]
def baseStart_7191163 : Nat := 118140960795 + 7191163 * 2 ^ 59
def prefixEnd_7191163 : Nat := 4983230072969 + 3 ^ 40 * 7191163 * 2
def baseEnd_7191163 : Nat := 3692523083828153275390949

theorem tailTrace_7191163 : CollatzResearch.WordTrace tailWord_7191163 prefixEnd_7191163 3692523083828153275390949 := by
  unfold tailWord_7191163
  simp only [CollatzResearch.WordTrace]
  refine ⟨262283262046652078707266143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174855508031101385804844095 262283262046652078707266143)
  ·
    refine ⟨393424893069978118060899215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262283262046652078707266143 393424893069978118060899215)
    ·
      refine ⟨590137339604967177091348823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393424893069978118060899215 590137339604967177091348823)
      ·
        refine ⟨885206009407450765637023235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590137339604967177091348823 885206009407450765637023235)
        ·
          refine ⟨1327809014111176148455534853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885206009407450765637023235 1327809014111176148455534853)
          ·
            refine ⟨248964190145845527835412785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1327809014111176148455534853 248964190145845527835412785)
            ·
              refine ⟨186723142609384145876559589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248964190145845527835412785 186723142609384145876559589)
              ·
                refine ⟨35010589239259527351854923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186723142609384145876559589 35010589239259527351854923)
                ·
                  refine ⟨52515883858889291027782385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35010589239259527351854923 52515883858889291027782385)
                  ·
                    refine ⟨39386912894166968270836789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52515883858889291027782385 39386912894166968270836789)
                    ·
                      refine ⟨3692523083828153275390949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39386912894166968270836789 3692523083828153275390949)
                      ·
                        rfl

theorem cell23_7191163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_7191163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191163 prefixEnd_7191163 := by exact prefixLift 7191163
  have htrace : WordTrace (prefixWord ++ tailWord_7191163) baseStart_7191163 baseEnd_7191163 := by
    simpa [prefixWord, tailWord_7191163, baseEnd_7191163] using wordTrace_append hprefix tailTrace_7191163
  have hstable : (prefixWord ++ tailWord_7191163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191163).length < 2 ^ (prefixWord ++ tailWord_7191163).sum := by decide
  have hdescent : baseEnd_7191163 < baseStart_7191163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191203 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 6]
def baseStart_7191203 : Nat := 118140960795 + 7191203 * 2 ^ 59
def prefixEnd_7191203 : Nat := 4983230072969 + 3 ^ 40 * 7191203 * 2
def baseEnd_7191203 : Nat := 3692543623054333118890765

theorem tailTrace_7191203 : CollatzResearch.WordTrace tailWord_7191203 prefixEnd_7191203 3692543623054333118890765 := by
  unfold tailWord_7191203
  simp only [CollatzResearch.WordTrace]
  refine ⟨262284720966507165538722263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174856480644338110359148175 262284720966507165538722263)
  ·
    refine ⟨393427081449760748308083395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262284720966507165538722263 393427081449760748308083395)
    ·
      refine ⟨590140622174641122462125093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393427081449760748308083395 590140622174641122462125093)
      ·
        refine ⟨110651366657745210461648455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 590140622174641122462125093 110651366657745210461648455)
        ·
          refine ⟨165977049986617815692472683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110651366657745210461648455 165977049986617815692472683)
          ·
            refine ⟨248965574979926723538709025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165977049986617815692472683 248965574979926723538709025)
            ·
              refine ⟨186724181234945042654031769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248965574979926723538709025 186724181234945042654031769)
              ·
                refine ⟨140043135926208781990523827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186724181234945042654031769 140043135926208781990523827)
                ·
                  refine ⟨210064703889313172985785741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140043135926208781990523827 210064703889313172985785741)
                  ·
                    refine ⟨78774263958492439869669653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210064703889313172985785741 78774263958492439869669653)
                    ·
                      refine ⟨3692543623054333118890765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78774263958492439869669653 3692543623054333118890765)
                      ·
                        rfl

theorem cell23_7191203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_7191203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191203 prefixEnd_7191203 := by exact prefixLift 7191203
  have htrace : WordTrace (prefixWord ++ tailWord_7191203) baseStart_7191203 baseEnd_7191203 := by
    simpa [prefixWord, tailWord_7191203, baseEnd_7191203] using wordTrace_append hprefix tailTrace_7191203
  have hstable : (prefixWord ++ tailWord_7191203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191203).length < 2 ^ (prefixWord ++ tailWord_7191203).sum := by decide
  have hdescent : baseEnd_7191203 < baseStart_7191203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191230 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_7191230 : Nat := 118140960795 + 7191230 * 2 ^ 59
def prefixEnd_7191230 : Nat := 4983230072969 + 3 ^ 40 * 7191230 * 2
def baseEnd_7191230 : Nat := 410284165225778279250349

theorem tailTrace_7191230 : CollatzResearch.WordTrace tailWord_7191230 prefixEnd_7191230 410284165225778279250349 := by
  unfold tailWord_7191230
  simp only [CollatzResearch.WordTrace]
  refine ⟨32785713217176168643744393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174857137158272899433303429 32785713217176168643744393)
  ·
    refine ⟨24589284912882126482808295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32785713217176168643744393 24589284912882126482808295)
    ·
      refine ⟨36883927369323189724212443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24589284912882126482808295 36883927369323189724212443)
      ·
        refine ⟨55325891053984784586318665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36883927369323189724212443 55325891053984784586318665)
        ·
          refine ⟨41494418290488588439738999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55325891053984784586318665 41494418290488588439738999)
          ·
            refine ⟨62241627435732882659608499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41494418290488588439738999 62241627435732882659608499)
            ·
              refine ⟨93362441153599323989412749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62241627435732882659608499 93362441153599323989412749)
              ·
                refine ⟨35010915432599746496029781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93362441153599323989412749 35010915432599746496029781)
                ·
                  refine ⟨410284165225778279250349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35010915432599746496029781 410284165225778279250349)
                  ·
                    rfl

theorem cell23_7191230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_7191230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191230 prefixEnd_7191230 := by exact prefixLift 7191230
  have htrace : WordTrace (prefixWord ++ tailWord_7191230) baseStart_7191230 baseEnd_7191230 := by
    simpa [prefixWord, tailWord_7191230, baseEnd_7191230] using wordTrace_append hprefix tailTrace_7191230
  have hstable : (prefixWord ++ tailWord_7191230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191230).length < 2 ^ (prefixWord ++ tailWord_7191230).sum := by decide
  have hdescent : baseEnd_7191230 < baseStart_7191230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191243 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 11]
def baseStart_7191243 : Nat := 118140960795 + 7191243 * 2 ^ 59
def prefixEnd_7191243 : Nat := 4983230072969 + 3 ^ 40 * 7191243 * 2
def baseEnd_7191243 : Nat := 1230854720760170987463527

theorem tailTrace_7191243 : CollatzResearch.WordTrace tailWord_7191243 prefixEnd_7191243 1230854720760170987463527 := by
  unfold tailWord_7191243
  simp only [CollatzResearch.WordTrace]
  refine ⟨262286179886362252370178383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174857453257574834913452255 262286179886362252370178383)
  ·
    refine ⟨393429269829543378555267575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262286179886362252370178383 393429269829543378555267575)
    ·
      refine ⟨590143904744315067832901363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393429269829543378555267575 590143904744315067832901363)
      ·
        refine ⟨885215857116472601749352045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590143904744315067832901363 885215857116472601749352045)
        ·
          refine ⟨331955946418677225656007017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 885215857116472601749352045 331955946418677225656007017)
          ·
            refine ⟨248966959814007919242005263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331955946418677225656007017 248966959814007919242005263)
            ·
              refine ⟨373450439721011878863007895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248966959814007919242005263 373450439721011878863007895)
              ·
                refine ⟨560175659581517818294511843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373450439721011878863007895 560175659581517818294511843)
                ·
                  refine ⟨840263489372276727441767765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560175659581517818294511843 840263489372276727441767765)
                  ·
                    refine ⟨1230854720760170987463527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 840263489372276727441767765 1230854720760170987463527)
                    ·
                      rfl

theorem cell23_7191243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 11].length) (baseStart_7191243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191243 prefixEnd_7191243 := by exact prefixLift 7191243
  have htrace : WordTrace (prefixWord ++ tailWord_7191243) baseStart_7191243 baseEnd_7191243 := by
    simpa [prefixWord, tailWord_7191243, baseEnd_7191243] using wordTrace_append hprefix tailTrace_7191243
  have hstable : (prefixWord ++ tailWord_7191243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191243).length < 2 ^ (prefixWord ++ tailWord_7191243).sum := by decide
  have hdescent : baseEnd_7191243 < baseStart_7191243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191257 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 3]
def baseStart_7191257 : Nat := 118140960795 + 7191257 * 2 ^ 59
def prefixEnd_7191257 : Nat := 4983230072969 + 3 ^ 40 * 7191257 * 2
def baseEnd_7191257 : Nat := 3692571351009675907615517

theorem tailTrace_7191257 : CollatzResearch.WordTrace tailWord_7191257 prefixEnd_7191257 3692571351009675907615517 := by
  unfold tailWord_7191257
  simp only [CollatzResearch.WordTrace]
  refine ⟨262286690508311532761188025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174857793672207688507458683 262286690508311532761188025)
  ·
    refine ⟨196715017881233649570891019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262286690508311532761188025 196715017881233649570891019)
    ·
      refine ⟨295072526821850474356336529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196715017881233649570891019 295072526821850474356336529)
      ·
        refine ⟨221304395116387855767252397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295072526821850474356336529 221304395116387855767252397)
        ·
          refine ⟨82989148168645445912719649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221304395116387855767252397 82989148168645445912719649)
          ·
            refine ⟨62241861126484084434539737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82989148168645445912719649 62241861126484084434539737)
            ·
              refine ⟨46681395844863063325904803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62241861126484084434539737 46681395844863063325904803)
              ·
                refine ⟨70022093767294594988857205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46681395844863063325904803 70022093767294594988857205)
                ·
                  refine ⟨6564571290683868280205363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70022093767294594988857205 6564571290683868280205363)
                  ·
                    refine ⟨9846856936025802420308045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564571290683868280205363 9846856936025802420308045)
                    ·
                      refine ⟨3692571351009675907615517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9846856936025802420308045 3692571351009675907615517)
                      ·
                        rfl

theorem cell23_7191257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_7191257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191257 prefixEnd_7191257 := by exact prefixLift 7191257
  have htrace : WordTrace (prefixWord ++ tailWord_7191257) baseStart_7191257 baseEnd_7191257 := by
    simpa [prefixWord, tailWord_7191257, baseEnd_7191257] using wordTrace_append hprefix tailTrace_7191257
  have hstable : (prefixWord ++ tailWord_7191257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191257).length < 2 ^ (prefixWord ++ tailWord_7191257).sum := by decide
  have hdescent : baseEnd_7191257 < baseStart_7191257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191285 : List Nat := [1, 3, 6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7191285 : Nat := 118140960795 + 7191285 * 2 ^ 59
def prefixEnd_7191285 : Nat := 4983230072969 + 3 ^ 40 * 7191285 * 2
def baseEnd_7191285 : Nat := 1230861909489333932688463

theorem tailTrace_7191285 : CollatzResearch.WordTrace tailWord_7191285 prefixEnd_7191285 1230861909489333932688463 := by
  unfold tailWord_7191285
  simp only [CollatzResearch.WordTrace]
  refine ⟨262287711752210093543207309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174858474501473395695471539 262287711752210093543207309)
  ·
    refine ⟨98357891907078785078702741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262287711752210093543207309 98357891907078785078702741)
    ·
      refine ⟨4610526183144318050564191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98357891907078785078702741 4610526183144318050564191)
      ·
        refine ⟨6915789274716477075846287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610526183144318050564191 6915789274716477075846287)
        ·
          refine ⟨10373683912074715613769431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915789274716477075846287 10373683912074715613769431)
          ·
            refine ⟨15560525868112073420654147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10373683912074715613769431 15560525868112073420654147)
            ·
              refine ⟨23340788802168110130981221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15560525868112073420654147 23340788802168110130981221)
              ·
                refine ⟨4376397900406520649558979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23340788802168110130981221 4376397900406520649558979)
                ·
                  refine ⟨6564596850609780974338469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376397900406520649558979 6564596850609780974338469)
                  ·
                    refine ⟨1230861909489333932688463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6564596850609780974338469 1230861909489333932688463)
                    ·
                      rfl

theorem cell23_7191285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7191285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191285 prefixEnd_7191285 := by exact prefixLift 7191285
  have htrace : WordTrace (prefixWord ++ tailWord_7191285) baseStart_7191285 baseEnd_7191285 := by
    simpa [prefixWord, tailWord_7191285, baseEnd_7191285] using wordTrace_append hprefix tailTrace_7191285
  have hstable : (prefixWord ++ tailWord_7191285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191285).length < 2 ^ (prefixWord ++ tailWord_7191285).sum := by decide
  have hdescent : baseEnd_7191285 < baseStart_7191285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191297 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_7191297 : Nat := 118140960795 + 7191297 * 2 ^ 59
def prefixEnd_7191297 : Nat := 4983230072969 + 3 ^ 40 * 7191297 * 2
def baseEnd_7191297 : Nat := 3692591890235855751115333

theorem tailTrace_7191297 : CollatzResearch.WordTrace tailWord_7191297 prefixEnd_7191297 3692591890235855751115333 := by
  unfold tailWord_7191297
  simp only [CollatzResearch.WordTrace]
  refine ⟨262288149428166619592644145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174858766285444413061762763 262288149428166619592644145)
  ·
    refine ⟨196716112071124964694483109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262288149428166619592644145 196716112071124964694483109)
    ·
      refine ⟨36884271013335930880215583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196716112071124964694483109 36884271013335930880215583)
      ·
        refine ⟨55326406520003896320323375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36884271013335930880215583 55326406520003896320323375)
        ·
          refine ⟨82989609780005844480485063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55326406520003896320323375 82989609780005844480485063)
          ·
            refine ⟨124484414670008766720727595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82989609780005844480485063 124484414670008766720727595)
            ·
              refine ⟨186726622005013150081091393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124484414670008766720727595 186726622005013150081091393)
              ·
                refine ⟨140044966503759862560818545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186726622005013150081091393 140044966503759862560818545)
                ·
                  refine ⟨105033724877819896920613909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140044966503759862560818545 105033724877819896920613909)
                  ·
                    refine ⟨4923455853647807668153777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105033724877819896920613909 4923455853647807668153777)
                    ·
                      refine ⟨3692591890235855751115333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923455853647807668153777 3692591890235855751115333)
                      ·
                        rfl

theorem cell23_7191297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_7191297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191297 prefixEnd_7191297 := by exact prefixLift 7191297
  have htrace : WordTrace (prefixWord ++ tailWord_7191297) baseStart_7191297 baseEnd_7191297 := by
    simpa [prefixWord, tailWord_7191297, baseEnd_7191297] using wordTrace_append hprefix tailTrace_7191297
  have hstable : (prefixWord ++ tailWord_7191297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191297).length < 2 ^ (prefixWord ++ tailWord_7191297).sum := by decide
  have hdescent : baseEnd_7191297 < baseStart_7191297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191317 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_7191317 : Nat := 118140960795 + 7191317 * 2 ^ 59
def prefixEnd_7191317 : Nat := 4983230072969 + 3 ^ 40 * 7191317 * 2
def baseEnd_7191317 : Nat := 3692602159848945672865241

theorem tailTrace_7191317 : CollatzResearch.WordTrace tailWord_7191317 prefixEnd_7191317 3692602159848945672865241 := by
  unfold tailWord_7191317
  simp only [CollatzResearch.WordTrace]
  refine ⟨262288878888094163008372205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174859252592062775338914803 262288878888094163008372205)
  ·
    refine ⟨98358329583035311128139577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262288878888094163008372205 98358329583035311128139577)
    ·
      refine ⟨73768747187276483346104683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98358329583035311128139577 73768747187276483346104683)
      ·
        refine ⟨110653120780914725019157025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73768747187276483346104683 110653120780914725019157025)
        ·
          refine ⟨82989840585686043764367769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110653120780914725019157025 82989840585686043764367769)
          ·
            refine ⟨62242380439264532823275827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82989840585686043764367769 62242380439264532823275827)
            ·
              refine ⟨93363570658896799234913741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62242380439264532823275827 93363570658896799234913741)
              ·
                refine ⟨35011338997086299713092653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93363570658896799234913741 35011338997086299713092653)
                ·
                  refine ⟨13129252123907362392409745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35011338997086299713092653 13129252123907362392409745)
                  ·
                    refine ⟨9846939092930521794307309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13129252123907362392409745 9846939092930521794307309)
                    ·
                      refine ⟨3692602159848945672865241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9846939092930521794307309 3692602159848945672865241)
                      ·
                        rfl

theorem cell23_7191317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_7191317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191317 prefixEnd_7191317 := by exact prefixLift 7191317
  have htrace : WordTrace (prefixWord ++ tailWord_7191317) baseStart_7191317 baseEnd_7191317 := by
    simpa [prefixWord, tailWord_7191317, baseEnd_7191317] using wordTrace_append hprefix tailTrace_7191317
  have hstable : (prefixWord ++ tailWord_7191317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191317).length < 2 ^ (prefixWord ++ tailWord_7191317).sum := by decide
  have hdescent : baseEnd_7191317 < baseStart_7191317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191325 : List Nat := [1, 4, 2, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7191325 : Nat := 118140960795 + 7191325 * 2 ^ 59
def prefixEnd_7191325 : Nat := 4983230072969 + 3 ^ 40 * 7191325 * 2
def baseEnd_7191325 : Nat := 3692606267694181641565205

theorem tailTrace_7191325 : CollatzResearch.WordTrace tailWord_7191325 prefixEnd_7191325 3692606267694181641565205 := by
  unfold tailWord_7191325
  simp only [CollatzResearch.WordTrace]
  refine ⟨262289170672065180374663429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174859447114710120249775619 262289170672065180374663429)
  ·
    refine ⟨49179219501012221320249393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262289170672065180374663429 49179219501012221320249393)
    ·
      refine ⟨36884414625759165990187045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49179219501012221320249393 36884414625759165990187045)
      ·
        refine ⟨6915827742329843623160071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36884414625759165990187045 6915827742329843623160071)
        ·
          refine ⟨10373741613494765434740107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915827742329843623160071 10373741613494765434740107)
          ·
            refine ⟨15560612420242148152110161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10373741613494765434740107 15560612420242148152110161)
            ·
              refine ⟨11670459315181611114082621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15560612420242148152110161 11670459315181611114082621)
              ·
                refine ⟨4376422243193104167780983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11670459315181611114082621 4376422243193104167780983)
                ·
                  refine ⟨6564633364789656251671475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376422243193104167780983 6564633364789656251671475)
                  ·
                    refine ⟨9846950047184484377507213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564633364789656251671475 9846950047184484377507213)
                    ·
                      refine ⟨3692606267694181641565205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9846950047184484377507213 3692606267694181641565205)
                      ·
                        rfl

theorem cell23_7191325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7191325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191325 prefixEnd_7191325 := by exact prefixLift 7191325
  have htrace : WordTrace (prefixWord ++ tailWord_7191325) baseStart_7191325 baseEnd_7191325 := by
    simpa [prefixWord, tailWord_7191325, baseEnd_7191325] using wordTrace_append hprefix tailTrace_7191325
  have hstable : (prefixWord ++ tailWord_7191325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191325).length < 2 ^ (prefixWord ++ tailWord_7191325).sum := by decide
  have hdescent : baseEnd_7191325 < baseStart_7191325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191327 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_7191327 : Nat := 118140960795 + 7191327 * 2 ^ 59
def prefixEnd_7191327 : Nat := 4983230072969 + 3 ^ 40 * 7191327 * 2
def baseEnd_7191327 : Nat := 3692607294655490633740195

theorem tailTrace_7191327 : CollatzResearch.WordTrace tailWord_7191327 prefixEnd_7191327 3692607294655490633740195 := by
  unfold tailWord_7191327
  simp only [CollatzResearch.WordTrace]
  refine ⟨262289243618057934716236235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174859495745371956477490823 262289243618057934716236235)
  ·
    refine ⟨393433865427086902074354353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262289243618057934716236235 393433865427086902074354353)
    ·
      refine ⟨295075399070315176555765765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393433865427086902074354353 295075399070315176555765765)
      ·
        refine ⟨55326637325684095604206081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295075399070315176555765765 55326637325684095604206081)
        ·
          refine ⟨41494977994263071703154561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55326637325684095604206081 41494977994263071703154561)
          ·
            refine ⟨31121233495697303777365921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41494977994263071703154561 31121233495697303777365921)
            ·
              refine ⟨23340925121772977833024441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31121233495697303777365921 23340925121772977833024441)
              ·
                refine ⟨17505693841329733374768331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23340925121772977833024441 17505693841329733374768331)
                ·
                  refine ⟨26258540761994600062152497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17505693841329733374768331 26258540761994600062152497)
                  ·
                    refine ⟨19693905571495950046614373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26258540761994600062152497 19693905571495950046614373)
                    ·
                      refine ⟨3692607294655490633740195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19693905571495950046614373 3692607294655490633740195)
                      ·
                        rfl

theorem cell23_7191327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_7191327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191327 prefixEnd_7191327 := by exact prefixLift 7191327
  have htrace : WordTrace (prefixWord ++ tailWord_7191327) baseStart_7191327 baseEnd_7191327 := by
    simpa [prefixWord, tailWord_7191327, baseEnd_7191327] using wordTrace_append hprefix tailTrace_7191327
  have hstable : (prefixWord ++ tailWord_7191327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191327).length < 2 ^ (prefixWord ++ tailWord_7191327).sum := by decide
  have hdescent : baseEnd_7191327 < baseStart_7191327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191358 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_7191358 : Nat := 118140960795 + 7191358 * 2 ^ 59
def prefixEnd_7191358 : Nat := 4983230072969 + 3 ^ 40 * 7191358 * 2
def baseEnd_7191358 : Nat := 1230874404185260004150851

theorem tailTrace_7191358 : CollatzResearch.WordTrace tailWord_7191358 prefixEnd_7191358 1230874404185260004150851 := by
  unfold tailWord_7191358
  simp only [CollatzResearch.WordTrace]
  refine ⟨32786296785118203376326841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174860249520630418007076485 32786296785118203376326841)
  ·
    refine ⟨24589722588838652532245131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32786296785118203376326841 24589722588838652532245131)
    ·
      refine ⟨36884583883257978798367697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24589722588838652532245131 36884583883257978798367697)
      ·
        refine ⟨27663437912443484098775773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36884583883257978798367697 27663437912443484098775773)
        ·
          refine ⟨10373789217166306537040915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27663437912443484098775773 10373789217166306537040915)
          ·
            refine ⟨15560683825749459805561373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10373789217166306537040915 15560683825749459805561373)
            ·
              refine ⟨5835256434656047427085515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15560683825749459805561373 5835256434656047427085515)
              ·
                refine ⟨8752884651984071140628273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835256434656047427085515 8752884651984071140628273)
                ·
                  refine ⟨6564663488988053355471205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8752884651984071140628273 6564663488988053355471205)
                  ·
                    refine ⟨1230874404185260004150851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6564663488988053355471205 1230874404185260004150851)
                    ·
                      rfl

theorem cell23_7191358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_7191358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191358 prefixEnd_7191358 := by exact prefixLift 7191358
  have htrace : WordTrace (prefixWord ++ tailWord_7191358) baseStart_7191358 baseEnd_7191358 := by
    simpa [prefixWord, tailWord_7191358, baseEnd_7191358] using wordTrace_append hprefix tailTrace_7191358
  have hstable : (prefixWord ++ tailWord_7191358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191358).length < 2 ^ (prefixWord ++ tailWord_7191358).sum := by decide
  have hdescent : baseEnd_7191358 < baseStart_7191358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191360 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_7191360 : Nat := 118140960795 + 7191360 * 2 ^ 59
def prefixEnd_7191360 : Nat := 4983230072969 + 3 ^ 40 * 7191360 * 2
def baseEnd_7191360 : Nat := 3692624239517089004627543

theorem tailTrace_7191360 : CollatzResearch.WordTrace tailWord_7191360 prefixEnd_7191360 3692624239517089004627543 := by
  unfold tailWord_7191360
  simp only [CollatzResearch.WordTrace]
  refine ⟨131145223613469190676093767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174860298151292254234791689 131145223613469190676093767)
  ·
    refine ⟨196717835420203786014140651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131145223613469190676093767 196717835420203786014140651)
    ·
      refine ⟨295076753130305679021210977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196717835420203786014140651 295076753130305679021210977)
      ·
        refine ⟨221307564847729259265908233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295076753130305679021210977 221307564847729259265908233)
        ·
          refine ⟨165980673635796944449431175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221307564847729259265908233 165980673635796944449431175)
          ·
            refine ⟨248971010453695416674146763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165980673635796944449431175 248971010453695416674146763)
            ·
              refine ⟨373456515680543125011220145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248971010453695416674146763 373456515680543125011220145)
              ·
                refine ⟨280092386760407343758415109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373456515680543125011220145 280092386760407343758415109)
                ·
                  refine ⟨52517322517576376954702833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280092386760407343758415109 52517322517576376954702833)
                  ·
                    refine ⟨39387991888182282716027125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52517322517576376954702833 39387991888182282716027125)
                    ·
                      refine ⟨3692624239517089004627543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39387991888182282716027125 3692624239517089004627543)
                      ·
                        rfl

theorem cell23_7191360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_7191360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191360 prefixEnd_7191360 := by exact prefixLift 7191360
  have htrace : WordTrace (prefixWord ++ tailWord_7191360) baseStart_7191360 baseEnd_7191360 := by
    simpa [prefixWord, tailWord_7191360, baseEnd_7191360] using wordTrace_append hprefix tailTrace_7191360
  have hstable : (prefixWord ++ tailWord_7191360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191360).length < 2 ^ (prefixWord ++ tailWord_7191360).sum := by decide
  have hdescent : baseEnd_7191360 < baseStart_7191360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191370 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_7191370 : Nat := 118140960795 + 7191370 * 2 ^ 59
def prefixEnd_7191370 : Nat := 4983230072969 + 3 ^ 40 * 7191370 * 2
def baseEnd_7191370 : Nat := 3692629374323633965502497

theorem tailTrace_7191370 : CollatzResearch.WordTrace tailWord_7191370 prefixEnd_7191370 3692629374323633965502497 := by
  unfold tailWord_7191370
  simp only [CollatzResearch.WordTrace]
  refine ⟨65572702989225538265012891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174860541304601435373367709 65572702989225538265012891)
  ·
    refine ⟨98359054483838307397519337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65572702989225538265012891 98359054483838307397519337)
    ·
      refine ⟨73769290862878730548139503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98359054483838307397519337 73769290862878730548139503)
      ·
        refine ⟨110653936294318095822209255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73769290862878730548139503 110653936294318095822209255)
        ·
          refine ⟨165980904441477143733313883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110653936294318095822209255 165980904441477143733313883)
          ·
            refine ⟨248971356662215715599970825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165980904441477143733313883 248971356662215715599970825)
            ·
              refine ⟨186728517496661786699978119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248971356662215715599970825 186728517496661786699978119)
              ·
                refine ⟨280092776244992680049967179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186728517496661786699978119 280092776244992680049967179)
                ·
                  refine ⟨420139164367489020074950769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280092776244992680049967179 420139164367489020074950769)
                  ·
                    refine ⟨315104373275616765056213077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 420139164367489020074950769 315104373275616765056213077)
                    ·
                      refine ⟨3692629374323633965502497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 315104373275616765056213077 3692629374323633965502497)
                      ·
                        rfl

theorem cell23_7191370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_7191370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191370 prefixEnd_7191370 := by exact prefixLift 7191370
  have htrace : WordTrace (prefixWord ++ tailWord_7191370) baseStart_7191370 baseEnd_7191370 := by
    simpa [prefixWord, tailWord_7191370, baseEnd_7191370] using wordTrace_append hprefix tailTrace_7191370
  have hstable : (prefixWord ++ tailWord_7191370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191370).length < 2 ^ (prefixWord ++ tailWord_7191370).sum := by decide
  have hdescent : baseEnd_7191370 < baseStart_7191370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191374 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_7191374 : Nat := 118140960795 + 7191374 * 2 ^ 59
def prefixEnd_7191374 : Nat := 4983230072969 + 3 ^ 40 * 7191374 * 2
def baseEnd_7191374 : Nat := 3692631428246251949852479

theorem tailTrace_7191374 : CollatzResearch.WordTrace tailWord_7191374 prefixEnd_7191374 3692631428246251949852479 := by
  unfold tailWord_7191374
  simp only [CollatzResearch.WordTrace]
  refine ⟨32786369731110957717899647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174860638565925107828798117 32786369731110957717899647)
  ·
    refine ⟨49179554596666436576849471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32786369731110957717899647 49179554596666436576849471)
    ·
      refine ⟨73769331894999654865274207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49179554596666436576849471 73769331894999654865274207)
      ·
        refine ⟨110653997842499482297911311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73769331894999654865274207 110653997842499482297911311)
        ·
          refine ⟨165980996763749223446866967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110653997842499482297911311 165980996763749223446866967)
          ·
            refine ⟨248971495145623835170300451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165980996763749223446866967 248971495145623835170300451)
            ·
              refine ⟨373457242718435752755450677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248971495145623835170300451 373457242718435752755450677)
              ·
                refine ⟨35011616504853351820823501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 373457242718435752755450677 35011616504853351820823501)
                ·
                  refine ⟨13129356189320006932808813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35011616504853351820823501 13129356189320006932808813)
                  ·
                    refine ⟨4923508570995002599803305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13129356189320006932808813 4923508570995002599803305)
                    ·
                      refine ⟨3692631428246251949852479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923508570995002599803305 3692631428246251949852479)
                      ·
                        rfl

theorem cell23_7191374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_7191374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191374 prefixEnd_7191374 := by exact prefixLift 7191374
  have htrace : WordTrace (prefixWord ++ tailWord_7191374) baseStart_7191374 baseEnd_7191374 := by
    simpa [prefixWord, tailWord_7191374, baseEnd_7191374] using wordTrace_append hprefix tailTrace_7191374
  have hstable : (prefixWord ++ tailWord_7191374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191374).length < 2 ^ (prefixWord ++ tailWord_7191374).sum := by decide
  have hdescent : baseEnd_7191374 < baseStart_7191374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191621 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 3]
def baseStart_7191621 : Nat := 118140960795 + 7191621 * 2 ^ 59
def prefixEnd_7191621 : Nat := 4983230072969 + 3 ^ 40 * 7191621 * 2
def baseEnd_7191621 : Nat := 3692758257967912483463843

theorem tailTrace_7191621 : CollatzResearch.WordTrace tailWord_7191621 prefixEnd_7191621 3692758257967912483463843 := by
  unfold tailWord_7191621
  simp only [CollatzResearch.WordTrace]
  refine ⟨262299966678992822927438717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174866644452661881951625811 262299966678992822927438717)
  ·
    refine ⟨98362487504622308597789519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262299966678992822927438717 98362487504622308597789519)
    ·
      refine ⟨147543731256933462896684279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98362487504622308597789519 147543731256933462896684279)
      ·
        refine ⟨221315596885400194345026419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147543731256933462896684279 221315596885400194345026419)
        ·
          refine ⟨331973395328100291517539629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221315596885400194345026419 331973395328100291517539629)
          ·
            refine ⟨124490023248037609319077361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331973395328100291517539629 124490023248037609319077361)
            ·
              refine ⟨93367517436028206989308021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124490023248037609319077361 93367517436028206989308021)
              ·
                refine ⟨8753204759627644405247627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93367517436028206989308021 8753204759627644405247627)
                ·
                  refine ⟨13129807139441466607871441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8753204759627644405247627 13129807139441466607871441)
                  ·
                    refine ⟨9847355354581099955903581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13129807139441466607871441 9847355354581099955903581)
                    ·
                      refine ⟨3692758257967912483463843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9847355354581099955903581 3692758257967912483463843)
                      ·
                        rfl

theorem cell23_7191621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_7191621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191621 prefixEnd_7191621 := by exact prefixLift 7191621
  have htrace : WordTrace (prefixWord ++ tailWord_7191621) baseStart_7191621 baseEnd_7191621 := by
    simpa [prefixWord, tailWord_7191621, baseEnd_7191621] using wordTrace_append hprefix tailTrace_7191621
  have hstable : (prefixWord ++ tailWord_7191621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191621).length < 2 ^ (prefixWord ++ tailWord_7191621).sum := by decide
  have hdescent : baseEnd_7191621 < baseStart_7191621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191629 : List Nat := [1, 6, 1, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_7191629 : Nat := 118140960795 + 7191629 * 2 ^ 59
def prefixEnd_7191629 : Nat := 4983230072969 + 3 ^ 40 * 7191629 * 2
def baseEnd_7191629 : Nat := 3692762365813148452163807

theorem tailTrace_7191629 : CollatzResearch.WordTrace tailWord_7191629 prefixEnd_7191629 3692762365813148452163807 := by
  unfold tailWord_7191629
  simp only [CollatzResearch.WordTrace]
  refine ⟨262300258462963840293729941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174866838975309226862486627 262300258462963840293729941)
  ·
    refine ⟨12295324615451430013768591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 262300258462963840293729941 12295324615451430013768591)
    ·
      refine ⟨18442986923177145020652887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12295324615451430013768591 18442986923177145020652887)
      ·
        refine ⟨27664480384765717530979331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18442986923177145020652887 27664480384765717530979331)
        ·
          refine ⟨41496720577148576296468997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27664480384765717530979331 41496720577148576296468997)
          ·
            refine ⟨7780635108215358055587937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41496720577148576296468997 7780635108215358055587937)
            ·
              refine ⟨5835476331161518541690953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7780635108215358055587937 5835476331161518541690953)
              ·
                refine ⟨4376607248371138906268215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5835476331161518541690953 4376607248371138906268215)
                ·
                  refine ⟨6564910872556708359402323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376607248371138906268215 6564910872556708359402323)
                  ·
                    refine ⟨9847366308835062539103485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564910872556708359402323 9847366308835062539103485)
                    ·
                      refine ⟨3692762365813148452163807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9847366308835062539103485 3692762365813148452163807)
                      ·
                        rfl

theorem cell23_7191629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_7191629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191629 prefixEnd_7191629 := by exact prefixLift 7191629
  have htrace : WordTrace (prefixWord ++ tailWord_7191629) baseStart_7191629 baseEnd_7191629 := by
    simpa [prefixWord, tailWord_7191629, baseEnd_7191629] using wordTrace_append hprefix tailTrace_7191629
  have hstable : (prefixWord ++ tailWord_7191629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191629).length < 2 ^ (prefixWord ++ tailWord_7191629).sum := by decide
  have hdescent : baseEnd_7191629 < baseStart_7191629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191651 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 3]
def baseStart_7191651 : Nat := 118140960795 + 7191651 * 2 ^ 59
def prefixEnd_7191651 : Nat := 4983230072969 + 3 ^ 40 * 7191651 * 2
def baseEnd_7191651 : Nat := 3692773662387547366088705

theorem tailTrace_7191651 : CollatzResearch.WordTrace tailWord_7191651 prefixEnd_7191651 3692773662387547366088705 := by
  unfold tailWord_7191651
  simp only [CollatzResearch.WordTrace]
  refine ⟨262301060868884138051030807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174867373912589425367353871 262301060868884138051030807)
  ·
    refine ⟨393451591303326207076546211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262301060868884138051030807 393451591303326207076546211)
    ·
      refine ⟨590177386954989310614819317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393451591303326207076546211 590177386954989310614819317)
      ·
        refine ⟨55329130027030247870139311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 590177386954989310614819317 55329130027030247870139311)
        ·
          refine ⟨82993695040545371805208967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55329130027030247870139311 82993695040545371805208967)
          ·
            refine ⟨124490542560818057707813451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82993695040545371805208967 124490542560818057707813451)
            ·
              refine ⟨186735813841227086561720177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124490542560818057707813451 186735813841227086561720177)
              ·
                refine ⟨140051860380920314921290133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186735813841227086561720177 140051860380920314921290133)
                ·
                  refine ⟨6564930955355639761935475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140051860380920314921290133 6564930955355639761935475)
                  ·
                    refine ⟨9847396433033459642903213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564930955355639761935475 9847396433033459642903213)
                    ·
                      refine ⟨3692773662387547366088705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9847396433033459642903213 3692773662387547366088705)
                      ·
                        rfl

theorem cell23_7191651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_7191651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191651 prefixEnd_7191651 := by exact prefixLift 7191651
  have htrace : WordTrace (prefixWord ++ tailWord_7191651) baseStart_7191651 baseEnd_7191651 := by
    simpa [prefixWord, tailWord_7191651, baseEnd_7191651] using wordTrace_append hprefix tailTrace_7191651
  have hstable : (prefixWord ++ tailWord_7191651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191651).length < 2 ^ (prefixWord ++ tailWord_7191651).sum := by decide
  have hdescent : baseEnd_7191651 < baseStart_7191651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191664 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_7191664 : Nat := 118140960795 + 7191664 * 2 ^ 59
def prefixEnd_7191664 : Nat := 4983230072969 + 3 ^ 40 * 7191664 * 2
def baseEnd_7191664 : Nat := 3692780337636055815226145

theorem tailTrace_7191664 : CollatzResearch.WordTrace tailWord_7191664 prefixEnd_7191664 3692780337636055815226145 := by
  unfold tailWord_7191664
  simp only [CollatzResearch.WordTrace]
  refine ⟨131150767508918520635627023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174867690011891360847502697 131150767508918520635627023)
  ·
    refine ⟨196726151263377780953440535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131150767508918520635627023 196726151263377780953440535)
    ·
      refine ⟨295089226895066671430160803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196726151263377780953440535 295089226895066671430160803)
      ·
        refine ⟨442633840342600007145241205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295089226895066671430160803 442633840342600007145241205)
        ·
          refine ⟨41496922532118750669866363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 442633840342600007145241205 41496922532118750669866363)
          ·
            refine ⟨62245383798178126004799545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41496922532118750669866363 62245383798178126004799545)
            ·
              refine ⟨46684037848633594503599659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62245383798178126004799545 46684037848633594503599659)
              ·
                refine ⟨70026056772950391755399489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46684037848633594503599659 70026056772950391755399489)
                ·
                  refine ⟨52519542579712793816549617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70026056772950391755399489 52519542579712793816549617)
                  ·
                    refine ⟨39389656934784595362412213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52519542579712793816549617 39389656934784595362412213)
                    ·
                      refine ⟨3692780337636055815226145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39389656934784595362412213 3692780337636055815226145)
                      ·
                        rfl

theorem cell23_7191664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_7191664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191664 prefixEnd_7191664 := by exact prefixLift 7191664
  have htrace : WordTrace (prefixWord ++ tailWord_7191664) baseStart_7191664 baseEnd_7191664 := by
    simpa [prefixWord, tailWord_7191664, baseEnd_7191664] using wordTrace_append hprefix tailTrace_7191664
  have hstable : (prefixWord ++ tailWord_7191664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191664).length < 2 ^ (prefixWord ++ tailWord_7191664).sum := by decide
  have hdescent : baseEnd_7191664 < baseStart_7191664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191669 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7191669 : Nat := 118140960795 + 7191669 * 2 ^ 59
def prefixEnd_7191669 : Nat := 4983230072969 + 3 ^ 40 * 7191669 * 2
def baseEnd_7191669 : Nat := 3692782905039328295663623

theorem tailTrace_7191669 : CollatzResearch.WordTrace tailWord_7191669 prefixEnd_7191669 3692782905039328295663623 := by
  unfold tailWord_7191669
  simp only [CollatzResearch.WordTrace]
  refine ⟨262301717382818927125186061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174867811588545951416790707 262301717382818927125186061)
  ·
    refine ⟨98363144018557097671944773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262301717382818927125186061 98363144018557097671944773)
    ·
      refine ⟨18443089503479455813489645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98363144018557097671944773 18443089503479455813489645)
      ·
        refine ⟨6916158563804795930058617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18443089503479455813489645 6916158563804795930058617)
        ·
          refine ⟨5187118922853596947543963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6916158563804795930058617 5187118922853596947543963)
          ·
            refine ⟨7780678384280395421315945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5187118922853596947543963 7780678384280395421315945)
            ·
              refine ⟨5835508788210296565986959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7780678384280395421315945 5835508788210296565986959)
              ·
                refine ⟨8753263182315444848980439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835508788210296565986959 8753263182315444848980439)
                ·
                  refine ⟨13129894773473167273470659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8753263182315444848980439 13129894773473167273470659)
                  ·
                    refine ⟨19694842160209750910205989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13129894773473167273470659 19694842160209750910205989)
                    ·
                      refine ⟨3692782905039328295663623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19694842160209750910205989 3692782905039328295663623)
                      ·
                        rfl

theorem cell23_7191669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7191669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191669 prefixEnd_7191669 := by exact prefixLift 7191669
  have htrace : WordTrace (prefixWord ++ tailWord_7191669) baseStart_7191669 baseEnd_7191669 := by
    simpa [prefixWord, tailWord_7191669, baseEnd_7191669] using wordTrace_append hprefix tailTrace_7191669
  have hstable : (prefixWord ++ tailWord_7191669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191669).length < 2 ^ (prefixWord ++ tailWord_7191669).sum := by decide
  have hdescent : baseEnd_7191669 < baseStart_7191669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191691 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 3, 4, 2]
def baseStart_7191691 : Nat := 118140960795 + 7191691 * 2 ^ 59
def prefixEnd_7191691 : Nat := 4983230072969 + 3 ^ 40 * 7191691 * 2
def baseEnd_7191691 : Nat := 3692794201613727209588521

theorem tailTrace_7191691 : CollatzResearch.WordTrace tailWord_7191691 prefixEnd_7191691 3692794201613727209588521 := by
  unfold tailWord_7191691
  simp only [CollatzResearch.WordTrace]
  refine ⟨262302519788739224882486927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174868346525826149921657951 262302519788739224882486927)
  ·
    refine ⟨393453779683108837323730391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262302519788739224882486927 393453779683108837323730391)
    ·
      refine ⟨590180669524663255985595587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393453779683108837323730391 590180669524663255985595587)
      ·
        refine ⟨885271004286994883978393381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590180669524663255985595587 885271004286994883978393381)
        ·
          refine ⟨165988313303811540745948759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 885271004286994883978393381 165988313303811540745948759)
          ·
            refine ⟨248982469955717311118923139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165988313303811540745948759 248982469955717311118923139)
            ·
              refine ⟨373473704933575966678384709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248982469955717311118923139 373473704933575966678384709)
              ·
                refine ⟨70026319675045493752197133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373473704933575966678384709 70026319675045493752197133)
                ·
                  refine ⟨26259869878142060157073925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70026319675045493752197133 26259869878142060157073925)
                  ·
                    refine ⟨4923725602151636279451361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26259869878142060157073925 4923725602151636279451361)
                    ·
                      refine ⟨3692794201613727209588521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923725602151636279451361 3692794201613727209588521)
                      ·
                        rfl

theorem cell23_7191691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 4, 2].length) (baseStart_7191691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191691 prefixEnd_7191691 := by exact prefixLift 7191691
  have htrace : WordTrace (prefixWord ++ tailWord_7191691) baseStart_7191691 baseEnd_7191691 := by
    simpa [prefixWord, tailWord_7191691, baseEnd_7191691] using wordTrace_append hprefix tailTrace_7191691
  have hstable : (prefixWord ++ tailWord_7191691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191691).length < 2 ^ (prefixWord ++ tailWord_7191691).sum := by decide
  have hdescent : baseEnd_7191691 < baseStart_7191691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191741 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_7191741 : Nat := 118140960795 + 7191741 * 2 ^ 59
def prefixEnd_7191741 : Nat := 4983230072969 + 3 ^ 40 * 7191741 * 2
def baseEnd_7191741 : Nat := 3692819875646452013963291

theorem tailTrace_7191741 : CollatzResearch.WordTrace tailWord_7191741 prefixEnd_7191741 3692819875646452013963291 := by
  unfold tailWord_7191741
  simp only [CollatzResearch.WordTrace]
  refine ⟨262304343438558083421807077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174869562292372055614538051 262304343438558083421807077)
  ·
    refine ⟨49182064394729640641588827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262304343438558083421807077 49182064394729640641588827)
    ·
      refine ⟨73773096592094460962383241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49182064394729640641588827 73773096592094460962383241)
      ·
        refine ⟨55329822444070845721787431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73773096592094460962383241 55329822444070845721787431)
        ·
          refine ⟨82994733666106268582681147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55329822444070845721787431 82994733666106268582681147)
          ·
            refine ⟨124492100499159402874021721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82994733666106268582681147 124492100499159402874021721)
            ·
              refine ⟨93369075374369552155516291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124492100499159402874021721 93369075374369552155516291)
              ·
                refine ⟨140053613061554328233274437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93369075374369552155516291 140053613061554328233274437)
                ·
                  refine ⟨26260052449041436543738957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140053613061554328233274437 26260052449041436543738957)
                  ·
                    refine ⟨9847519668390538703902109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26260052449041436543738957 9847519668390538703902109)
                    ·
                      refine ⟨3692819875646452013963291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9847519668390538703902109 3692819875646452013963291)
                      ·
                        rfl

theorem cell23_7191741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_7191741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191741 prefixEnd_7191741 := by exact prefixLift 7191741
  have htrace : WordTrace (prefixWord ++ tailWord_7191741) baseStart_7191741 baseEnd_7191741 := by
    simpa [prefixWord, tailWord_7191741, baseEnd_7191741] using wordTrace_append hprefix tailTrace_7191741
  have hstable : (prefixWord ++ tailWord_7191741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191741).length < 2 ^ (prefixWord ++ tailWord_7191741).sum := by decide
  have hdescent : baseEnd_7191741 < baseStart_7191741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191888 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 2, 6, 2]
def baseStart_7191888 : Nat := 118140960795 + 7191888 * 2 ^ 59
def prefixEnd_7191888 : Nat := 4983230072969 + 3 ^ 40 * 7191888 * 2
def baseEnd_7191888 : Nat := 3692895357302662938825115

theorem tailTrace_7191888 : CollatzResearch.WordTrace tailWord_7191888 prefixEnd_7191888 3692895357302662938825115 := by
  unfold tailWord_7191888
  simp only [CollatzResearch.WordTrace]
  refine ⟨131154852484512763763704159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174873136646017018351605545 131154852484512763763704159)
  ·
    refine ⟨196732278726769145645556239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131154852484512763763704159 196732278726769145645556239)
    ·
      refine ⟨295098418090153718468334359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196732278726769145645556239 295098418090153718468334359)
      ·
        refine ⟨442647627135230577702501539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295098418090153718468334359 442647627135230577702501539)
        ·
          refine ⟨663971440702845866553752309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442647627135230577702501539 663971440702845866553752309)
          ·
            refine ⟨62247322565891799989414279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 663971440702845866553752309 62247322565891799989414279)
            ·
              refine ⟨93370983848837699984121419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62247322565891799989414279 93370983848837699984121419)
              ·
                refine ⟨140056475773256549976182129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93370983848837699984121419 140056475773256549976182129)
                ·
                  refine ⟨105042356829942412482136597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140056475773256549976182129 105042356829942412482136597)
                  ·
                    refine ⟨4923860476403550585100153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105042356829942412482136597 4923860476403550585100153)
                    ·
                      refine ⟨3692895357302662938825115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923860476403550585100153 3692895357302662938825115)
                      ·
                        rfl

theorem cell23_7191888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 6, 2].length) (baseStart_7191888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191888 prefixEnd_7191888 := by exact prefixLift 7191888
  have htrace : WordTrace (prefixWord ++ tailWord_7191888) baseStart_7191888 baseEnd_7191888 := by
    simpa [prefixWord, tailWord_7191888, baseEnd_7191888] using wordTrace_append hprefix tailTrace_7191888
  have hstable : (prefixWord ++ tailWord_7191888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191888).length < 2 ^ (prefixWord ++ tailWord_7191888).sum := by decide
  have hdescent : baseEnd_7191888 < baseStart_7191888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191891 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 5]
def baseStart_7191891 : Nat := 118140960795 + 7191891 * 2 ^ 59
def prefixEnd_7191891 : Nat := 4983230072969 + 3 ^ 40 * 7191891 * 2
def baseEnd_7191891 : Nat := 3692896897744626427087601

theorem tailTrace_7191891 : CollatzResearch.WordTrace tailWord_7191891 prefixEnd_7191891 3692896897744626427087601 := by
  unfold tailWord_7191891
  simp only [CollatzResearch.WordTrace]
  refine ⟨262309814388014659039767527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174873209592009772693178351 262309814388014659039767527)
  ·
    refine ⟨393464721582021988559651291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262309814388014659039767527 393464721582021988559651291)
    ·
      refine ⟨590197082373032982839476937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393464721582021988559651291 590197082373032982839476937)
      ·
        refine ⟨442647811779774737129607703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590197082373032982839476937 442647811779774737129607703)
        ·
          refine ⟨663971717669662105694411555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442647811779774737129607703 663971717669662105694411555)
          ·
            refine ⟨995957576504493158541617333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663971717669662105694411555 995957576504493158541617333)
            ·
              refine ⟨93371022797296233613276625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 995957576504493158541617333 93371022797296233613276625)
              ·
                refine ⟨70028267097972175209957469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93371022797296233613276625 70028267097972175209957469)
                ·
                  refine ⟨26260600161739565703734051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70028267097972175209957469 26260600161739565703734051)
                  ·
                    refine ⟨39390900242609348555601077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26260600161739565703734051 39390900242609348555601077)
                    ·
                      refine ⟨3692896897744626427087601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39390900242609348555601077 3692896897744626427087601)
                      ·
                        rfl

theorem cell23_7191891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_7191891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191891 prefixEnd_7191891 := by exact prefixLift 7191891
  have htrace : WordTrace (prefixWord ++ tailWord_7191891) baseStart_7191891 baseEnd_7191891 := by
    simpa [prefixWord, tailWord_7191891, baseEnd_7191891] using wordTrace_append hprefix tailTrace_7191891
  have hstable : (prefixWord ++ tailWord_7191891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191891).length < 2 ^ (prefixWord ++ tailWord_7191891).sum := by decide
  have hdescent : baseEnd_7191891 < baseStart_7191891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191898 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_7191898 : Nat := 118140960795 + 7191898 * 2 ^ 59
def prefixEnd_7191898 : Nat := 4983230072969 + 3 ^ 40 * 7191898 * 2
def baseEnd_7191898 : Nat := 1230966830703069299900023

theorem tailTrace_7191898 : CollatzResearch.WordTrace tailWord_7191898 prefixEnd_7191898 1230966830703069299900023 := by
  unfold tailWord_7191898
  simp only [CollatzResearch.WordTrace]
  refine ⟨65577517424747324808818087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174873379799326199490181565 65577517424747324808818087)
  ·
    refine ⟨98366276137120987213227131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65577517424747324808818087 98366276137120987213227131)
    ·
      refine ⟨147549414205681480819840697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98366276137120987213227131 147549414205681480819840697)
      ·
        refine ⟨110662060654261110614880523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147549414205681480819840697 110662060654261110614880523)
        ·
          refine ⟨165993090981391665922320785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110662060654261110614880523 165993090981391665922320785)
          ·
            refine ⟨124494818236043749441740589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165993090981391665922320785 124494818236043749441740589)
            ·
              refine ⟨46685556838516406040652721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124494818236043749441740589 46685556838516406040652721)
              ·
                refine ⟨35014167628887304530489541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46685556838516406040652721 35014167628887304530489541)
                ·
                  refine ⟨6565156430416369599466789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35014167628887304530489541 6565156430416369599466789)
                  ·
                    refine ⟨1230966830703069299900023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6565156430416369599466789 1230966830703069299900023)
                    ·
                      rfl

theorem cell23_7191898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_7191898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191898 prefixEnd_7191898 := by exact prefixLift 7191898
  have htrace : WordTrace (prefixWord ++ tailWord_7191898) baseStart_7191898 baseEnd_7191898 := by
    simpa [prefixWord, tailWord_7191898, baseEnd_7191898] using wordTrace_append hprefix tailTrace_7191898
  have hstable : (prefixWord ++ tailWord_7191898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191898).length < 2 ^ (prefixWord ++ tailWord_7191898).sum := by decide
  have hdescent : baseEnd_7191898 < baseStart_7191898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191905 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_7191905 : Nat := 118140960795 + 7191905 * 2 ^ 59
def prefixEnd_7191905 : Nat := 4983230072969 + 3 ^ 40 * 7191905 * 2
def baseEnd_7191905 : Nat := 3692904086473789372312537

theorem tailTrace_7191905 : CollatzResearch.WordTrace tailWord_7191905 prefixEnd_7191905 3692904086473789372312537 := by
  unfold tailWord_7191905
  simp only [CollatzResearch.WordTrace]
  refine ⟨262310325009963939430777169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174873550006642626287184779 262310325009963939430777169)
  ·
    refine ⟨196732743757472954573082877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262310325009963939430777169 196732743757472954573082877)
    ·
      refine ⟨73774778909052357964906079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196732743757472954573082877 73774778909052357964906079)
      ·
        refine ⟨110662168363578536947359119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73774778909052357964906079 110662168363578536947359119)
        ·
          refine ⟨165993252545367805421038679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110662168363578536947359119 165993252545367805421038679)
          ·
            refine ⟨248989878818051708131558019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165993252545367805421038679 248989878818051708131558019)
            ·
              refine ⟨373484818227077562197337029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248989878818051708131558019 373484818227077562197337029)
              ·
                refine ⟨70028403417577042912000693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373484818227077562197337029 70028403417577042912000693)
                ·
                  refine ⟨6565162820397847773000065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70028403417577042912000693 6565162820397847773000065)
                  ·
                    refine ⟨4923872115298385829750049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6565162820397847773000065 4923872115298385829750049)
                    ·
                      refine ⟨3692904086473789372312537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923872115298385829750049 3692904086473789372312537)
                      ·
                        rfl

theorem cell23_7191905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_7191905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191905 prefixEnd_7191905 := by exact prefixLift 7191905
  have htrace : WordTrace (prefixWord ++ tailWord_7191905) baseStart_7191905 baseEnd_7191905 := by
    simpa [prefixWord, tailWord_7191905, baseEnd_7191905] using wordTrace_append hprefix tailTrace_7191905
  have hstable : (prefixWord ++ tailWord_7191905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191905).length < 2 ^ (prefixWord ++ tailWord_7191905).sum := by decide
  have hdescent : baseEnd_7191905 < baseStart_7191905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191908 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_7191908 : Nat := 118140960795 + 7191908 * 2 ^ 59
def prefixEnd_7191908 : Nat := 4983230072969 + 3 ^ 40 * 7191908 * 2
def baseEnd_7191908 : Nat := 3692905626915752860575023

theorem tailTrace_7191908 : CollatzResearch.WordTrace tailWord_7191908 prefixEnd_7191908 3692905626915752860575023 := by
  unfold tailWord_7191908
  simp only [CollatzResearch.WordTrace]
  refine ⟨131155217214476535471568189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174873622952635380628757585 131155217214476535471568189)
  ·
    refine ⟨49183206455428700801838071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131155217214476535471568189 49183206455428700801838071)
    ·
      refine ⟨73774809683143051202757107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49183206455428700801838071 73774809683143051202757107)
      ·
        refine ⟨110662214524714576804135661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73774809683143051202757107 110662214524714576804135661)
        ·
          refine ⟨41498330446767966301550873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110662214524714576804135661 41498330446767966301550873)
          ·
            refine ⟨31123747835075974726163155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41498330446767966301550873 31123747835075974726163155)
            ·
              refine ⟨46685621752613962089244733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31123747835075974726163155 46685621752613962089244733)
              ·
                refine ⟨17507108157230235783466775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46685621752613962089244733 17507108157230235783466775)
                ·
                  refine ⟨26260662235845353675200163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17507108157230235783466775 26260662235845353675200163)
                  ·
                    refine ⟨39390993353768030512800245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26260662235845353675200163 39390993353768030512800245)
                    ·
                      refine ⟨3692905626915752860575023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39390993353768030512800245 3692905626915752860575023)
                      ·
                        rfl

theorem cell23_7191908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_7191908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191908 prefixEnd_7191908 := by exact prefixLift 7191908
  have htrace : WordTrace (prefixWord ++ tailWord_7191908) baseStart_7191908 baseEnd_7191908 := by
    simpa [prefixWord, tailWord_7191908, baseEnd_7191908] using wordTrace_append hprefix tailTrace_7191908
  have hstable : (prefixWord ++ tailWord_7191908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191908).length < 2 ^ (prefixWord ++ tailWord_7191908).sum := by decide
  have hdescent : baseEnd_7191908 < baseStart_7191908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7191931 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 6]
def baseStart_7191931 : Nat := 118140960795 + 7191931 * 2 ^ 59
def prefixEnd_7191931 : Nat := 4983230072969 + 3 ^ 40 * 7191931 * 2
def baseEnd_7191931 : Nat := 3692917436970806270587417

theorem tailTrace_7191931 : CollatzResearch.WordTrace tailWord_7191931 prefixEnd_7191931 3692917436970806270587417 := by
  unfold tailWord_7191931
  simp only [CollatzResearch.WordTrace]
  refine ⟨262311273307869745871223647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174874182205246497247482431 262311273307869745871223647)
  ·
    refine ⟨393466909961804618806835471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262311273307869745871223647 393466909961804618806835471)
    ·
      refine ⟨590200364942706928210253207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393466909961804618806835471 590200364942706928210253207)
      ·
        refine ⟨885300547414060392315379811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590200364942706928210253207 885300547414060392315379811)
        ·
          refine ⟨1327950821121090588473069717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885300547414060392315379811 1327950821121090588473069717)
          ·
            refine ⟨62247694740051121334675143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1327950821121090588473069717 62247694740051121334675143)
            ·
              refine ⟨93371542110076682002012715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62247694740051121334675143 93371542110076682002012715)
              ·
                refine ⟨140057313165115023003019073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93371542110076682002012715 140057313165115023003019073)
                ·
                  refine ⟨105042984873836267252264305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140057313165115023003019073 105042984873836267252264305)
                  ·
                    refine ⟨78782238655377200439198229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105042984873836267252264305 78782238655377200439198229)
                    ·
                      refine ⟨3692917436970806270587417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78782238655377200439198229 3692917436970806270587417)
                      ·
                        rfl

theorem cell23_7191931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_7191931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7191931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7191931 prefixEnd_7191931 := by exact prefixLift 7191931
  have htrace : WordTrace (prefixWord ++ tailWord_7191931) baseStart_7191931 baseEnd_7191931 := by
    simpa [prefixWord, tailWord_7191931, baseEnd_7191931] using wordTrace_append hprefix tailTrace_7191931
  have hstable : (prefixWord ++ tailWord_7191931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7191931).length < 2 ^ (prefixWord ++ tailWord_7191931).sum := by decide
  have hdescent : baseEnd_7191931 < baseStart_7191931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7191931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192008 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_7192008 : Nat := 118140960795 + 7192008 * 2 ^ 59
def prefixEnd_7192008 : Nat := 4983230072969 + 3 ^ 40 * 7192008 * 2
def baseEnd_7192008 : Nat := 3692956974981202469324563

theorem tailTrace_7192008 : CollatzResearch.WordTrace tailWord_7192008 prefixEnd_7192008 3692956974981202469324563 := by
  unfold tailWord_7192008
  simp only [CollatzResearch.WordTrace]
  refine ⟨131157040864295394010888339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174876054485727192014517785 131157040864295394010888339)
  ·
    refine ⟨196735561296443091016332509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131157040864295394010888339 196735561296443091016332509)
    ·
      refine ⟨73775835486166159131124691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196735561296443091016332509 73775835486166159131124691)
      ·
        refine ⟨110663753229249238696687037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73775835486166159131124691 110663753229249238696687037)
        ·
          refine ⟨41498907460968464511257639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110663753229249238696687037 41498907460968464511257639)
          ·
            refine ⟨62248361191452696766886459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41498907460968464511257639 62248361191452696766886459)
            ·
              refine ⟨93372541787179045150329689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62248361191452696766886459 93372541787179045150329689)
              ·
                refine ⟨70029406340384283862747267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93372541787179045150329689 70029406340384283862747267)
                ·
                  refine ⟨105044109510576425794120901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70029406340384283862747267 105044109510576425794120901)
                  ·
                    refine ⟨19695770533233079836397669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105044109510576425794120901 19695770533233079836397669)
                    ·
                      refine ⟨3692956974981202469324563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19695770533233079836397669 3692956974981202469324563)
                      ·
                        rfl

theorem cell23_7192008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_7192008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192008 prefixEnd_7192008 := by exact prefixLift 7192008
  have htrace : WordTrace (prefixWord ++ tailWord_7192008) baseStart_7192008 baseEnd_7192008 := by
    simpa [prefixWord, tailWord_7192008, baseEnd_7192008] using wordTrace_append hprefix tailTrace_7192008
  have hstable : (prefixWord ++ tailWord_7192008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192008).length < 2 ^ (prefixWord ++ tailWord_7192008).sum := by decide
  have hdescent : baseEnd_7192008 < baseStart_7192008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192012 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 1, 4, 2]
def baseStart_7192012 : Nat := 118140960795 + 7192012 * 2 ^ 59
def prefixEnd_7192012 : Nat := 4983230072969 + 3 ^ 40 * 7192012 * 2
def baseEnd_7192012 : Nat := 3692959028903820453674545

theorem tailTrace_7192012 : CollatzResearch.WordTrace tailWord_7192012 prefixEnd_7192012 3692959028903820453674545 := by
  unfold tailWord_7192012
  simp only [CollatzResearch.WordTrace]
  refine ⟨131157113810288148352461145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174876151747050864469948193 131157113810288148352461145)
  ·
    refine ⟨98367835357716111264345859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131157113810288148352461145 98367835357716111264345859)
    ·
      refine ⟨147551753036574166896518789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98367835357716111264345859 147551753036574166896518789)
      ·
        refine ⟨27665953694357656293097273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147551753036574166896518789 27665953694357656293097273)
        ·
          refine ⟨20749465270768242219822955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27665953694357656293097273 20749465270768242219822955)
          ·
            refine ⟨31124197906152363329734433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20749465270768242219822955 31124197906152363329734433)
            ·
              refine ⟨23343148429614272497300825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31124197906152363329734433 23343148429614272497300825)
              ·
                refine ⟨17507361322210704372975619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23343148429614272497300825 17507361322210704372975619)
                ·
                  refine ⟨26261041983316056559463429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17507361322210704372975619 26261041983316056559463429)
                  ·
                    refine ⟨4923945371871760604899393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26261041983316056559463429 4923945371871760604899393)
                    ·
                      refine ⟨3692959028903820453674545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923945371871760604899393 3692959028903820453674545)
                      ·
                        rfl

theorem cell23_7192012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_7192012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192012 prefixEnd_7192012 := by exact prefixLift 7192012
  have htrace : WordTrace (prefixWord ++ tailWord_7192012) baseStart_7192012 baseEnd_7192012 := by
    simpa [prefixWord, tailWord_7192012, baseEnd_7192012] using wordTrace_append hprefix tailTrace_7192012
  have hstable : (prefixWord ++ tailWord_7192012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192012).length < 2 ^ (prefixWord ++ tailWord_7192012).sum := by decide
  have hdescent : baseEnd_7192012 < baseStart_7192012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192029 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_7192029 : Nat := 118140960795 + 7192029 * 2 ^ 59
def prefixEnd_7192029 : Nat := 4983230072969 + 3 ^ 40 * 7192029 * 2
def baseEnd_7192029 : Nat := 3692967758074946887161967

theorem tailTrace_7192029 : CollatzResearch.WordTrace tailWord_7192029 prefixEnd_7192029 3692967758074946887161967 := by
  unfold tailWord_7192029
  simp only [CollatzResearch.WordTrace]
  refine ⟨262314847661514708608291141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174876565107676472405527427 262314847661514708608291141)
  ·
    refine ⟨49184033936534007864054589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262314847661514708608291141 49184033936534007864054589)
    ·
      refine ⟨18444012726200252949020471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49184033936534007864054589 18444012726200252949020471)
      ·
        refine ⟨27666019089300379423530707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18444012726200252949020471 27666019089300379423530707)
        ·
          refine ⟨41499028633950569135296061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27666019089300379423530707 41499028633950569135296061)
          ·
            refine ⟨15562135737731463425736023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41499028633950569135296061 15562135737731463425736023)
            ·
              refine ⟨23343203606597195138604035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15562135737731463425736023 23343203606597195138604035)
              ·
                refine ⟨35014805409895792707906053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23343203606597195138604035 35014805409895792707906053)
                ·
                  refine ⟨6565276014355461132732385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35014805409895792707906053 6565276014355461132732385)
                  ·
                    refine ⟨4923957010766595849549289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6565276014355461132732385 4923957010766595849549289)
                    ·
                      refine ⟨3692967758074946887161967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923957010766595849549289 3692967758074946887161967)
                      ·
                        rfl

theorem cell23_7192029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_7192029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192029 prefixEnd_7192029 := by exact prefixLift 7192029
  have htrace : WordTrace (prefixWord ++ tailWord_7192029) baseStart_7192029 baseEnd_7192029 := by
    simpa [prefixWord, tailWord_7192029, baseEnd_7192029] using wordTrace_append hprefix tailTrace_7192029
  have hstable : (prefixWord ++ tailWord_7192029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192029).length < 2 ^ (prefixWord ++ tailWord_7192029).sum := by decide
  have hdescent : baseEnd_7192029 < baseStart_7192029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192035 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 7]
def baseStart_7192035 : Nat := 118140960795 + 7192035 * 2 ^ 59
def prefixEnd_7192035 : Nat := 4983230072969 + 3 ^ 40 * 7192035 * 2
def baseEnd_7192035 : Nat := 410330093217652651520771

theorem tailTrace_7192035 : CollatzResearch.WordTrace tailWord_7192035 prefixEnd_7192035 410330093217652651520771 := by
  unfold tailWord_7192035
  simp only [CollatzResearch.WordTrace]
  refine ⟨262315066499492971633009559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174876710999661981088673039 262315066499492971633009559)
  ·
    refine ⟨393472599749239457449514339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262315066499492971633009559 393472599749239457449514339)
    ·
      refine ⟨590208899623859186174271509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393472599749239457449514339 590208899623859186174271509)
      ·
        refine ⟨27666042169868399351918977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 590208899623859186174271509 27666042169868399351918977)
        ·
          refine ⟨20749531627401299513939233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27666042169868399351918977 20749531627401299513939233)
          ·
            refine ⟨15562148720550974635454425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20749531627401299513939233 15562148720550974635454425)
            ·
              refine ⟨11671611540413230976590819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15562148720550974635454425 11671611540413230976590819)
              ·
                refine ⟨17507417310619846464886229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11671611540413230976590819 17507417310619846464886229)
                ·
                  refine ⟨410330093217652651520771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17507417310619846464886229 410330093217652651520771)
                  ·
                    rfl

theorem cell23_7192035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 7].length) (baseStart_7192035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192035 prefixEnd_7192035 := by exact prefixLift 7192035
  have htrace : WordTrace (prefixWord ++ tailWord_7192035) baseStart_7192035 baseEnd_7192035 := by
    simpa [prefixWord, tailWord_7192035, baseEnd_7192035] using wordTrace_append hprefix tailTrace_7192035
  have hstable : (prefixWord ++ tailWord_7192035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192035).length < 2 ^ (prefixWord ++ tailWord_7192035).sum := by decide
  have hdescent : baseEnd_7192035 < baseStart_7192035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192046 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_7192046 : Nat := 118140960795 + 7192046 * 2 ^ 59
def prefixEnd_7192046 : Nat := 4983230072969 + 3 ^ 40 * 7192046 * 2
def baseEnd_7192046 : Nat := 3692976487246073320649389

theorem tailTrace_7192046 : CollatzResearch.WordTrace tailWord_7192046 prefixEnd_7192046 3692976487246073320649389 := by
  unfold tailWord_7192046
  simp only [CollatzResearch.WordTrace]
  refine ⟨32789433462806640063957499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174876978468302080341106661 32789433462806640063957499)
  ·
    refine ⟨49184150194209960095936249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32789433462806640063957499 49184150194209960095936249)
    ·
      refine ⟨36888112645657470071952187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49184150194209960095936249 36888112645657470071952187)
      ·
        refine ⟨55332168968486205107928281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36888112645657470071952187 55332168968486205107928281)
        ·
          refine ⟨41499126726364653830946211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55332168968486205107928281 41499126726364653830946211)
          ·
            refine ⟨62248690089546980746419317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41499126726364653830946211 62248690089546980746419317)
            ·
              refine ⟨5835814695895029444976811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62248690089546980746419317 5835814695895029444976811)
              ·
                refine ⟨8753722043842544167465217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835814695895029444976811 8753722043842544167465217)
                ·
                  refine ⟨6565291532881908125598913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8753722043842544167465217 6565291532881908125598913)
                  ·
                    refine ⟨4923968649661431094199185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6565291532881908125598913 4923968649661431094199185)
                    ·
                      refine ⟨3692976487246073320649389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4923968649661431094199185 3692976487246073320649389)
                      ·
                        rfl

theorem cell23_7192046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_7192046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192046 prefixEnd_7192046 := by exact prefixLift 7192046
  have htrace : WordTrace (prefixWord ++ tailWord_7192046) baseStart_7192046 baseEnd_7192046 := by
    simpa [prefixWord, tailWord_7192046, baseEnd_7192046] using wordTrace_append hprefix tailTrace_7192046
  have hstable : (prefixWord ++ tailWord_7192046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192046).length < 2 ^ (prefixWord ++ tailWord_7192046).sum := by decide
  have hdescent : baseEnd_7192046 < baseStart_7192046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192048 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 1, 7]
def baseStart_7192048 : Nat := 118140960795 + 7192048 * 2 ^ 59
def prefixEnd_7192048 : Nat := 4983230072969 + 3 ^ 40 * 7192048 * 2
def baseEnd_7192048 : Nat := 1230992504735794104274793

theorem tailTrace_7192048 : CollatzResearch.WordTrace tailWord_7192048 prefixEnd_7192048 1230992504735794104274793 := by
  unfold tailWord_7192048
  simp only [CollatzResearch.WordTrace]
  refine ⟨131157770324222937426616399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174877027098963916568821865 131157770324222937426616399)
  ·
    refine ⟨196736655486334406139924599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131157770324222937426616399 196736655486334406139924599)
    ·
      refine ⟨295104983229501609209886899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196736655486334406139924599 295104983229501609209886899)
      ·
        refine ⟨442657474844252413814830349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295104983229501609209886899 442657474844252413814830349)
        ·
          refine ⟨165996553066594655180561381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442657474844252413814830349 165996553066594655180561381)
          ·
            refine ⟨31124353699986497846355259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165996553066594655180561381 31124353699986497846355259)
            ·
              refine ⟨46686530549979746769532889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31124353699986497846355259 46686530549979746769532889)
              ·
                refine ⟨35014897912484810077149667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46686530549979746769532889 35014897912484810077149667)
                ·
                  refine ⟨52522346868727215115724501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35014897912484810077149667 52522346868727215115724501)
                  ·
                    refine ⟨1230992504735794104274793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52522346868727215115724501 1230992504735794104274793)
                    ·
                      rfl

theorem cell23_7192048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_7192048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192048 prefixEnd_7192048 := by exact prefixLift 7192048
  have htrace : WordTrace (prefixWord ++ tailWord_7192048) baseStart_7192048 baseEnd_7192048 := by
    simpa [prefixWord, tailWord_7192048, baseEnd_7192048] using wordTrace_append hprefix tailTrace_7192048
  have hstable : (prefixWord ++ tailWord_7192048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192048).length < 2 ^ (prefixWord ++ tailWord_7192048).sum := by decide
  have hdescent : baseEnd_7192048 < baseStart_7192048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192085 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_7192085 : Nat := 118140960795 + 7192085 * 2 ^ 59
def prefixEnd_7192085 : Nat := 4983230072969 + 3 ^ 40 * 7192085 * 2
def baseEnd_7192085 : Nat := 3692996512991598668061709

theorem tailTrace_7192085 : CollatzResearch.WordTrace tailWord_7192085 prefixEnd_7192085 3692996512991598668061709 := by
  unfold tailWord_7192085
  simp only [CollatzResearch.WordTrace]
  refine ⟨262316890149311830172329709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174877926766207886781553139 262316890149311830172329709)
  ·
    refine ⟨98368833805991936314623641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262316890149311830172329709 98368833805991936314623641)
    ·
      refine ⟨73776625354493952235967731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98368833805991936314623641 73776625354493952235967731)
      ·
        refine ⟨110664938031740928353951597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73776625354493952235967731 110664938031740928353951597)
        ·
          refine ⟨41499351761902848132731849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110664938031740928353951597 41499351761902848132731849)
          ·
            refine ⟨31124513821427136099548887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41499351761902848132731849 31124513821427136099548887)
            ·
              refine ⟨46686770732140704149323331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31124513821427136099548887 46686770732140704149323331)
              ·
                refine ⟨70030156098211056223984997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46686770732140704149323331 70030156098211056223984997)
                ·
                  refine ⟨13130654268414573041997187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70030156098211056223984997 13130654268414573041997187)
                  ·
                    refine ⟨19695981402621859562995781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13130654268414573041997187 19695981402621859562995781)
                    ·
                      refine ⟨3692996512991598668061709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19695981402621859562995781 3692996512991598668061709)
                      ·
                        rfl

theorem cell23_7192085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_7192085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192085 prefixEnd_7192085 := by exact prefixLift 7192085
  have htrace : WordTrace (prefixWord ++ tailWord_7192085) baseStart_7192085 baseEnd_7192085 := by
    simpa [prefixWord, tailWord_7192085, baseEnd_7192085] using wordTrace_append hprefix tailTrace_7192085
  have hstable : (prefixWord ++ tailWord_7192085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192085).length < 2 ^ (prefixWord ++ tailWord_7192085).sum := by decide
  have hdescent : baseEnd_7192085 < baseStart_7192085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192122 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_7192122 : Nat := 118140960795 + 7192122 * 2 ^ 59
def prefixEnd_7192122 : Nat := 4983230072969 + 3 ^ 40 * 7192122 * 2
def baseEnd_7192122 : Nat := 3693015511775815023299039

theorem tailTrace_7192122 : CollatzResearch.WordTrace tailWord_7192122 prefixEnd_7192122 3693015511775815023299039 := by
  unfold tailWord_7192122
  simp only [CollatzResearch.WordTrace]
  refine ⟨65579559912544446372856655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174878826433451856994284413 65579559912544446372856655)
  ·
    refine ⟨98369339868816669559284983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65579559912544446372856655 98369339868816669559284983)
    ·
      refine ⟨147554009803225004338927475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98369339868816669559284983 147554009803225004338927475)
      ·
        refine ⟨221331014704837506508391213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147554009803225004338927475 221331014704837506508391213)
        ·
          refine ⟨82999130514314064940646705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221331014704837506508391213 82999130514314064940646705)
          ·
            refine ⟨62249347885735548705485029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82999130514314064940646705 62249347885735548705485029)
            ·
              refine ⟨11671752728575415382278443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62249347885735548705485029 11671752728575415382278443)
              ·
                refine ⟨17507629092863123073417665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11671752728575415382278443 17507629092863123073417665)
                ·
                  refine ⟨13130721819647342305063249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17507629092863123073417665 13130721819647342305063249)
                  ·
                    refine ⟨9848041364735506728797437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13130721819647342305063249 9848041364735506728797437)
                    ·
                      refine ⟨3693015511775815023299039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9848041364735506728797437 3693015511775815023299039)
                      ·
                        rfl

theorem cell23_7192122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_7192122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192122 prefixEnd_7192122 := by exact prefixLift 7192122
  have htrace : WordTrace (prefixWord ++ tailWord_7192122) baseStart_7192122 baseEnd_7192122 := by
    simpa [prefixWord, tailWord_7192122, baseEnd_7192122] using wordTrace_append hprefix tailTrace_7192122
  have hstable : (prefixWord ++ tailWord_7192122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192122).length < 2 ^ (prefixWord ++ tailWord_7192122).sum := by decide
  have hdescent : baseEnd_7192122 < baseStart_7192122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192128 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_7192128 : Nat := 118140960795 + 7192128 * 2 ^ 59
def prefixEnd_7192128 : Nat := 4983230072969 + 3 ^ 40 * 7192128 * 2
def baseEnd_7192128 : Nat := 3693018592659741999824011

theorem tailTrace_7192128 : CollatzResearch.WordTrace tailWord_7192128 prefixEnd_7192128 3693018592659741999824011 := by
  unfold tailWord_7192128
  simp only [CollatzResearch.WordTrace]
  refine ⟨131159229244078024258072519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174878972325437365677430025 131159229244078024258072519)
  ·
    refine ⟨196738843866117036387108779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131159229244078024258072519 196738843866117036387108779)
    ·
      refine ⟨295108265799175554580663169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196738843866117036387108779 295108265799175554580663169)
      ·
        refine ⟨221331199349381665935497377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295108265799175554580663169 221331199349381665935497377)
        ·
          refine ⟨165998399512036249451623033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221331199349381665935497377 165998399512036249451623033)
          ·
            refine ⟨124498799634027187088717275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165998399512036249451623033 124498799634027187088717275)
            ·
              refine ⟨186748199451040780633075913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124498799634027187088717275 186748199451040780633075913)
              ·
                refine ⟨140061149588280585474806935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186748199451040780633075913 140061149588280585474806935)
                ·
                  refine ⟨210091724382420878212210403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140061149588280585474806935 210091724382420878212210403)
                  ·
                    refine ⟨315137586573631317318315605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210091724382420878212210403 315137586573631317318315605)
                    ·
                      refine ⟨3693018592659741999824011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 315137586573631317318315605 3693018592659741999824011)
                      ·
                        rfl

theorem cell23_7192128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_7192128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192128 prefixEnd_7192128 := by exact prefixLift 7192128
  have htrace : WordTrace (prefixWord ++ tailWord_7192128) baseStart_7192128 baseEnd_7192128 := by
    simpa [prefixWord, tailWord_7192128, baseEnd_7192128] using wordTrace_append hprefix tailTrace_7192128
  have hstable : (prefixWord ++ tailWord_7192128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192128).length < 2 ^ (prefixWord ++ tailWord_7192128).sum := by decide
  have hdescent : baseEnd_7192128 < baseStart_7192128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192129 : List Nat := [1, 2, 5, 1, 1, 1, 2, 5, 1, 4]
def baseStart_7192129 : Nat := 118140960795 + 7192129 * 2 ^ 59
def prefixEnd_7192129 : Nat := 4983230072969 + 3 ^ 40 * 7192129 * 2
def baseEnd_7192129 : Nat := 1231006368713465498637169

theorem tailTrace_7192129 : CollatzResearch.WordTrace tailWord_7192129 prefixEnd_7192129 1231006368713465498637169 := by
  unfold tailWord_7192129
  simp only [CollatzResearch.WordTrace]
  refine ⟨262318494961152425686931441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174878996640768283791287627 262318494961152425686931441)
  ·
    refine ⟨196738871220864319265198581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262318494961152425686931441 196738871220864319265198581)
    ·
      refine ⟨18444269176956029931112367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196738871220864319265198581 18444269176956029931112367)
      ·
        refine ⟨27666403765434044896668551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18444269176956029931112367 27666403765434044896668551)
        ·
          refine ⟨41499605648151067345002827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27666403765434044896668551 41499605648151067345002827)
          ·
            refine ⟨62249408472226601017504241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41499605648151067345002827 62249408472226601017504241)
            ·
              refine ⟨46687056354169950763128181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62249408472226601017504241 46687056354169950763128181)
              ·
                refine ⟨4376911533203432884043267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46687056354169950763128181 4376911533203432884043267)
                ·
                  refine ⟨6565367299805149326064901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376911533203432884043267 6565367299805149326064901)
                  ·
                    refine ⟨1231006368713465498637169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6565367299805149326064901 1231006368713465498637169)
                    ·
                      rfl

theorem cell23_7192129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_7192129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192129 prefixEnd_7192129 := by exact prefixLift 7192129
  have htrace : WordTrace (prefixWord ++ tailWord_7192129) baseStart_7192129 baseEnd_7192129 := by
    simpa [prefixWord, tailWord_7192129, baseEnd_7192129] using wordTrace_append hprefix tailTrace_7192129
  have hstable : (prefixWord ++ tailWord_7192129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192129).length < 2 ^ (prefixWord ++ tailWord_7192129).sum := by decide
  have hdescent : baseEnd_7192129 < baseStart_7192129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192146 : List Nat := [3, 2, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_7192146 : Nat := 118140960795 + 7192146 * 2 ^ 59
def prefixEnd_7192146 : Nat := 4983230072969 + 3 ^ 40 * 7192146 * 2
def baseEnd_7192146 : Nat := 1231009278437174309799643

theorem tailTrace_7192146 : CollatzResearch.WordTrace tailWord_7192146 prefixEnd_7192146 1231009278437174309799643 := by
  unfold tailWord_7192146
  simp only [CollatzResearch.WordTrace]
  refine ⟨65579778750522709397575073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174879410001393891726866861 65579778750522709397575073)
  ·
    refine ⟨49184834062892032048181305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65579778750522709397575073 49184834062892032048181305)
    ·
      refine ⟨36888625547169024036135979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49184834062892032048181305 36888625547169024036135979)
      ·
        refine ⟨55332938320753536054203969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36888625547169024036135979 55332938320753536054203969)
        ·
          refine ⟨41499703740565152040652977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55332938320753536054203969 41499703740565152040652977)
          ·
            refine ⟨31124777805423864030489733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41499703740565152040652977 31124777805423864030489733)
            ·
              refine ⟨5835895838516974505716825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31124777805423864030489733 5835895838516974505716825)
              ·
                refine ⟨4376921878887730879287619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5835895838516974505716825 4376921878887730879287619)
                ·
                  refine ⟨6565382818331596318931429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376921878887730879287619 6565382818331596318931429)
                  ·
                    refine ⟨1231009278437174309799643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6565382818331596318931429 1231009278437174309799643)
                    ·
                      rfl

theorem cell23_7192146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_7192146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192146 prefixEnd_7192146 := by exact prefixLift 7192146
  have htrace : WordTrace (prefixWord ++ tailWord_7192146) baseStart_7192146 baseEnd_7192146 := by
    simpa [prefixWord, tailWord_7192146, baseEnd_7192146] using wordTrace_append hprefix tailTrace_7192146
  have hstable : (prefixWord ++ tailWord_7192146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192146).length < 2 ^ (prefixWord ++ tailWord_7192146).sum := by decide
  have hdescent : baseEnd_7192146 < baseStart_7192146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192152 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 3, 1, 3]
def baseStart_7192152 : Nat := 118140960795 + 7192152 * 2 ^ 59
def prefixEnd_7192152 : Nat := 4983230072969 + 3 ^ 40 * 7192152 * 2
def baseEnd_7192152 : Nat := 3693030916195449905923901

theorem tailTrace_7192152 : CollatzResearch.WordTrace tailWord_7192152 prefixEnd_7192152 3693030916195449905923901 := by
  unfold tailWord_7192152
  simp only [CollatzResearch.WordTrace]
  refine ⟨131159666920034550307509355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174879555893379400410012473 131159666920034550307509355)
  ·
    refine ⟨196739500380051825461264033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131159666920034550307509355 196739500380051825461264033)
    ·
      refine ⟨147554625285038869095948025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196739500380051825461264033 147554625285038869095948025)
      ·
        refine ⟨110665968963779151821961019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147554625285038869095948025 110665968963779151821961019)
        ·
          refine ⟨165998953445668727732941529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110665968963779151821961019 165998953445668727732941529)
          ·
            refine ⟨124499215084251545799706147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165998953445668727732941529 124499215084251545799706147)
            ·
              refine ⟨186748822626377318699559221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124499215084251545799706147 186748822626377318699559221)
              ·
                refine ⟨17507702121222873628083677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186748822626377318699559221 17507702121222873628083677)
                ·
                  refine ⟨6565388295458577610531379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17507702121222873628083677 6565388295458577610531379)
                  ·
                    refine ⟨9848082443187866415797069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6565388295458577610531379 9848082443187866415797069)
                    ·
                      refine ⟨3693030916195449905923901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9848082443187866415797069 3693030916195449905923901)
                      ·
                        rfl

theorem cell23_7192152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_7192152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192152 prefixEnd_7192152 := by exact prefixLift 7192152
  have htrace : WordTrace (prefixWord ++ tailWord_7192152) baseStart_7192152 baseEnd_7192152 := by
    simpa [prefixWord, tailWord_7192152, baseEnd_7192152] using wordTrace_append hprefix tailTrace_7192152
  have hstable : (prefixWord ++ tailWord_7192152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192152).length < 2 ^ (prefixWord ++ tailWord_7192152).sum := by decide
  have hdescent : baseEnd_7192152 < baseStart_7192152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
