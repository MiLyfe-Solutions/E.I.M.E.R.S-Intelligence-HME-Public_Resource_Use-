import V185TrunkScan23Chunk1279

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7583328 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_7583328 : Nat := 118140960795 + 7583328 * 2 ^ 59
def prefixEnd_7583328 : Nat := 4983230072969 + 3 ^ 40 * 7583328 * 2
def baseEnd_7583328 : Nat := 3893892224698611428024915

theorem tailTrace_7583328 : CollatzResearch.WordTrace tailWord_7583328 prefixEnd_7583328 3893892224698611428024915 := by
  unfold tailWord_7583328
  simp only [CollatzResearch.WordTrace]
  refine ⟨138293347335452630078499319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184391129780603506771332425 138293347335452630078499319)
  ·
    refine ⟨207440021003178945117748979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138293347335452630078499319 207440021003178945117748979)
    ·
      refine ⟨311160031504768417676623469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207440021003178945117748979 311160031504768417676623469)
      ·
        refine ⟨116685011814288156628733801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311160031504768417676623469 116685011814288156628733801)
        ·
          refine ⟨87513758860716117471550351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116685011814288156628733801 87513758860716117471550351)
          ·
            refine ⟨131270638291074176207325527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87513758860716117471550351 131270638291074176207325527)
            ·
              refine ⟨196905957436611264310988291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131270638291074176207325527 196905957436611264310988291)
              ·
                refine ⟨295358936154916896466482437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196905957436611264310988291 295358936154916896466482437)
                ·
                  refine ⟨55379800529046918087465457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295358936154916896466482437 55379800529046918087465457)
                  ·
                    refine ⟨41534850396785188565599093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55379800529046918087465457 41534850396785188565599093)
                    ·
                      refine ⟨3893892224698611428024915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41534850396785188565599093 3893892224698611428024915)
                      ·
                        rfl

theorem cell23_7583328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_7583328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583328 prefixEnd_7583328 := by exact prefixLift 7583328
  have htrace : WordTrace (prefixWord ++ tailWord_7583328) baseStart_7583328 baseEnd_7583328 := by
    simpa [prefixWord, tailWord_7583328, baseEnd_7583328] using wordTrace_append hprefix tailTrace_7583328
  have hstable : (prefixWord ++ tailWord_7583328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583328).length < 2 ^ (prefixWord ++ tailWord_7583328).sum := by decide
  have hdescent : baseEnd_7583328 < baseStart_7583328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583332 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_7583332 : Nat := 118140960795 + 7583332 * 2 ^ 59
def prefixEnd_7583332 : Nat := 4983230072969 + 3 ^ 40 * 7583332 * 2
def baseEnd_7583332 : Nat := 3893894278621229412374897

theorem tailTrace_7583332 : CollatzResearch.WordTrace tailWord_7583332 prefixEnd_7583332 3893894278621229412374897 := by
  unfold tailWord_7583332
  simp only [CollatzResearch.WordTrace]
  refine ⟨138293420281445384420072125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184391227041927179226762833 138293420281445384420072125)
  ·
    refine ⟨51860032605542019157527047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138293420281445384420072125 51860032605542019157527047)
    ·
      refine ⟨77790048908313028736290571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51860032605542019157527047 77790048908313028736290571)
      ·
        refine ⟨116685073362469543104435857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77790048908313028736290571 116685073362469543104435857)
        ·
          refine ⟨87513805021852157328326893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116685073362469543104435857 87513805021852157328326893)
          ·
            refine ⟨32817676883194558998122585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87513805021852157328326893 32817676883194558998122585)
            ·
              refine ⟨24613257662395919248591939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32817676883194558998122585 24613257662395919248591939)
              ·
                refine ⟨36919886493593878872887909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24613257662395919248591939 36919886493593878872887909)
                ·
                  refine ⟨6922478717548852288666483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36919886493593878872887909 6922478717548852288666483)
                  ·
                    refine ⟨10383718076323278432999725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6922478717548852288666483 10383718076323278432999725)
                    ·
                      refine ⟨3893894278621229412374897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10383718076323278432999725 3893894278621229412374897)
                      ·
                        rfl

theorem cell23_7583332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_7583332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583332 prefixEnd_7583332 := by exact prefixLift 7583332
  have htrace : WordTrace (prefixWord ++ tailWord_7583332) baseStart_7583332 baseEnd_7583332 := by
    simpa [prefixWord, tailWord_7583332, baseEnd_7583332] using wordTrace_append hprefix tailTrace_7583332
  have hstable : (prefixWord ++ tailWord_7583332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583332).length < 2 ^ (prefixWord ++ tailWord_7583332).sum := by decide
  have hdescent : baseEnd_7583332 < baseStart_7583332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583333 : List Nat := [1, 3, 1, 3, 3, 2, 3, 2, 1, 2, 2]
def baseStart_7583333 : Nat := 118140960795 + 7583333 * 2 ^ 59
def prefixEnd_7583333 : Nat := 4983230072969 + 3 ^ 40 * 7583333 * 2
def baseEnd_7583333 : Nat := 3893894792101883908462393

theorem tailTrace_7583333 : CollatzResearch.WordTrace tailWord_7583333 prefixEnd_7583333 3893894792101883908462393 := by
  unfold tailWord_7583333
  simp only [CollatzResearch.WordTrace]
  refine ⟨276586877035887146010930653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184391251357258097340620435 276586877035887146010930653)
  ·
    refine ⟨103720078888457679754098995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276586877035887146010930653 103720078888457679754098995)
    ·
      refine ⟨155580118332686519631148493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103720078888457679754098995 155580118332686519631148493)
      ·
        refine ⟨58342544374757444861680685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155580118332686519631148493 58342544374757444861680685)
        ·
          refine ⟨21878454140534041823130257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58342544374757444861680685 21878454140534041823130257)
          ·
            refine ⟨16408840605400531367347693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21878454140534041823130257 16408840605400531367347693)
            ·
              refine ⟨6153315227025199262755385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16408840605400531367347693 6153315227025199262755385)
              ·
                refine ⟨4614986420268899447066539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6153315227025199262755385 4614986420268899447066539)
                ·
                  refine ⟨6922479630403349170599809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614986420268899447066539 6922479630403349170599809)
                  ·
                    refine ⟨5191859722802511877949857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6922479630403349170599809 5191859722802511877949857)
                    ·
                      refine ⟨3893894792101883908462393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191859722802511877949857 3893894792101883908462393)
                      ·
                        rfl

theorem cell23_7583333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_7583333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583333 prefixEnd_7583333 := by exact prefixLift 7583333
  have htrace : WordTrace (prefixWord ++ tailWord_7583333) baseStart_7583333 baseEnd_7583333 := by
    simpa [prefixWord, tailWord_7583333, baseEnd_7583333] using wordTrace_append hprefix tailTrace_7583333
  have hstable : (prefixWord ++ tailWord_7583333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583333).length < 2 ^ (prefixWord ++ tailWord_7583333).sum := by decide
  have hdescent : baseEnd_7583333 < baseStart_7583333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583372 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 1, 4, 2]
def baseStart_7583372 : Nat := 118140960795 + 7583372 * 2 ^ 59
def prefixEnd_7583372 : Nat := 4983230072969 + 3 ^ 40 * 7583372 * 2
def baseEnd_7583372 : Nat := 3893914817847409255874713

theorem tailTrace_7583372 : CollatzResearch.WordTrace tailWord_7583372 prefixEnd_7583372 3893914817847409255874713 := by
  unfold tailWord_7583372
  simp only [CollatzResearch.WordTrace]
  refine ⟨138294149741372927835800185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184392199655163903781066913 138294149741372927835800185)
  ·
    refine ⟨103720612306029695876850139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138294149741372927835800185 103720612306029695876850139)
    ·
      refine ⟨155580918459044543815275209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103720612306029695876850139 155580918459044543815275209)
      ·
        refine ⟨116685688844283407861456407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155580918459044543815275209 116685688844283407861456407)
        ·
          refine ⟨175028533266425111792184611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116685688844283407861456407 175028533266425111792184611)
          ·
            refine ⟨262542799899637667688276917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175028533266425111792184611 262542799899637667688276917)
            ·
              refine ⟨24613387490591031345775961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262542799899637667688276917 24613387490591031345775961)
              ·
                refine ⟨18460040617943273509331971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24613387490591031345775961 18460040617943273509331971)
                ·
                  refine ⟨27690060926914910263997957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18460040617943273509331971 27690060926914910263997957)
                  ·
                    refine ⟨5191886423796545674499617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27690060926914910263997957 5191886423796545674499617)
                    ·
                      refine ⟨3893914817847409255874713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191886423796545674499617 3893914817847409255874713)
                      ·
                        rfl

theorem cell23_7583372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_7583372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583372 prefixEnd_7583372 := by exact prefixLift 7583372
  have htrace : WordTrace (prefixWord ++ tailWord_7583372) baseStart_7583372 baseEnd_7583372 := by
    simpa [prefixWord, tailWord_7583372, baseEnd_7583372] using wordTrace_append hprefix tailTrace_7583372
  have hstable : (prefixWord ++ tailWord_7583372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583372).length < 2 ^ (prefixWord ++ tailWord_7583372).sum := by decide
  have hdescent : baseEnd_7583372 < baseStart_7583372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583446 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_7583446 : Nat := 118140960795 + 7583446 * 2 ^ 59
def prefixEnd_7583446 : Nat := 4983230072969 + 3 ^ 40 * 7583446 * 2
def baseEnd_7583446 : Nat := 432661423935093551816597

theorem tailTrace_7583446 : CollatzResearch.WordTrace tailWord_7583446 prefixEnd_7583446 432661423935093551816597 := by
  unfold tailWord_7583446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17286937405279860394362137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184393998989651844206529461 17286937405279860394362137)
  ·
    refine ⟨12965203053959895295771603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17286937405279860394362137 12965203053959895295771603)
    ·
      refine ⟨19447804580939842943657405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12965203053959895295771603 19447804580939842943657405)
      ·
        refine ⟨7292926717852441103871527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19447804580939842943657405 7292926717852441103871527)
        ·
          refine ⟨10939390076778661655807291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7292926717852441103871527 10939390076778661655807291)
          ·
            refine ⟨16409085115167992483710937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10939390076778661655807291 16409085115167992483710937)
            ·
              refine ⟨12306813836375994362783203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16409085115167992483710937 12306813836375994362783203)
              ·
                refine ⟨18460220754563991544174805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12306813836375994362783203 18460220754563991544174805)
                ·
                  refine ⟨432661423935093551816597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18460220754563991544174805 432661423935093551816597)
                  ·
                    rfl

theorem cell23_7583446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_7583446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583446 prefixEnd_7583446 := by exact prefixLift 7583446
  have htrace : WordTrace (prefixWord ++ tailWord_7583446) baseStart_7583446 baseEnd_7583446 := by
    simpa [prefixWord, tailWord_7583446, baseEnd_7583446] using wordTrace_append hprefix tailTrace_7583446
  have hstable : (prefixWord ++ tailWord_7583446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583446).length < 2 ^ (prefixWord ++ tailWord_7583446).sum := by decide
  have hdescent : baseEnd_7583446 < baseStart_7583446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583482 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_7583482 : Nat := 118140960795 + 7583482 * 2 ^ 59
def prefixEnd_7583482 : Nat := 4983230072969 + 3 ^ 40 * 7583482 * 2
def baseEnd_7583482 : Nat := 3893971300719403825499207

theorem tailTrace_7583482 : CollatzResearch.WordTrace tailWord_7583482 prefixEnd_7583482 3893971300719403825499207 := by
  unfold tailWord_7583482
  simp only [CollatzResearch.WordTrace]
  refine ⟨69148077878086836114526175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184394874341564896305403133 69148077878086836114526175)
  ·
    refine ⟨103722116817130254171789263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69148077878086836114526175 103722116817130254171789263)
    ·
      refine ⟨155583175225695381257683895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103722116817130254171789263 155583175225695381257683895)
      ·
        refine ⟨233374762838543071886525843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155583175225695381257683895 233374762838543071886525843)
        ·
          refine ⟨350062144257814607829788765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233374762838543071886525843 350062144257814607829788765)
          ·
            refine ⟨131273304096680477936170787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350062144257814607829788765 131273304096680477936170787)
            ·
              refine ⟨196909956145020716904256181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131273304096680477936170787 196909956145020716904256181)
              ·
                refine ⟨18460308388595692209774017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196909956145020716904256181 18460308388595692209774017)
                ·
                  refine ⟨13845231291446769157330513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18460308388595692209774017 13845231291446769157330513)
                  ·
                    refine ⟨10383923468585076867997885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13845231291446769157330513 10383923468585076867997885)
                    ·
                      refine ⟨3893971300719403825499207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10383923468585076867997885 3893971300719403825499207)
                      ·
                        rfl

theorem cell23_7583482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_7583482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583482 prefixEnd_7583482 := by exact prefixLift 7583482
  have htrace : WordTrace (prefixWord ++ tailWord_7583482) baseStart_7583482 baseEnd_7583482 := by
    simpa [prefixWord, tailWord_7583482, baseEnd_7583482] using wordTrace_append hprefix tailTrace_7583482
  have hstable : (prefixWord ++ tailWord_7583482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583482).length < 2 ^ (prefixWord ++ tailWord_7583482).sum := by decide
  have hdescent : baseEnd_7583482 < baseStart_7583482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583506 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7583506 : Nat := 118140960795 + 7583506 * 2 ^ 59
def prefixEnd_7583506 : Nat := 4983230072969 + 3 ^ 40 * 7583506 * 2
def baseEnd_7583506 : Nat := 1297994541418370577199699

theorem tailTrace_7583506 : CollatzResearch.WordTrace tailWord_7583506 prefixEnd_7583506 1297994541418370577199699 := by
  unfold tailWord_7583506
  simp only [CollatzResearch.WordTrace]
  refine ⟨69148296716065099139244593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184395457909506931037985581 69148296716065099139244593)
  ·
    refine ⟨51861222537048824354433445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69148296716065099139244593 51861222537048824354433445)
    ·
      refine ⟨9723979225696654566456271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51861222537048824354433445 9723979225696654566456271)
      ·
        refine ⟨14585968838544981849684407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9723979225696654566456271 14585968838544981849684407)
        ·
          refine ⟨21878953257817472774526611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14585968838544981849684407 21878953257817472774526611)
          ·
            refine ⟨32818429886726209161789917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21878953257817472774526611 32818429886726209161789917)
            ·
              refine ⟨12306911207522328435671219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32818429886726209161789917 12306911207522328435671219)
              ·
                refine ⟨18460366811283492653506829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12306911207522328435671219 18460366811283492653506829)
                ·
                  refine ⟨6922637554231309745065061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18460366811283492653506829 6922637554231309745065061)
                  ·
                    refine ⟨1297994541418370577199699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6922637554231309745065061 1297994541418370577199699)
                    ·
                      rfl

theorem cell23_7583506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7583506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583506 prefixEnd_7583506 := by exact prefixLift 7583506
  have htrace : WordTrace (prefixWord ++ tailWord_7583506) baseStart_7583506 baseEnd_7583506 := by
    simpa [prefixWord, tailWord_7583506, baseEnd_7583506] using wordTrace_append hprefix tailTrace_7583506
  have hstable : (prefixWord ++ tailWord_7583506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583506).length < 2 ^ (prefixWord ++ tailWord_7583506).sum := by decide
  have hdescent : baseEnd_7583506 < baseStart_7583506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583515 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 5, 5]
def baseStart_7583515 : Nat := 118140960795 + 7583515 * 2 ^ 59
def prefixEnd_7583515 : Nat := 4983230072969 + 3 ^ 40 * 7583515 * 2
def baseEnd_7583515 : Nat := 1297996081860334065462185

theorem tailTrace_7583515 : CollatzResearch.WordTrace tailWord_7583515 prefixEnd_7583515 1297996081860334065462185 := by
  unfold tailWord_7583515
  simp only [CollatzResearch.WordTrace]
  refine ⟨276593515121227791094055999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184395676747485194062703999 276593515121227791094055999)
  ·
    refine ⟨414890272681841686641083999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276593515121227791094055999 414890272681841686641083999)
    ·
      refine ⟨622335409022762529961625999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414890272681841686641083999 622335409022762529961625999)
      ·
        refine ⟨933503113534143794942438999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622335409022762529961625999 933503113534143794942438999)
        ·
          refine ⟨1400254670301215692413658499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933503113534143794942438999 1400254670301215692413658499)
          ·
            refine ⟨2100382005451823538620487749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400254670301215692413658499 2100382005451823538620487749)
            ·
              refine ⟨393821626022216913491341453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2100382005451823538620487749 393821626022216913491341453)
              ·
                refine ⟨147683109758331342559253045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393821626022216913491341453 147683109758331342559253045)
                ·
                  refine ⟨13845291539843563364929973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147683109758331342559253045 13845291539843563364929973)
                  ·
                    refine ⟨1297996081860334065462185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13845291539843563364929973 1297996081860334065462185)
                    ·
                      rfl

theorem cell23_7583515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 5].length) (baseStart_7583515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583515 prefixEnd_7583515 := by exact prefixLift 7583515
  have htrace : WordTrace (prefixWord ++ tailWord_7583515) baseStart_7583515 baseEnd_7583515 := by
    simpa [prefixWord, tailWord_7583515, baseEnd_7583515] using wordTrace_append hprefix tailTrace_7583515
  have hstable : (prefixWord ++ tailWord_7583515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583515).length < 2 ^ (prefixWord ++ tailWord_7583515).sum := by decide
  have hdescent : baseEnd_7583515 < baseStart_7583515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583532 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_7583532 : Nat := 118140960795 + 7583532 * 2 ^ 59
def prefixEnd_7583532 : Nat := 4983230072969 + 3 ^ 40 * 7583532 * 2
def baseEnd_7583532 : Nat := 1297998991584042876624659

theorem tailTrace_7583532 : CollatzResearch.WordTrace tailWord_7583532 prefixEnd_7583532 1297998991584042876624659 := by
  unfold tailWord_7583532
  simp only [CollatzResearch.WordTrace]
  refine ⟨138297067581083101498712425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184396090108110801998283233 138297067581083101498712425)
  ·
    refine ⟨103722800685812326124034319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138297067581083101498712425 103722800685812326124034319)
    ·
      refine ⟨155584201028718489186051479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103722800685812326124034319 155584201028718489186051479)
      ·
        refine ⟨233376301543077733779077219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155584201028718489186051479 233376301543077733779077219)
        ·
          refine ⟨350064452314616600668615829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233376301543077733779077219 350064452314616600668615829)
          ·
            refine ⟨16409271202247653156341367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 350064452314616600668615829 16409271202247653156341367)
            ·
              refine ⟨24613906803371479734512051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16409271202247653156341367 24613906803371479734512051)
              ·
                refine ⟨36920860205057219601768077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24613906803371479734512051 36920860205057219601768077)
                ·
                  refine ⟨13845322576896457350663029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36920860205057219601768077 13845322576896457350663029)
                  ·
                    refine ⟨1297998991584042876624659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13845322576896457350663029 1297998991584042876624659)
                    ·
                      rfl

theorem cell23_7583532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_7583532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583532 prefixEnd_7583532 := by exact prefixLift 7583532
  have htrace : WordTrace (prefixWord ++ tailWord_7583532) baseStart_7583532 baseEnd_7583532 := by
    simpa [prefixWord, tailWord_7583532, baseEnd_7583532] using wordTrace_append hprefix tailTrace_7583532
  have hstable : (prefixWord ++ tailWord_7583532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583532).length < 2 ^ (prefixWord ++ tailWord_7583532).sum := by decide
  have hdescent : baseEnd_7583532 < baseStart_7583532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583535 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_7583535 : Nat := 118140960795 + 7583535 * 2 ^ 59
def prefixEnd_7583535 : Nat := 4983230072969 + 3 ^ 40 * 7583535 * 2
def baseEnd_7583535 : Nat := 3893998515194092118136463

theorem tailTrace_7583535 : CollatzResearch.WordTrace tailWord_7583535 prefixEnd_7583535 3893998515194092118136463 := by
  unfold tailWord_7583535
  simp only [CollatzResearch.WordTrace]
  refine ⟨276594244581155334509784059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184396163054103556339856039 276594244581155334509784059)
  ·
    refine ⟨414891366871733001764676089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276594244581155334509784059 414891366871733001764676089)
    ·
      refine ⟨311168525153799751323507067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414891366871733001764676089 311168525153799751323507067)
      ·
        refine ⟨466752787730699626985260601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311168525153799751323507067 466752787730699626985260601)
        ·
          refine ⟨350064590798024720238945451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466752787730699626985260601 350064590798024720238945451)
          ·
            refine ⟨525096886197037080358418177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350064590798024720238945451 525096886197037080358418177)
            ·
              refine ⟨393822664647777810268813633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525096886197037080358418177 393822664647777810268813633)
              ·
                refine ⟨295366998485833357701610225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393822664647777810268813633 295366998485833357701610225)
                ·
                  refine ⟨221525248864375018276207669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295366998485833357701610225 221525248864375018276207669)
                  ·
                    refine ⟨20767992081035157963394469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 221525248864375018276207669 20767992081035157963394469)
                    ·
                      refine ⟨3893998515194092118136463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20767992081035157963394469 3893998515194092118136463)
                      ·
                        rfl

theorem cell23_7583535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_7583535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583535 prefixEnd_7583535 := by exact prefixLift 7583535
  have htrace : WordTrace (prefixWord ++ tailWord_7583535) baseStart_7583535 baseEnd_7583535 := by
    simpa [prefixWord, tailWord_7583535, baseEnd_7583535] using wordTrace_append hprefix tailTrace_7583535
  have hstable : (prefixWord ++ tailWord_7583535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583535).length < 2 ^ (prefixWord ++ tailWord_7583535).sum := by decide
  have hdescent : baseEnd_7583535 < baseStart_7583535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583589 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 3]
def baseStart_7583589 : Nat := 118140960795 + 7583589 * 2 ^ 59
def prefixEnd_7583589 : Nat := 4983230072969 + 3 ^ 40 * 7583589 * 2
def baseEnd_7583589 : Nat := 3894026243149434906861215

theorem tailTrace_7583589 : CollatzResearch.WordTrace tailWord_7583589 prefixEnd_7583589 3894026243149434906861215 := by
  unfold tailWord_7583589
  simp only [CollatzResearch.WordTrace]
  refine ⟨276596214122959701732249821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184397476081973134488166547 276596214122959701732249821)
  ·
    refine ⟨103723580296109888149593683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276596214122959701732249821 103723580296109888149593683)
    ·
      refine ⟨155585370444164832224390525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103723580296109888149593683 155585370444164832224390525)
      ·
        refine ⟨58344513916561812084146447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155585370444164832224390525 58344513916561812084146447)
        ·
          refine ⟨87516770874842718126219671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58344513916561812084146447 87516770874842718126219671)
          ·
            refine ⟨131275156312264077189329507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87516770874842718126219671 131275156312264077189329507)
            ·
              refine ⟨196912734468396115783994261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131275156312264077189329507 196912734468396115783994261)
              ·
                refine ⟨9230284428206067927374731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196912734468396115783994261 9230284428206067927374731)
                ·
                  refine ⟨13845426642309101891062097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9230284428206067927374731 13845426642309101891062097)
                  ·
                    refine ⟨10384069981731826418296573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13845426642309101891062097 10384069981731826418296573)
                    ·
                      refine ⟨3894026243149434906861215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10384069981731826418296573 3894026243149434906861215)
                      ·
                        rfl

theorem cell23_7583589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_7583589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583589 prefixEnd_7583589 := by exact prefixLift 7583589
  have htrace : WordTrace (prefixWord ++ tailWord_7583589) baseStart_7583589 baseEnd_7583589 := by
    simpa [prefixWord, tailWord_7583589, baseEnd_7583589] using wordTrace_append hprefix tailTrace_7583589
  have hstable : (prefixWord ++ tailWord_7583589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583589).length < 2 ^ (prefixWord ++ tailWord_7583589).sum := by decide
  have hdescent : baseEnd_7583589 < baseStart_7583589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583630 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_7583630 : Nat := 118140960795 + 7583630 * 2 ^ 59
def prefixEnd_7583630 : Nat := 4983230072969 + 3 ^ 40 * 7583630 * 2
def baseEnd_7583630 : Nat := 1298015765285423082149509

theorem tailTrace_7583630 : CollatzResearch.WordTrace tailWord_7583630 prefixEnd_7583630 1298015765285423082149509 := by
  unfold tailWord_7583630
  simp only [CollatzResearch.WordTrace]
  refine ⟨34574713689476395716811543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184398473010540777156328229 34574713689476395716811543)
  ·
    refine ⟨51862070534214593575217315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34574713689476395716811543 51862070534214593575217315)
    ·
      refine ⟨77793105801321890362825973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51862070534214593575217315 77793105801321890362825973)
      ·
        refine ⟨7293103668873927221514935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77793105801321890362825973 7293103668873927221514935)
        ·
          refine ⟨10939655503310890832272403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7293103668873927221514935 10939655503310890832272403)
          ·
            refine ⟨16409483254966336248408605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10939655503310890832272403 16409483254966336248408605)
            ·
              refine ⟨6153556220612376093153227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16409483254966336248408605 6153556220612376093153227)
              ·
                refine ⟨9230334330918564139729841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6153556220612376093153227 9230334330918564139729841)
                ·
                  refine ⟨6922750748188923104797381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9230334330918564139729841 6922750748188923104797381)
                  ·
                    refine ⟨1298015765285423082149509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6922750748188923104797381 1298015765285423082149509)
                    ·
                      rfl

theorem cell23_7583630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_7583630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583630 prefixEnd_7583630 := by exact prefixLift 7583630
  have htrace : WordTrace (prefixWord ++ tailWord_7583630) baseStart_7583630 baseEnd_7583630 := by
    simpa [prefixWord, tailWord_7583630, baseEnd_7583630] using wordTrace_append hprefix tailTrace_7583630
  have hstable : (prefixWord ++ tailWord_7583630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583630).length < 2 ^ (prefixWord ++ tailWord_7583630).sum := by decide
  have hdescent : baseEnd_7583630 < baseStart_7583630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583636 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_7583636 : Nat := 118140960795 + 7583636 * 2 ^ 59
def prefixEnd_7583636 : Nat := 4983230072969 + 3 ^ 40 * 7583636 * 2
def baseEnd_7583636 : Nat := 3894050376740196222973499

theorem tailTrace_7583636 : CollatzResearch.WordTrace tailWord_7583636 prefixEnd_7583636 3894050376740196222973499 := by
  unfold tailWord_7583636
  simp only [CollatzResearch.WordTrace]
  refine ⟨138298964176894714379605381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184398618902526285839473841 138298964176894714379605381)
  ·
    refine ⟨25931055783167758946176009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138298964176894714379605381 25931055783167758946176009)
    ·
      refine ⟨19448291837375819209632007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25931055783167758946176009 19448291837375819209632007)
      ·
        refine ⟨29172437756063728814448011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19448291837375819209632007 29172437756063728814448011)
        ·
          refine ⟨43758656634095593221672017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29172437756063728814448011 43758656634095593221672017)
          ·
            refine ⟨32818992475571694916254013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43758656634095593221672017 32818992475571694916254013)
            ·
              refine ⟨12307122178339385593595255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32818992475571694916254013 12307122178339385593595255)
              ·
                refine ⟨18460683267509078390392883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307122178339385593595255 18460683267509078390392883)
                ·
                  refine ⟨27691024901263617585589325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18460683267509078390392883 27691024901263617585589325)
                  ·
                    refine ⟨10384134337973856594595997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27691024901263617585589325 10384134337973856594595997)
                    ·
                      refine ⟨3894050376740196222973499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10384134337973856594595997 3894050376740196222973499)
                      ·
                        rfl

theorem cell23_7583636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_7583636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583636 prefixEnd_7583636 := by exact prefixLift 7583636
  have htrace : WordTrace (prefixWord ++ tailWord_7583636) baseStart_7583636 baseEnd_7583636 := by
    simpa [prefixWord, tailWord_7583636, baseEnd_7583636] using wordTrace_append hprefix tailTrace_7583636
  have hstable : (prefixWord ++ tailWord_7583636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583636).length < 2 ^ (prefixWord ++ tailWord_7583636).sum := by decide
  have hdescent : baseEnd_7583636 < baseStart_7583636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583712 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 1, 7]
def baseStart_7583712 : Nat := 118140960795 + 7583712 * 2 ^ 59
def prefixEnd_7583712 : Nat := 4983230072969 + 3 ^ 40 * 7583712 * 2
def baseEnd_7583712 : Nat := 1298029800423312641874383

theorem tailTrace_7583712 : CollatzResearch.WordTrace tailWord_7583712 prefixEnd_7583712 1298029800423312641874383 := by
  unfold tailWord_7583712
  simp only [CollatzResearch.WordTrace]
  refine ⟨138300350150757046869488695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184400466867676062492651593 138300350150757046869488695)
  ·
    refine ⟨207450525226135570304233043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138300350150757046869488695 207450525226135570304233043)
    ·
      refine ⟨311175787839203355456349565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207450525226135570304233043 311175787839203355456349565)
      ·
        refine ⟨116690920439701258296131087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311175787839203355456349565 116690920439701258296131087)
        ·
          refine ⟨175036380659551887444196631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116690920439701258296131087 175036380659551887444196631)
          ·
            refine ⟨262554570989327831166294947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175036380659551887444196631 262554570989327831166294947)
            ·
              refine ⟨393831856483991746749442421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262554570989327831166294947 393831856483991746749442421)
              ·
                refine ⟨36921736545374226257760227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 393831856483991746749442421 36921736545374226257760227)
                ·
                  refine ⟨55382604818061339386640341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36921736545374226257760227 55382604818061339386640341)
                  ·
                    refine ⟨1298029800423312641874383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55382604818061339386640341 1298029800423312641874383)
                    ·
                      rfl

theorem cell23_7583712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_7583712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583712 prefixEnd_7583712 := by exact prefixLift 7583712
  have htrace : WordTrace (prefixWord ++ tailWord_7583712) baseStart_7583712 baseEnd_7583712 := by
    simpa [prefixWord, tailWord_7583712, baseEnd_7583712] using wordTrace_append hprefix tailTrace_7583712
  have hstable : (prefixWord ++ tailWord_7583712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583712).length < 2 ^ (prefixWord ++ tailWord_7583712).sum := by decide
  have hdescent : baseEnd_7583712 < baseStart_7583712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583793 : List Nat := [1, 2, 2, 3, 1, 3, 2, 4, 1, 4]
def baseStart_7583793 : Nat := 118140960795 + 7583793 * 2 ^ 59
def prefixEnd_7583793 : Nat := 4983230072969 + 3 ^ 40 * 7583793 * 2
def baseEnd_7583793 : Nat := 1298043664400984036236759

theorem tailTrace_7583793 : CollatzResearch.WordTrace tailWord_7583793 prefixEnd_7583793 1298043664400984036236759 := by
  unfold tailWord_7583793
  simp only [CollatzResearch.WordTrace]
  refine ⟨276603654614220644572676033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184402436409480429715117355 276603654614220644572676033)
  ·
    refine ⟨207452740960665483429507025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276603654614220644572676033 207452740960665483429507025)
    ·
      refine ⟨155589555720499112572130269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207452740960665483429507025 155589555720499112572130269)
      ·
        refine ⟨58346083395187167214548851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155589555720499112572130269 58346083395187167214548851)
        ·
          refine ⟨87519125092780750821823277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58346083395187167214548851 87519125092780750821823277)
          ·
            refine ⟨32819671909792781558183729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87519125092780750821823277 32819671909792781558183729)
            ·
              refine ⟨24614753932344586168637797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32819671909792781558183729 24614753932344586168637797)
              ·
                refine ⟨4615266362314609906619587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24614753932344586168637797 4615266362314609906619587)
                ·
                  refine ⟨6922899543471914859929381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4615266362314609906619587 6922899543471914859929381)
                  ·
                    refine ⟨1298043664400984036236759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6922899543471914859929381 1298043664400984036236759)
                    ·
                      rfl

theorem cell23_7583793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_7583793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583793 prefixEnd_7583793 := by exact prefixLift 7583793
  have htrace : WordTrace (prefixWord ++ tailWord_7583793) baseStart_7583793 baseEnd_7583793 := by
    simpa [prefixWord, tailWord_7583793, baseEnd_7583793] using wordTrace_append hprefix tailTrace_7583793
  have hstable : (prefixWord ++ tailWord_7583793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583793).length < 2 ^ (prefixWord ++ tailWord_7583793).sum := by decide
  have hdescent : baseEnd_7583793 < baseStart_7583793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583816 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_7583816 : Nat := 118140960795 + 7583816 * 2 ^ 59
def prefixEnd_7583816 : Nat := 4983230072969 + 3 ^ 40 * 7583816 * 2
def baseEnd_7583816 : Nat := 3894142803258005518722671

theorem tailTrace_7583816 : CollatzResearch.WordTrace tailWord_7583816 prefixEnd_7583816 3894142803258005518722671 := by
  unfold tailWord_7583816
  simp only [CollatzResearch.WordTrace]
  refine ⟨138302246746568659750381651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184402995662091546333842201 138302246746568659750381651)
  ·
    refine ⟨207453370119852989625572477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138302246746568659750381651 207453370119852989625572477)
    ·
      refine ⟨77795013794944871109589679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207453370119852989625572477 77795013794944871109589679)
      ·
        refine ⟨116692520692417306664384519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77795013794944871109589679 116692520692417306664384519)
        ·
          refine ⟨175038781038625959996576779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116692520692417306664384519 175038781038625959996576779)
          ·
            refine ⟨262558171557938939994865169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175038781038625959996576779 262558171557938939994865169)
            ·
              refine ⟨196918628668454204996148877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262558171557938939994865169 196918628668454204996148877)
              ·
                refine ⟨73844485750670326873555829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196918628668454204996148877 73844485750670326873555829)
                ·
                  refine ⟨6922920539125343144395859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73844485750670326873555829 6922920539125343144395859)
                  ·
                    refine ⟨10384380808688014716593789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6922920539125343144395859 10384380808688014716593789)
                    ·
                      refine ⟨3894142803258005518722671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10384380808688014716593789 3894142803258005518722671)
                      ·
                        rfl

theorem cell23_7583816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_7583816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583816 prefixEnd_7583816 := by exact prefixLift 7583816
  have htrace : WordTrace (prefixWord ++ tailWord_7583816) baseStart_7583816 baseEnd_7583816 := by
    simpa [prefixWord, tailWord_7583816, baseEnd_7583816] using wordTrace_append hprefix tailTrace_7583816
  have hstable : (prefixWord ++ tailWord_7583816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583816).length < 2 ^ (prefixWord ++ tailWord_7583816).sum := by decide
  have hdescent : baseEnd_7583816 < baseStart_7583816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583873 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_7583873 : Nat := 118140960795 + 7583873 * 2 ^ 59
def prefixEnd_7583873 : Nat := 4983230072969 + 3 ^ 40 * 7583873 * 2
def baseEnd_7583873 : Nat := 3894172071655311795709909

theorem tailTrace_7583873 : CollatzResearch.WordTrace tailWord_7583873 prefixEnd_7583873 3894172071655311795709909 := by
  unfold tailWord_7583873
  simp only [CollatzResearch.WordTrace]
  refine ⟨276606572453930818235588273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184404381635953878823725515 276606572453930818235588273)
  ·
    refine ⟨207454929340448113676691205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276606572453930818235588273 207454929340448113676691205)
    ·
      refine ⟨38897799251334021314379601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207454929340448113676691205 38897799251334021314379601)
      ·
        refine ⟨29173349438500515985784701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38897799251334021314379601 29173349438500515985784701)
        ·
          refine ⟨10940006039437693494669263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29173349438500515985784701 10940006039437693494669263)
          ·
            refine ⟨16410009059156540242003895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10940006039437693494669263 16410009059156540242003895)
            ·
              refine ⟨24615013588734810363005843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16410009059156540242003895 24615013588734810363005843)
              ·
                refine ⟨36922520383102215544508765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24615013588734810363005843 36922520383102215544508765)
                ·
                  refine ⟨13845945143663330829190787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36922520383102215544508765 13845945143663330829190787)
                  ·
                    refine ⟨20768917715494996243786181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13845945143663330829190787 20768917715494996243786181)
                    ·
                      refine ⟨3894172071655311795709909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20768917715494996243786181 3894172071655311795709909)
                      ·
                        rfl

theorem cell23_7583873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_7583873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583873 prefixEnd_7583873 := by exact prefixLift 7583873
  have htrace : WordTrace (prefixWord ++ tailWord_7583873) baseStart_7583873 baseEnd_7583873 := by
    simpa [prefixWord, tailWord_7583873, baseEnd_7583873] using wordTrace_append hprefix tailTrace_7583873
  have hstable : (prefixWord ++ tailWord_7583873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583873).length < 2 ^ (prefixWord ++ tailWord_7583873).sum := by decide
  have hdescent : baseEnd_7583873 < baseStart_7583873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583879 : List Nat := [1, 1, 4, 2, 1, 1, 4, 9]
def baseStart_7583879 : Nat := 118140960795 + 7583879 * 2 ^ 59
def prefixEnd_7583879 : Nat := 4983230072969 + 3 ^ 40 * 7583879 * 2
def baseEnd_7583879 : Nat := 144228709353305139712403

theorem tailTrace_7583879 : CollatzResearch.WordTrace tailWord_7583879 prefixEnd_7583879 144228709353305139712403 := by
  unfold tailWord_7583879
  simp only [CollatzResearch.WordTrace]
  refine ⟨276606791291909081260306691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184404527527939387506871127 276606791291909081260306691)
  ·
    refine ⟨414910186937863621890460037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276606791291909081260306691 414910186937863621890460037)
    ·
      refine ⟨77795660050849429104461257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 414910186937863621890460037 77795660050849429104461257)
      ·
        refine ⟨58346745038137071828345943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77795660050849429104461257 58346745038137071828345943)
        ·
          refine ⟨87520117557205607742518915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58346745038137071828345943 87520117557205607742518915)
          ·
            refine ⟨131280176335808411613778373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87520117557205607742518915 131280176335808411613778373)
            ·
              refine ⟨24615033062964077177583445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131280176335808411613778373 24615033062964077177583445)
              ·
                refine ⟨144228709353305139712403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24615033062964077177583445 144228709353305139712403)
                ·
                  rfl

theorem cell23_7583879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 9].length) (baseStart_7583879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583879 prefixEnd_7583879 := by exact prefixLift 7583879
  have htrace : WordTrace (prefixWord ++ tailWord_7583879) baseStart_7583879 baseEnd_7583879 := by
    simpa [prefixWord, tailWord_7583879, baseEnd_7583879] using wordTrace_append hprefix tailTrace_7583879
  have hstable : (prefixWord ++ tailWord_7583879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583879).length < 2 ^ (prefixWord ++ tailWord_7583879).sum := by decide
  have hdescent : baseEnd_7583879 < baseStart_7583879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583890 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_7583890 : Nat := 118140960795 + 7583890 * 2 ^ 59
def prefixEnd_7583890 : Nat := 4983230072969 + 3 ^ 40 * 7583890 * 2
def baseEnd_7583890 : Nat := 3894180800826438229197331

theorem tailTrace_7583890 : CollatzResearch.WordTrace tailWord_7583890 prefixEnd_7583890 3894180800826438229197331 := by
  unfold tailWord_7583890
  simp only [CollatzResearch.WordTrace]
  refine ⟨69151798123717307534739281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184404794996579486759304749 69151798123717307534739281)
  ·
    refine ⟨51863848592787980651054461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69151798123717307534739281 51863848592787980651054461)
    ·
      refine ⟨19448943222295492744145423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51863848592787980651054461 19448943222295492744145423)
      ·
        refine ⟨29173414833443239116218135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19448943222295492744145423 29173414833443239116218135)
        ·
          refine ⟨43760122250164858674327203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29173414833443239116218135 43760122250164858674327203)
          ·
            refine ⟨65640183375247288011490805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43760122250164858674327203 65640183375247288011490805)
            ·
              refine ⟨6153767191429433251077263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65640183375247288011490805 6153767191429433251077263)
              ·
                refine ⟨9230650787144149876615895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6153767191429433251077263 9230650787144149876615895)
                ·
                  refine ⟨13845976180716224814923843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9230650787144149876615895 13845976180716224814923843)
                  ·
                    refine ⟨20768964271074337222385765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13845976180716224814923843 20768964271074337222385765)
                    ·
                      refine ⟨3894180800826438229197331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20768964271074337222385765 3894180800826438229197331)
                      ·
                        rfl

theorem cell23_7583890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_7583890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583890 prefixEnd_7583890 := by exact prefixLift 7583890
  have htrace : WordTrace (prefixWord ++ tailWord_7583890) baseStart_7583890 baseEnd_7583890 := by
    simpa [prefixWord, tailWord_7583890, baseEnd_7583890] using wordTrace_append hprefix tailTrace_7583890
  have hstable : (prefixWord ++ tailWord_7583890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583890).length < 2 ^ (prefixWord ++ tailWord_7583890).sum := by decide
  have hdescent : baseEnd_7583890 < baseStart_7583890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583896 : List Nat := [2, 1, 2, 4, 4, 10]
def baseStart_7583896 : Nat := 118140960795 + 7583896 * 2 ^ 59
def prefixEnd_7583896 : Nat := 4983230072969 + 3 ^ 40 * 7583896 * 2
def baseEnd_7583896 : Nat := 16025448072882161340421

theorem tailTrace_7583896 : CollatzResearch.WordTrace tailWord_7583896 prefixEnd_7583896 16025448072882161340421 := by
  unfold tailWord_7583896
  simp only [CollatzResearch.WordTrace]
  refine ⟨138303705666423746581837771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184404940888564995442450361 138303705666423746581837771)
  ·
    refine ⟨207455558499635619872756657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138303705666423746581837771 207455558499635619872756657)
    ·
      refine ⟨155591668874726714904567493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207455558499635619872756657 155591668874726714904567493)
      ·
        refine ⟨29173437914011259044606405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155591668874726714904567493 29173437914011259044606405)
        ·
          refine ⟨5470019608877111070863701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29173437914011259044606405 5470019608877111070863701)
          ·
            refine ⟨16025448072882161340421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5470019608877111070863701 16025448072882161340421)
            ·
              rfl

theorem cell23_7583896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 10].length) (baseStart_7583896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583896 prefixEnd_7583896 := by exact prefixLift 7583896
  have htrace : WordTrace (prefixWord ++ tailWord_7583896) baseStart_7583896 baseEnd_7583896 := by
    simpa [prefixWord, tailWord_7583896, baseEnd_7583896] using wordTrace_append hprefix tailTrace_7583896
  have hstable : (prefixWord ++ tailWord_7583896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583896).length < 2 ^ (prefixWord ++ tailWord_7583896).sum := by decide
  have hdescent : baseEnd_7583896 < baseStart_7583896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583909 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_7583909 : Nat := 118140960795 + 7583909 * 2 ^ 59
def prefixEnd_7583909 : Nat := 4983230072969 + 3 ^ 40 * 7583909 * 2
def baseEnd_7583909 : Nat := 1298063518986291218286581

theorem tailTrace_7583909 : CollatzResearch.WordTrace tailWord_7583909 prefixEnd_7583909 1298063518986291218286581 := by
  unfold tailWord_7583909
  simp only [CollatzResearch.WordTrace]
  refine ⟨276607885481800396383898781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184405256987866930922599187 276607885481800396383898781)
  ·
    refine ⟨103727957055675148643962043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276607885481800396383898781 103727957055675148643962043)
    ·
      refine ⟨155591935583512722965943065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103727957055675148643962043 155591935583512722965943065)
      ·
        refine ⟨116693951687634542224457299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155591935583512722965943065 116693951687634542224457299)
        ·
          refine ⟨175040927531451813336685949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116693951687634542224457299 175040927531451813336685949)
          ·
            refine ⟨65640347824294430001257231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175040927531451813336685949 65640347824294430001257231)
            ·
              refine ⟨98460521736441645001885847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65640347824294430001257231 98460521736441645001885847)
              ·
                refine ⟨147690782604662467502828771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98460521736441645001885847 147690782604662467502828771)
                ·
                  refine ⟨221536173906993701254243157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147690782604662467502828771 221536173906993701254243157)
                  ·
                    refine ⟨1298063518986291218286581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 221536173906993701254243157 1298063518986291218286581)
                    ·
                      rfl

theorem cell23_7583909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_7583909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583909 prefixEnd_7583909 := by exact prefixLift 7583909
  have htrace : WordTrace (prefixWord ++ tailWord_7583909) baseStart_7583909 baseEnd_7583909 := by
    simpa [prefixWord, tailWord_7583909, baseEnd_7583909] using wordTrace_append hprefix tailTrace_7583909
  have hstable : (prefixWord ++ tailWord_7583909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583909).length < 2 ^ (prefixWord ++ tailWord_7583909).sum := by decide
  have hdescent : baseEnd_7583909 < baseStart_7583909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583919 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_7583919 : Nat := 118140960795 + 7583919 * 2 ^ 59
def prefixEnd_7583919 : Nat := 4983230072969 + 3 ^ 40 * 7583919 * 2
def baseEnd_7583919 : Nat := 3894195691765418615734697

theorem tailTrace_7583919 : CollatzResearch.WordTrace tailWord_7583919 prefixEnd_7583919 3894195691765418615734697 := by
  unfold tailWord_7583919
  simp only [CollatzResearch.WordTrace]
  refine ⟨276608250211764168091762811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184405500141176112061175207 276608250211764168091762811)
  ·
    refine ⟨414912375317646252137644217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276608250211764168091762811 414912375317646252137644217)
    ·
      refine ⟨311184281488234689103233163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414912375317646252137644217 311184281488234689103233163)
      ·
        refine ⟨466776422232352033654849745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311184281488234689103233163 466776422232352033654849745)
        ·
          refine ⟨350082316674264025241137309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466776422232352033654849745 350082316674264025241137309)
          ·
            refine ⟨131280868752849009465426491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350082316674264025241137309 131280868752849009465426491)
            ·
              refine ⟨196921303129273514198139737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131280868752849009465426491 196921303129273514198139737)
              ·
                refine ⟨147690977346955135648604803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196921303129273514198139737 147690977346955135648604803)
                ·
                  refine ⟨221536466020432703472907205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147690977346955135648604803 221536466020432703472907205)
                  ·
                    refine ⟨41538087378831131901170101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221536466020432703472907205 41538087378831131901170101)
                    ·
                      refine ⟨3894195691765418615734697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41538087378831131901170101 3894195691765418615734697)
                      ·
                        rfl

theorem cell23_7583919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_7583919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583919 prefixEnd_7583919 := by exact prefixLift 7583919
  have htrace : WordTrace (prefixWord ++ tailWord_7583919) baseStart_7583919 baseEnd_7583919 := by
    simpa [prefixWord, tailWord_7583919, baseEnd_7583919] using wordTrace_append hprefix tailTrace_7583919
  have hstable : (prefixWord ++ tailWord_7583919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583919).length < 2 ^ (prefixWord ++ tailWord_7583919).sum := by decide
  have hdescent : baseEnd_7583919 < baseStart_7583919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584050 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_7584050 : Nat := 118140960795 + 7584050 * 2 ^ 59
def prefixEnd_7584050 : Nat := 4983230072969 + 3 ^ 40 * 7584050 * 2
def baseEnd_7584050 : Nat := 1298087652577052534398865

theorem tailTrace_7584050 : CollatzResearch.WordTrace tailWord_7584050 prefixEnd_7584050 1298087652577052534398865 := by
  unfold tailWord_7584050
  simp only [CollatzResearch.WordTrace]
  refine ⟨69153257043572394366195401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184408685449526384976521069 69153257043572394366195401)
  ·
    refine ⟨51864942782679295774646551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69153257043572394366195401 51864942782679295774646551)
    ·
      refine ⟨77797414174018943661969827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51864942782679295774646551 77797414174018943661969827)
      ·
        refine ⟨116696121261028415492954741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77797414174018943661969827 116696121261028415492954741)
        ·
          refine ⟨10940261368221413952464507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116696121261028415492954741 10940261368221413952464507)
          ·
            refine ⟨16410392052332120928696761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10940261368221413952464507 16410392052332120928696761)
            ·
              refine ⟨12307794039249090696522571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16410392052332120928696761 12307794039249090696522571)
              ·
                refine ⟨18461691058873636044783857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307794039249090696522571 18461691058873636044783857)
                ·
                  refine ⟨13846268294155227033587893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18461691058873636044783857 13846268294155227033587893)
                  ·
                    refine ⟨1298087652577052534398865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13846268294155227033587893 1298087652577052534398865)
                    ·
                      rfl

theorem cell23_7584050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_7584050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584050 prefixEnd_7584050 := by exact prefixLift 7584050
  have htrace : WordTrace (prefixWord ++ tailWord_7584050) baseStart_7584050 baseEnd_7584050 := by
    simpa [prefixWord, tailWord_7584050, baseEnd_7584050] using wordTrace_append hprefix tailTrace_7584050
  have hstable : (prefixWord ++ tailWord_7584050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584050).length < 2 ^ (prefixWord ++ tailWord_7584050).sum := by decide
  have hdescent : baseEnd_7584050 < baseStart_7584050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584137 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 3]
def baseStart_7584137 : Nat := 118140960795 + 7584137 * 2 ^ 59
def prefixEnd_7584137 : Nat := 4983230072969 + 3 ^ 40 * 7584137 * 2
def baseEnd_7584137 : Nat := 3894307630548098762808695

theorem tailTrace_7584137 : CollatzResearch.WordTrace tailWord_7584137 prefixEnd_7584137 3894307630548098762808695 := by
  unfold tailWord_7584137
  simp only [CollatzResearch.WordTrace]
  refine ⟨276616201324974391323198665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184410800883316260882132443 276616201324974391323198665)
  ·
    refine ⟨207462150993730793492398999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276616201324974391323198665 207462150993730793492398999)
    ·
      refine ⟨311193226490596190238598499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207462150993730793492398999 311193226490596190238598499)
      ·
        refine ⟨466789839735894285357897749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311193226490596190238598499 466789839735894285357897749)
        ·
          refine ⟨21880773737620044626151457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 466789839735894285357897749 21880773737620044626151457)
          ·
            refine ⟨16410580303215033469613593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21880773737620044626151457 16410580303215033469613593)
            ·
              refine ⟨12307935227411275102210195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16410580303215033469613593 12307935227411275102210195)
              ·
                refine ⟨18461902841116912653315293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307935227411275102210195 18461902841116912653315293)
                ·
                  refine ⟨6923213565418842244993235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18461902841116912653315293 6923213565418842244993235)
                  ·
                    refine ⟨10384820348128263367489853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6923213565418842244993235 10384820348128263367489853)
                    ·
                      refine ⟨3894307630548098762808695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10384820348128263367489853 3894307630548098762808695)
                      ·
                        rfl

theorem cell23_7584137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 3].length) (baseStart_7584137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584137 prefixEnd_7584137 := by exact prefixLift 7584137
  have htrace : WordTrace (prefixWord ++ tailWord_7584137) baseStart_7584137 baseEnd_7584137 := by
    simpa [prefixWord, tailWord_7584137, baseEnd_7584137] using wordTrace_append hprefix tailTrace_7584137
  have hstable : (prefixWord ++ tailWord_7584137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584137).length < 2 ^ (prefixWord ++ tailWord_7584137).sum := by decide
  have hdescent : baseEnd_7584137 < baseStart_7584137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584157 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_7584157 : Nat := 118140960795 + 7584157 * 2 ^ 59
def prefixEnd_7584157 : Nat := 4983230072969 + 3 ^ 40 * 7584157 * 2
def baseEnd_7584157 : Nat := 1298105966720396228186201

theorem tailTrace_7584157 : CollatzResearch.WordTrace tailWord_7584157 prefixEnd_7584157 1298105966720396228186201 := by
  unfold tailWord_7584157
  simp only [CollatzResearch.WordTrace]
  refine ⟨276616930784901934738926725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184411287189934623159284483 276616930784901934738926725)
  ·
    refine ⟨51865674522169112763548761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276616930784901934738926725 51865674522169112763548761)
    ·
      refine ⟨38899255891626834572661571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51865674522169112763548761 38899255891626834572661571)
      ·
        refine ⟨58348883837440251858992357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38899255891626834572661571 58348883837440251858992357)
        ·
          refine ⟨10940415719520047223561067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58348883837440251858992357 10940415719520047223561067)
          ·
            refine ⟨16410623579280070835341601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10940415719520047223561067 16410623579280070835341601)
            ·
              refine ⟨12307967684460053126506201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16410623579280070835341601 12307967684460053126506201)
              ·
                refine ⟨9230975763345039844879651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12307967684460053126506201 9230975763345039844879651)
                ·
                  refine ⟨13846463645017559767319477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9230975763345039844879651 13846463645017559767319477)
                  ·
                    refine ⟨1298105966720396228186201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13846463645017559767319477 1298105966720396228186201)
                    ·
                      rfl

theorem cell23_7584157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_7584157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584157 prefixEnd_7584157 := by exact prefixLift 7584157
  have htrace : WordTrace (prefixWord ++ tailWord_7584157) baseStart_7584157 baseEnd_7584157 := by
    simpa [prefixWord, tailWord_7584157, baseEnd_7584157] using wordTrace_append hprefix tailTrace_7584157
  have hstable : (prefixWord ++ tailWord_7584157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584157).length < 2 ^ (prefixWord ++ tailWord_7584157).sum := by decide
  have hdescent : baseEnd_7584157 < baseStart_7584157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584160 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 4]
def baseStart_7584160 : Nat := 118140960795 + 7584160 * 2 ^ 59
def prefixEnd_7584160 : Nat := 4983230072969 + 3 ^ 40 * 7584160 * 2
def baseEnd_7584160 : Nat := 3894319440603152172821089

theorem tailTrace_7584160 : CollatzResearch.WordTrace tailWord_7584160 prefixEnd_7584160 3894319440603152172821089 := by
  unfold tailWord_7584160
  simp only [CollatzResearch.WordTrace]
  refine ⟨138308520101945533125642967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184411360135927377500857289 138308520101945533125642967)
  ·
    refine ⟨207462780152918299688464451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138308520101945533125642967 207462780152918299688464451)
    ·
      refine ⟨311194170229377449532696677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207462780152918299688464451 311194170229377449532696677)
      ·
        refine ⟨58348906918008271787380627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311194170229377449532696677 58348906918008271787380627)
        ·
          refine ⟨87523360377012407681070941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58348906918008271787380627 87523360377012407681070941)
          ·
            refine ⟨32821260141379652880401603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87523360377012407681070941 32821260141379652880401603)
            ·
              refine ⟨49231890212069479320602405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32821260141379652880401603 49231890212069479320602405)
              ·
                refine ⟨9230979414763027372612951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49231890212069479320602405 9230979414763027372612951)
                ·
                  refine ⟨13846469122144541058919427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9230979414763027372612951 13846469122144541058919427)
                  ·
                    refine ⟨20769703683216811588379141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13846469122144541058919427 20769703683216811588379141)
                    ·
                      refine ⟨3894319440603152172821089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20769703683216811588379141 3894319440603152172821089)
                      ·
                        rfl

theorem cell23_7584160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_7584160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584160 prefixEnd_7584160 := by exact prefixLift 7584160
  have htrace : WordTrace (prefixWord ++ tailWord_7584160) baseStart_7584160 baseEnd_7584160 := by
    simpa [prefixWord, tailWord_7584160, baseEnd_7584160] using wordTrace_append hprefix tailTrace_7584160
  have hstable : (prefixWord ++ tailWord_7584160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584160).length < 2 ^ (prefixWord ++ tailWord_7584160).sum := by decide
  have hdescent : baseEnd_7584160 < baseStart_7584160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584183 : List Nat := [1, 1, 3, 1, 3, 5, 9]
def baseStart_7584183 : Nat := 118140960795 + 7584183 * 2 ^ 59
def prefixEnd_7584183 : Nat := 4983230072969 + 3 ^ 40 * 7584183 * 2
def baseEnd_7584183 : Nat := 48078163588372908430043

theorem tailTrace_7584183 : CollatzResearch.WordTrace tailWord_7584183 prefixEnd_7584183 48078163588372908430043 := by
  unfold tailWord_7584183
  simp only [CollatzResearch.WordTrace]
  refine ⟨276617879082807741179373203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184411919388538494119582135 276617879082807741179373203)
  ·
    refine ⟨414926818624211611769059805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276617879082807741179373203 414926818624211611769059805)
    ·
      refine ⟨155597556984079354413397427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414926818624211611769059805 155597556984079354413397427)
      ·
        refine ⟨233396335476119031620096141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155597556984079354413397427 233396335476119031620096141)
        ·
          refine ⟨87523625803544636857536053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233396335476119031620096141 87523625803544636857536053)
          ·
            refine ⟨8205339919082309705394005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87523625803544636857536053 8205339919082309705394005)
            ·
              refine ⟨48078163588372908430043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8205339919082309705394005 48078163588372908430043)
              ·
                rfl

theorem cell23_7584183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 9].length) (baseStart_7584183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584183 prefixEnd_7584183 := by exact prefixLift 7584183
  have htrace : WordTrace (prefixWord ++ tailWord_7584183) baseStart_7584183 baseEnd_7584183 := by
    simpa [prefixWord, tailWord_7584183, baseEnd_7584183] using wordTrace_append hprefix tailTrace_7584183
  have hstable : (prefixWord ++ tailWord_7584183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584183).length < 2 ^ (prefixWord ++ tailWord_7584183).sum := by decide
  have hdescent : baseEnd_7584183 < baseStart_7584183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584227 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 3]
def baseStart_7584227 : Nat := 118140960795 + 7584227 * 2 ^ 59
def prefixEnd_7584227 : Nat := 4983230072969 + 3 ^ 40 * 7584227 * 2
def baseEnd_7584227 : Nat := 3894353843807003410683281

theorem tailTrace_7584227 : CollatzResearch.WordTrace tailWord_7584227 prefixEnd_7584227 3894353843807003410683281 := by
  unfold tailWord_7584227
  simp only [CollatzResearch.WordTrace]
  refine ⟨276619483894648336693974935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184412989263098891129316623 276619483894648336693974935)
  ·
    refine ⟨414929225841972505040962403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276619483894648336693974935 414929225841972505040962403)
    ·
      refine ⟨622393838762958757561443605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414929225841972505040962403 622393838762958757561443605)
      ·
        refine ⟨29174711192013691760692669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 622393838762958757561443605 29174711192013691760692669)
        ·
          refine ⟨10940516697005134410259751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29174711192013691760692669 10940516697005134410259751)
          ·
            refine ⟨16410775045507701615389627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10940516697005134410259751 16410775045507701615389627)
            ·
              refine ⟨24616162568261552423084441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16410775045507701615389627 24616162568261552423084441)
              ·
                refine ⟨18462121926196164317313331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24616162568261552423084441 18462121926196164317313331)
                ·
                  refine ⟨27693182889294246475969997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18462121926196164317313331 27693182889294246475969997)
                  ·
                    refine ⟨10384943583485342428488749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27693182889294246475969997 10384943583485342428488749)
                    ·
                      refine ⟨3894353843807003410683281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10384943583485342428488749 3894353843807003410683281)
                      ·
                        rfl

theorem cell23_7584227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_7584227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584227 prefixEnd_7584227 := by exact prefixLift 7584227
  have htrace : WordTrace (prefixWord ++ tailWord_7584227) baseStart_7584227 baseEnd_7584227 := by
    simpa [prefixWord, tailWord_7584227, baseEnd_7584227] using wordTrace_append hprefix tailTrace_7584227
  have hstable : (prefixWord ++ tailWord_7584227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584227).length < 2 ^ (prefixWord ++ tailWord_7584227).sum := by decide
  have hdescent : baseEnd_7584227 < baseStart_7584227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584243 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 2, 6]
def baseStart_7584243 : Nat := 118140960795 + 7584243 * 2 ^ 59
def prefixEnd_7584243 : Nat := 4983230072969 + 3 ^ 40 * 7584243 * 2
def baseEnd_7584243 : Nat := 1298120686499158449361069

theorem tailTrace_7584243 : CollatzResearch.WordTrace tailWord_7584243 prefixEnd_7584243 1298120686499158449361069 := by
  unfold tailWord_7584243
  simp only [CollatzResearch.WordTrace]
  refine ⟨276620067462590371426557383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184413378308393580951038255 276620067462590371426557383)
  ·
    refine ⟨414930101193885557139836075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276620067462590371426557383 414930101193885557139836075)
    ·
      refine ⟨622395151790828335709754113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414930101193885557139836075 622395151790828335709754113)
      ·
        refine ⟨466796363843121251782315585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622395151790828335709754113 466796363843121251782315585)
        ·
          refine ⟨350097272882340938836736689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466796363843121251782315585 350097272882340938836736689)
          ·
            refine ⟨262572954661755704127552517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350097272882340938836736689 262572954661755704127552517)
            ·
              refine ⟨49232428999079194523916097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262572954661755704127552517 49232428999079194523916097)
              ·
                refine ⟨36924321749309395892937073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49232428999079194523916097 36924321749309395892937073)
                ·
                  refine ⟨27693241311982046919702805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36924321749309395892937073 27693241311982046919702805)
                  ·
                    refine ⟨1298120686499158449361069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27693241311982046919702805 1298120686499158449361069)
                    ·
                      rfl

theorem cell23_7584243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 6].length) (baseStart_7584243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584243 prefixEnd_7584243 := by exact prefixLift 7584243
  have htrace : WordTrace (prefixWord ++ tailWord_7584243) baseStart_7584243 baseEnd_7584243 := by
    simpa [prefixWord, tailWord_7584243, baseEnd_7584243] using wordTrace_append hprefix tailTrace_7584243
  have hstable : (prefixWord ++ tailWord_7584243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584243).length < 2 ^ (prefixWord ++ tailWord_7584243).sum := by decide
  have hdescent : baseEnd_7584243 < baseStart_7584243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584260 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_7584260 : Nat := 118140960795 + 7584260 * 2 ^ 59
def prefixEnd_7584260 : Nat := 4983230072969 + 3 ^ 40 * 7584260 * 2
def baseEnd_7584260 : Nat := 1298123596222867260523543

theorem tailTrace_7584260 : CollatzResearch.WordTrace tailWord_7584260 prefixEnd_7584260 1298123596222867260523543 := by
  unfold tailWord_7584260
  simp only [CollatzResearch.WordTrace]
  refine ⟨138310343751764391664963117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184413791669019188886617489 138310343751764391664963117)
  ·
    refine ⟨51866378906911646874361169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138310343751764391664963117 51866378906911646874361169)
    ·
      refine ⟨38899784180183735155770877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51866378906911646874361169 38899784180183735155770877)
      ·
        refine ⟨14587419067568900683414079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38899784180183735155770877 14587419067568900683414079)
        ·
          refine ⟨21881128601353351025121119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14587419067568900683414079 21881128601353351025121119)
          ·
            refine ⟨32821692902030026537681679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21881128601353351025121119 32821692902030026537681679)
            ·
              refine ⟨49232539353045039806522519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32821692902030026537681679 49232539353045039806522519)
              ·
                refine ⟨73848809029567559709783779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49232539353045039806522519 73848809029567559709783779)
                ·
                  refine ⟨110773213544351339564675669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73848809029567559709783779 110773213544351339564675669)
                  ·
                    refine ⟨1298123596222867260523543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110773213544351339564675669 1298123596222867260523543)
                    ·
                      rfl

theorem cell23_7584260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_7584260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584260 prefixEnd_7584260 := by exact prefixLift 7584260
  have htrace : WordTrace (prefixWord ++ tailWord_7584260) baseStart_7584260 baseEnd_7584260 := by
    simpa [prefixWord, tailWord_7584260, baseEnd_7584260] using wordTrace_append hprefix tailTrace_7584260
  have hstable : (prefixWord ++ tailWord_7584260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584260).length < 2 ^ (prefixWord ++ tailWord_7584260).sum := by decide
  have hdescent : baseEnd_7584260 < baseStart_7584260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584267 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 1, 4, 2]
def baseStart_7584267 : Nat := 118140960795 + 7584267 * 2 ^ 59
def prefixEnd_7584267 : Nat := 4983230072969 + 3 ^ 40 * 7584267 * 2
def baseEnd_7584267 : Nat := 3894374383033183254183097

theorem tailTrace_7584267 : CollatzResearch.WordTrace tailWord_7584267 prefixEnd_7584267 3894374383033183254183097 := by
  unfold tailWord_7584267
  simp only [CollatzResearch.WordTrace]
  refine ⟨276620942814503423525431055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184413961876335615683620703 276620942814503423525431055)
  ·
    refine ⟨414931414221755135288146583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276620942814503423525431055 414931414221755135288146583)
    ·
      refine ⟨622397121332632702932219875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414931414221755135288146583 622397121332632702932219875)
      ·
        refine ⟨933595681998949054398329813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622397121332632702932219875 933595681998949054398329813)
        ·
          refine ⟨21881148796850368462460855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 933595681998949054398329813 21881148796850368462460855)
          ·
            refine ⟨32821723195275552693691283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21881148796850368462460855 32821723195275552693691283)
            ·
              refine ⟨49232584792913329040536925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32821723195275552693691283 49232584792913329040536925)
              ·
                refine ⟨18462219297342498390201347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49232584792913329040536925 18462219297342498390201347)
                ·
                  refine ⟨27693328946013747585302021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18462219297342498390201347 27693328946013747585302021)
                  ·
                    refine ⟨5192499177377577672244129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27693328946013747585302021 5192499177377577672244129)
                    ·
                      refine ⟨3894374383033183254183097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192499177377577672244129 3894374383033183254183097)
                      ·
                        rfl

theorem cell23_7584267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 4, 2].length) (baseStart_7584267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584267 prefixEnd_7584267 := by exact prefixLift 7584267
  have htrace : WordTrace (prefixWord ++ tailWord_7584267) baseStart_7584267 baseEnd_7584267 := by
    simpa [prefixWord, tailWord_7584267, baseEnd_7584267] using wordTrace_append hprefix tailTrace_7584267
  have hstable : (prefixWord ++ tailWord_7584267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584267).length < 2 ^ (prefixWord ++ tailWord_7584267).sum := by decide
  have hdescent : baseEnd_7584267 < baseStart_7584267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584288 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7584288 : Nat := 118140960795 + 7584288 * 2 ^ 59
def prefixEnd_7584288 : Nat := 4983230072969 + 3 ^ 40 * 7584288 * 2
def baseEnd_7584288 : Nat := 3894385166126927672020501

theorem tailTrace_7584288 : CollatzResearch.WordTrace tailWord_7584288 prefixEnd_7584288 3894385166126927672020501 := by
  unfold tailWord_7584288
  simp only [CollatzResearch.WordTrace]
  refine ⟨138310854373713672055972759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184414472498284896074630345 138310854373713672055972759)
  ·
    refine ⟨207466281560570508083959139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138310854373713672055972759 207466281560570508083959139)
    ·
      refine ⟨311199422340855762125938709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207466281560570508083959139 311199422340855762125938709)
      ·
        refine ⟨14587472922227613849653377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 311199422340855762125938709 14587472922227613849653377)
        ·
          refine ⟨10940604691670710387240033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14587472922227613849653377 10940604691670710387240033)
          ·
            refine ⟨8205453518753032790430025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10940604691670710387240033 8205453518753032790430025)
            ·
              refine ⟨6154090139064774592822519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8205453518753032790430025 6154090139064774592822519)
              ·
                refine ⟨9231135208597161889233779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6154090139064774592822519 9231135208597161889233779)
                ·
                  refine ⟨13846702812895742833850669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9231135208597161889233779 13846702812895742833850669)
                  ·
                    refine ⟨5192513554835903562694001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13846702812895742833850669 5192513554835903562694001)
                    ·
                      refine ⟨3894385166126927672020501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192513554835903562694001 3894385166126927672020501)
                      ·
                        rfl

theorem cell23_7584288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7584288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584288 prefixEnd_7584288 := by exact prefixLift 7584288
  have htrace : WordTrace (prefixWord ++ tailWord_7584288) baseStart_7584288 baseEnd_7584288 := by
    simpa [prefixWord, tailWord_7584288, baseEnd_7584288] using wordTrace_append hprefix tailTrace_7584288
  have hstable : (prefixWord ++ tailWord_7584288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584288).length < 2 ^ (prefixWord ++ tailWord_7584288).sum := by decide
  have hdescent : baseEnd_7584288 < baseStart_7584288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584295 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7584295 : Nat := 118140960795 + 7584295 * 2 ^ 59
def prefixEnd_7584295 : Nat := 4983230072969 + 3 ^ 40 * 7584295 * 2
def baseEnd_7584295 : Nat := 3894388760491509144632969

theorem tailTrace_7584295 : CollatzResearch.WordTrace tailWord_7584295 prefixEnd_7584295 3894388760491509144632969 := by
  unfold tailWord_7584295
  simp only [CollatzResearch.WordTrace]
  refine ⟨276621964058401984307450339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184414642705601322871633559 276621964058401984307450339)
  ·
    refine ⟨414932946087602976461175509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276621964058401984307450339 414932946087602976461175509)
    ·
      refine ⟨9724990923928194760808801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 414932946087602976461175509 9724990923928194760808801)
      ·
        refine ⟨7293743192946146070606601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9724990923928194760808801 7293743192946146070606601)
        ·
          refine ⟨5470307394709609552954951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7293743192946146070606601 5470307394709609552954951)
          ·
            refine ⟨8205461092064414329432427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470307394709609552954951 8205461092064414329432427)
            ·
              refine ⟨12308191638096621494148641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8205461092064414329432427 12308191638096621494148641)
              ·
                refine ⟨9231143728572466120611481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12308191638096621494148641 9231143728572466120611481)
                ·
                  refine ⟨6923357796429349590458611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9231143728572466120611481 6923357796429349590458611)
                  ·
                    refine ⟨10385036694644024385687917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6923357796429349590458611 10385036694644024385687917)
                    ·
                      refine ⟨3894388760491509144632969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10385036694644024385687917 3894388760491509144632969)
                      ·
                        rfl

theorem cell23_7584295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7584295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584295 prefixEnd_7584295 := by exact prefixLift 7584295
  have htrace : WordTrace (prefixWord ++ tailWord_7584295) baseStart_7584295 baseEnd_7584295 := by
    simpa [prefixWord, tailWord_7584295, baseEnd_7584295] using wordTrace_append hprefix tailTrace_7584295
  have hstable : (prefixWord ++ tailWord_7584295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584295).length < 2 ^ (prefixWord ++ tailWord_7584295).sum := by decide
  have hdescent : baseEnd_7584295 < baseStart_7584295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584317 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_7584317 : Nat := 118140960795 + 7584317 * 2 ^ 59
def prefixEnd_7584317 : Nat := 4983230072969 + 3 ^ 40 * 7584317 * 2
def baseEnd_7584317 : Nat := 3894400057065908058557867

theorem tailTrace_7584317 : CollatzResearch.WordTrace tailWord_7584317 prefixEnd_7584317 3894400057065908058557867 := by
  unfold tailWord_7584317
  simp only [CollatzResearch.WordTrace]
  refine ⟨276622766464322282064751205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184415177642881521376500803 276622766464322282064751205)
  ·
    refine ⟨51866768712060427887140851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276622766464322282064751205 51866768712060427887140851)
    ·
      refine ⟨77800153068090641830711277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51866768712060427887140851 77800153068090641830711277)
      ·
        refine ⟨29175057400533990686516729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77800153068090641830711277 29175057400533990686516729)
        ·
          refine ⟨21881293050400493014887547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29175057400533990686516729 21881293050400493014887547)
          ·
            refine ⟨32821939575600739522331321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21881293050400493014887547 32821939575600739522331321)
            ·
              refine ⟨24616454681700554641748491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32821939575600739522331321 24616454681700554641748491)
              ·
                refine ⟨36924682022550831962622737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24616454681700554641748491 36924682022550831962622737)
                ·
                  refine ⟨27693511516913123971967053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36924682022550831962622737 27693511516913123971967053)
                  ·
                    refine ⟨10385066818842421489487645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27693511516913123971967053 10385066818842421489487645)
                    ·
                      refine ⟨3894400057065908058557867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10385066818842421489487645 3894400057065908058557867)
                      ·
                        rfl

theorem cell23_7584317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_7584317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584317 prefixEnd_7584317 := by exact prefixLift 7584317
  have htrace : WordTrace (prefixWord ++ tailWord_7584317) baseStart_7584317 baseEnd_7584317 := by
    simpa [prefixWord, tailWord_7584317, baseEnd_7584317] using wordTrace_append hprefix tailTrace_7584317
  have hstable : (prefixWord ++ tailWord_7584317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584317).length < 2 ^ (prefixWord ++ tailWord_7584317).sum := by decide
  have hdescent : baseEnd_7584317 < baseStart_7584317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584318 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_7584318 : Nat := 118140960795 + 7584318 * 2 ^ 59
def prefixEnd_7584318 : Nat := 4983230072969 + 3 ^ 40 * 7584318 * 2
def baseEnd_7584318 : Nat := 3894400570546562554645363

theorem tailTrace_7584318 : CollatzResearch.WordTrace tailWord_7584318 prefixEnd_7584318 3894400570546562554645363 := by
  unfold tailWord_7584318
  simp only [CollatzResearch.WordTrace]
  refine ⟨34577850367164832404442201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184415201958212439490358405 34577850367164832404442201)
  ·
    refine ⟨25933387775373624303331651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34577850367164832404442201 25933387775373624303331651)
    ·
      refine ⟨38900081663060436454997477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25933387775373624303331651 38900081663060436454997477)
      ·
        refine ⟨7293765311823831835312027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38900081663060436454997477 7293765311823831835312027)
        ·
          refine ⟨10940647967735747752968041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7293765311823831835312027 10940647967735747752968041)
          ·
            refine ⟨8205485975801810814726031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10940647967735747752968041 8205485975801810814726031)
            ·
              refine ⟨12308228963702716222089047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8205485975801810814726031 12308228963702716222089047)
              ·
                refine ⟨18462343445554074333133571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12308228963702716222089047 18462343445554074333133571)
                ·
                  refine ⟨27693515168331111499700357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18462343445554074333133571 27693515168331111499700357)
                  ·
                    refine ⟨5192534094062083406193817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27693515168331111499700357 5192534094062083406193817)
                    ·
                      refine ⟨3894400570546562554645363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192534094062083406193817 3894400570546562554645363)
                      ·
                        rfl

theorem cell23_7584318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_7584318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584318 prefixEnd_7584318 := by exact prefixLift 7584318
  have htrace : WordTrace (prefixWord ++ tailWord_7584318) baseStart_7584318 baseEnd_7584318 := by
    simpa [prefixWord, tailWord_7584318, baseEnd_7584318] using wordTrace_append hprefix tailTrace_7584318
  have hstable : (prefixWord ++ tailWord_7584318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584318).length < 2 ^ (prefixWord ++ tailWord_7584318).sum := by decide
  have hdescent : baseEnd_7584318 < baseStart_7584318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584367 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 3, 4]
def baseStart_7584367 : Nat := 118140960795 + 7584367 * 2 ^ 59
def prefixEnd_7584367 : Nat := 4983230072969 + 3 ^ 40 * 7584367 * 2
def baseEnd_7584367 : Nat := 1298141910366210954310879

theorem tailTrace_7584367 : CollatzResearch.WordTrace tailWord_7584367 prefixEnd_7584367 1298141910366210954310879 := by
  unfold tailWord_7584367
  simp only [CollatzResearch.WordTrace]
  refine ⟨276624590114141140604071355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184416393409427427069380903 276624590114141140604071355)
  ·
    refine ⟨414936885171211710906107033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276624590114141140604071355 414936885171211710906107033)
    ·
      refine ⟨311202663878408783179580275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414936885171211710906107033 311202663878408783179580275)
      ·
        refine ⟨466803995817613174769370413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311202663878408783179580275 466803995817613174769370413)
        ·
          refine ⟨175051498431604940538513905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466803995817613174769370413 175051498431604940538513905)
          ·
            refine ⟨131288623823703705403885429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175051498431604940538513905 131288623823703705403885429)
            ·
              refine ⟨12308308483472222381614259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131288623823703705403885429 12308308483472222381614259)
              ·
                refine ⟨18462462725208333572421389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12308308483472222381614259 18462462725208333572421389)
                ·
                  refine ⟨6923423521953125089658021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18462462725208333572421389 6923423521953125089658021)
                  ·
                    refine ⟨1298141910366210954310879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6923423521953125089658021 1298141910366210954310879)
                    ·
                      rfl

theorem cell23_7584367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 4].length) (baseStart_7584367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584367 prefixEnd_7584367 := by exact prefixLift 7584367
  have htrace : WordTrace (prefixWord ++ tailWord_7584367) baseStart_7584367 baseEnd_7584367 := by
    simpa [prefixWord, tailWord_7584367, baseEnd_7584367] using wordTrace_append hprefix tailTrace_7584367
  have hstable : (prefixWord ++ tailWord_7584367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584367).length < 2 ^ (prefixWord ++ tailWord_7584367).sum := by decide
  have hdescent : baseEnd_7584367 < baseStart_7584367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584414 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_7584414 : Nat := 118140960795 + 7584414 * 2 ^ 59
def prefixEnd_7584414 : Nat := 4983230072969 + 3 ^ 40 * 7584414 * 2
def baseEnd_7584414 : Nat := 432716651632154908782769

theorem tailTrace_7584414 : CollatzResearch.WordTrace tailWord_7584414 prefixEnd_7584414 432716651632154908782769 := by
  unfold tailWord_7584414
  simp only [CollatzResearch.WordTrace]
  refine ⟨34578288043121358453879037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184417536229980578420688197 34578288043121358453879037)
  ·
    refine ⟨12966858016170509420204639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34578288043121358453879037 12966858016170509420204639)
    ·
      refine ⟨19450287024255764130306959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12966858016170509420204639 19450287024255764130306959)
      ·
        refine ⟨29175430536383646195460439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19450287024255764130306959 29175430536383646195460439)
        ·
          refine ⟨43763145804575469293190659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29175430536383646195460439 43763145804575469293190659)
          ·
            refine ⟨65644718706863203939785989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43763145804575469293190659 65644718706863203939785989)
            ·
              refine ⟨12308384757536850738709873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65644718706863203939785989 12308384757536850738709873)
              ·
                refine ⟨9231288568152638054032405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12308384757536850738709873 9231288568152638054032405)
                ·
                  refine ⟨432716651632154908782769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9231288568152638054032405 432716651632154908782769)
                  ·
                    rfl

theorem cell23_7584414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_7584414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584414 prefixEnd_7584414 := by exact prefixLift 7584414
  have htrace : WordTrace (prefixWord ++ tailWord_7584414) baseStart_7584414 baseEnd_7584414 := by
    simpa [prefixWord, tailWord_7584414, baseEnd_7584414] using wordTrace_append hprefix tailTrace_7584414
  have hstable : (prefixWord ++ tailWord_7584414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584414).length < 2 ^ (prefixWord ++ tailWord_7584414).sum := by decide
  have hdescent : baseEnd_7584414 < baseStart_7584414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584447 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_7584447 : Nat := 118140960795 + 7584447 * 2 ^ 59
def prefixEnd_7584447 : Nat := 4983230072969 + 3 ^ 40 * 7584447 * 2
def baseEnd_7584447 : Nat := 3894466809550992549932269

theorem tailTrace_7584447 : CollatzResearch.WordTrace tailWord_7584447 prefixEnd_7584447 3894466809550992549932269 := by
  unfold tailWord_7584447
  simp only [CollatzResearch.WordTrace]
  refine ⟨276627507953851314266983595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184418338635900876177989063 276627507953851314266983595)
  ·
    refine ⟨414941261930776971400475393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276627507953851314266983595 414941261930776971400475393)
    ·
      refine ⟨311205946448082728550356545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414941261930776971400475393 311205946448082728550356545)
      ·
        refine ⟨233404459836062046412767409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311205946448082728550356545 233404459836062046412767409)
        ·
          refine ⟨175053344877046534809575557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233404459836062046412767409 175053344877046534809575557)
          ·
            refine ⟨32822502164446225276795417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175053344877046534809575557 32822502164446225276795417)
            ·
              refine ⟨24616876623334668957596563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32822502164446225276795417 24616876623334668957596563)
              ·
                refine ⟨36925314935002003436394845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24616876623334668957596563 36925314935002003436394845)
                ·
                  refine ⟨13846993100625751288648067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36925314935002003436394845 13846993100625751288648067)
                  ·
                    refine ⟨20770489650938626932972101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13846993100625751288648067 20770489650938626932972101)
                    ·
                      refine ⟨3894466809550992549932269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20770489650938626932972101 3894466809550992549932269)
                      ·
                        rfl

theorem cell23_7584447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_7584447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584447 prefixEnd_7584447 := by exact prefixLift 7584447
  have htrace : WordTrace (prefixWord ++ tailWord_7584447) baseStart_7584447 baseEnd_7584447 := by
    simpa [prefixWord, tailWord_7584447, baseEnd_7584447] using wordTrace_append hprefix tailTrace_7584447
  have hstable : (prefixWord ++ tailWord_7584447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584447).length < 2 ^ (prefixWord ++ tailWord_7584447).sum := by decide
  have hdescent : baseEnd_7584447 < baseStart_7584447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584458 : List Nat := [3, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3]
def baseStart_7584458 : Nat := 118140960795 + 7584458 * 2 ^ 59
def prefixEnd_7584458 : Nat := 4983230072969 + 3 ^ 40 * 7584458 * 2
def baseEnd_7584458 : Nat := 3894472457838192006894719

theorem tailTrace_7584458 : CollatzResearch.WordTrace tailWord_7584458 prefixEnd_7584458 3894472457838192006894719 := by
  unfold tailWord_7584458
  simp only [CollatzResearch.WordTrace]
  refine ⟨69156977289202865786408507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184418606104540975430422685 69156977289202865786408507)
  ·
    refine ⟨103735465933804298679612761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69156977289202865786408507 103735465933804298679612761)
    ·
      refine ⟨77801599450353224009709571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103735465933804298679612761 77801599450353224009709571)
      ·
        refine ⟨116702399175529836014564357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77801599450353224009709571 116702399175529836014564357)
        ·
          refine ⟨21881699845411844252730817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116702399175529836014564357 21881699845411844252730817)
          ·
            refine ⟨16411274884058883189548113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21881699845411844252730817 16411274884058883189548113)
            ·
              refine ⟨12308456163044162392161085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16411274884058883189548113 12308456163044162392161085)
              ·
                refine ⟨4615671061141560897060407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12308456163044162392161085 4615671061141560897060407)
                ·
                  refine ⟨6923506591712341345590611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4615671061141560897060407 6923506591712341345590611)
                  ·
                    refine ⟨10385259887568512018385917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6923506591712341345590611 10385259887568512018385917)
                    ·
                      refine ⟨3894472457838192006894719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10385259887568512018385917 3894472457838192006894719)
                      ·
                        rfl

theorem cell23_7584458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_7584458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584458 prefixEnd_7584458 := by exact prefixLift 7584458
  have htrace : WordTrace (prefixWord ++ tailWord_7584458) baseStart_7584458 baseEnd_7584458 := by
    simpa [prefixWord, tailWord_7584458, baseEnd_7584458] using wordTrace_append hprefix tailTrace_7584458
  have hstable : (prefixWord ++ tailWord_7584458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584458).length < 2 ^ (prefixWord ++ tailWord_7584458).sum := by decide
  have hdescent : baseEnd_7584458 < baseStart_7584458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584480 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_7584480 : Nat := 118140960795 + 7584480 * 2 ^ 59
def prefixEnd_7584480 : Nat := 4983230072969 + 3 ^ 40 * 7584480 * 2
def baseEnd_7584480 : Nat := 3894483754412590920819617

theorem tailTrace_7584480 : CollatzResearch.WordTrace tailWord_7584480 prefixEnd_7584480 3894483754412590920819617 := by
  unfold tailWord_7584480
  simp only [CollatzResearch.WordTrace]
  refine ⟨138314355781365880451467447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184419141041821173935289929 138314355781365880451467447)
  ·
    refine ⟨207471533672048820677201171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138314355781365880451467447 207471533672048820677201171)
    ·
      refine ⟨311207300508073231015801757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207471533672048820677201171 311207300508073231015801757)
      ·
        refine ⟨116702737690527461630925659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311207300508073231015801757 116702737690527461630925659)
        ·
          refine ⟨175054106535791192446388489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116702737690527461630925659 175054106535791192446388489)
          ·
            refine ⟨131290579901843394334791367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175054106535791192446388489 131290579901843394334791367)
            ·
              refine ⟨196935869852765091502187051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131290579901843394334791367 196935869852765091502187051)
              ·
                refine ⟨295403804779147637253280577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196935869852765091502187051 295403804779147637253280577)
                ·
                  refine ⟨221552853584360727939960433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295403804779147637253280577 221552853584360727939960433)
                  ·
                    refine ⟨166164640188270545954970325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221552853584360727939960433 166164640188270545954970325)
                    ·
                      refine ⟨3894483754412590920819617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166164640188270545954970325 3894483754412590920819617)
                      ·
                        rfl

theorem cell23_7584480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_7584480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584480 prefixEnd_7584480 := by exact prefixLift 7584480
  have htrace : WordTrace (prefixWord ++ tailWord_7584480) baseStart_7584480 baseEnd_7584480 := by
    simpa [prefixWord, tailWord_7584480, baseEnd_7584480] using wordTrace_append hprefix tailTrace_7584480
  have hstable : (prefixWord ++ tailWord_7584480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584480).length < 2 ^ (prefixWord ++ tailWord_7584480).sum := by decide
  have hdescent : baseEnd_7584480 < baseStart_7584480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584481 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_7584481 : Nat := 118140960795 + 7584481 * 2 ^ 59
def prefixEnd_7584481 : Nat := 4983230072969 + 3 ^ 40 * 7584481 * 2
def baseEnd_7584481 : Nat := 3894484267893245416907113

theorem tailTrace_7584481 : CollatzResearch.WordTrace tailWord_7584481 prefixEnd_7584481 3894484267893245416907113 := by
  unfold tailWord_7584481
  simp only [CollatzResearch.WordTrace]
  refine ⟨276628748035728138073721297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184419165357152092049147531 276628748035728138073721297)
  ·
    refine ⟨207471561026796103555290973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276628748035728138073721297 207471561026796103555290973)
    ·
      refine ⟨77801835385048538833234115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207471561026796103555290973 77801835385048538833234115)
      ·
        refine ⟨116702753077572808249851173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77801835385048538833234115 116702753077572808249851173)
        ·
          refine ⟨21881766202044901546847095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116702753077572808249851173 21881766202044901546847095)
          ·
            refine ⟨32822649303067352320270643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21881766202044901546847095 32822649303067352320270643)
            ·
              refine ⟨49233973954601028480405965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32822649303067352320270643 49233973954601028480405965)
              ·
                refine ⟨18462740232975385680152237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49233973954601028480405965 18462740232975385680152237)
                ·
                  refine ⟨6923527587365769630057089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18462740232975385680152237 6923527587365769630057089)
                  ·
                    refine ⟨5192645690524327222542817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6923527587365769630057089 5192645690524327222542817)
                    ·
                      refine ⟨3894484267893245416907113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192645690524327222542817 3894484267893245416907113)
                      ·
                        rfl

theorem cell23_7584481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_7584481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584481 prefixEnd_7584481 := by exact prefixLift 7584481
  have htrace : WordTrace (prefixWord ++ tailWord_7584481) baseStart_7584481 baseEnd_7584481 := by
    simpa [prefixWord, tailWord_7584481, baseEnd_7584481] using wordTrace_append hprefix tailTrace_7584481
  have hstable : (prefixWord ++ tailWord_7584481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584481).length < 2 ^ (prefixWord ++ tailWord_7584481).sum := by decide
  have hdescent : baseEnd_7584481 < baseStart_7584481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584494 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_7584494 : Nat := 118140960795 + 7584494 * 2 ^ 59
def prefixEnd_7584494 : Nat := 4983230072969 + 3 ^ 40 * 7584494 * 2
def baseEnd_7584494 : Nat := 3894490943141753866044553

theorem tailTrace_7584494 : CollatzResearch.WordTrace tailWord_7584494 prefixEnd_7584494 3894490943141753866044553 := by
  unfold tailWord_7584494
  simp only [CollatzResearch.WordTrace]
  refine ⟨34578652773085130161743067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184419481456454027529296357 34578652773085130161743067)
  ·
    refine ⟨51867979159627695242614601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34578652773085130161743067 51867979159627695242614601)
    ·
      refine ⟨38900984369720771431960951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51867979159627695242614601 38900984369720771431960951)
      ·
        refine ⟨58351476554581157147941427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38900984369720771431960951 58351476554581157147941427)
        ·
          refine ⟨87527214831871735721912141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58351476554581157147941427 87527214831871735721912141)
          ·
            refine ⟨32822705561951900895717053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87527214831871735721912141 32822705561951900895717053)
            ·
              refine ⟨12308514585731962835893895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32822705561951900895717053 12308514585731962835893895)
              ·
                refine ⟨18462771878597944253840843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12308514585731962835893895 18462771878597944253840843)
                ·
                  refine ⟨27694157817896916380761265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18462771878597944253840843 27694157817896916380761265)
                  ·
                    refine ⟨20770618363422687285570949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27694157817896916380761265 20770618363422687285570949)
                    ·
                      refine ⟨3894490943141753866044553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20770618363422687285570949 3894490943141753866044553)
                      ·
                        rfl

theorem cell23_7584494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_7584494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584494 prefixEnd_7584494 := by exact prefixLift 7584494
  have htrace : WordTrace (prefixWord ++ tailWord_7584494) baseStart_7584494 baseEnd_7584494 := by
    simpa [prefixWord, tailWord_7584494, baseEnd_7584494] using wordTrace_append hprefix tailTrace_7584494
  have hstable : (prefixWord ++ tailWord_7584494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584494).length < 2 ^ (prefixWord ++ tailWord_7584494).sum := by decide
  have hdescent : baseEnd_7584494 < baseStart_7584494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584524 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 5, 3, 2]
def baseStart_7584524 : Nat := 118140960795 + 7584524 * 2 ^ 59
def prefixEnd_7584524 : Nat := 4983230072969 + 3 ^ 40 * 7584524 * 2
def baseEnd_7584524 : Nat := 3894506347561388748669415

theorem tailTrace_7584524 : CollatzResearch.WordTrace tailWord_7584524 prefixEnd_7584524 3894506347561388748669415 := by
  unfold tailWord_7584524
  simp only [CollatzResearch.WordTrace]
  refine ⟨138315158187286178208768313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184420210916381570945024417 138315158187286178208768313)
  ·
    refine ⟨103736368640464633656576235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138315158187286178208768313 103736368640464633656576235)
    ·
      refine ⟨155604552960696950484864353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103736368640464633656576235 155604552960696950484864353)
      ·
        refine ⟨116703414720522712863648265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155604552960696950484864353 116703414720522712863648265)
        ·
          refine ⟨87527561040392034647736199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116703414720522712863648265 87527561040392034647736199)
          ·
            refine ⟨131291341560588051971604299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87527561040392034647736199 131291341560588051971604299)
            ·
              refine ⟨196937012340882077957406449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131291341560588051971604299 196937012340882077957406449)
              ·
                refine ⟨147702759255661558468054837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196937012340882077957406449 147702759255661558468054837)
                ·
                  refine ⟨13847133680218271106380141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147702759255661558468054837 13847133680218271106380141)
                  ·
                    refine ⟨5192675130081851664892553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13847133680218271106380141 5192675130081851664892553)
                    ·
                      refine ⟨3894506347561388748669415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192675130081851664892553 3894506347561388748669415)
                      ·
                        rfl

theorem cell23_7584524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_7584524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584524 prefixEnd_7584524 := by exact prefixLift 7584524
  have htrace : WordTrace (prefixWord ++ tailWord_7584524) baseStart_7584524 baseEnd_7584524 := by
    simpa [prefixWord, tailWord_7584524, baseEnd_7584524] using wordTrace_append hprefix tailTrace_7584524
  have hstable : (prefixWord ++ tailWord_7584524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584524).length < 2 ^ (prefixWord ++ tailWord_7584524).sum := by decide
  have hdescent : baseEnd_7584524 < baseStart_7584524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584548 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_7584548 : Nat := 118140960795 + 7584548 * 2 ^ 59
def prefixEnd_7584548 : Nat := 4983230072969 + 3 ^ 40 * 7584548 * 2
def baseEnd_7584548 : Nat := 3894518671097096654769305

theorem tailTrace_7584548 : CollatzResearch.WordTrace tailWord_7584548 prefixEnd_7584548 3894518671097096654769305 := by
  unfold tailWord_7584548
  simp only [CollatzResearch.WordTrace]
  refine ⟨138315595863242704258205149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184420794484323605677606865 138315595863242704258205149)
  ·
    refine ⟨51868348448716014096826931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138315595863242704258205149 51868348448716014096826931)
    ·
      refine ⟨77802522673074021145240397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51868348448716014096826931 77802522673074021145240397)
      ·
        refine ⟨29175946002402757929465149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77802522673074021145240397 29175946002402757929465149)
        ·
          refine ⟨10940979750901034223549431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29175946002402757929465149 10940979750901034223549431)
          ·
            refine ⟨16411469626351551335324147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10940979750901034223549431 16411469626351551335324147)
            ·
              refine ⟨24617204439527327002986221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16411469626351551335324147 24617204439527327002986221)
              ·
                refine ⟨9231451664822747626119833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24617204439527327002986221 9231451664822747626119833)
                ·
                  refine ⟨6923588748617060719589875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9231451664822747626119833 6923588748617060719589875)
                  ·
                    refine ⟨10385383122925591079384813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6923588748617060719589875 10385383122925591079384813)
                    ·
                      refine ⟨3894518671097096654769305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10385383122925591079384813 3894518671097096654769305)
                      ·
                        rfl

theorem cell23_7584548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_7584548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584548 prefixEnd_7584548 := by exact prefixLift 7584548
  have htrace : WordTrace (prefixWord ++ tailWord_7584548) baseStart_7584548 baseEnd_7584548 := by
    simpa [prefixWord, tailWord_7584548, baseEnd_7584548] using wordTrace_append hprefix tailTrace_7584548
  have hstable : (prefixWord ++ tailWord_7584548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584548).length < 2 ^ (prefixWord ++ tailWord_7584548).sum := by decide
  have hdescent : baseEnd_7584548 < baseStart_7584548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584558 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7584558 : Nat := 118140960795 + 7584558 * 2 ^ 59
def prefixEnd_7584558 : Nat := 4983230072969 + 3 ^ 40 * 7584558 * 2
def baseEnd_7584558 : Nat := 3894523805903641615644259

theorem tailTrace_7584558 : CollatzResearch.WordTrace tailWord_7584558 prefixEnd_7584558 3894523805903641615644259 := by
  unfold tailWord_7584558
  simp only [CollatzResearch.WordTrace]
  refine ⟨34578944557056147528034291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184421037637632786816182885 34578944557056147528034291)
  ·
    refine ⟨51868416835584221292051437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34578944557056147528034291 51868416835584221292051437)
    ·
      refine ⟨19450656313344082984519289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51868416835584221292051437 19450656313344082984519289)
      ·
        refine ⟨14587992235008062238389467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19450656313344082984519289 14587992235008062238389467)
        ·
          refine ⟨21881988352512093357584201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14587992235008062238389467 21881988352512093357584201)
          ·
            refine ⟨16411491264384070018188151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21881988352512093357584201 16411491264384070018188151)
            ·
              refine ⟨24617236896576105027282227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16411491264384070018188151 24617236896576105027282227)
              ·
                refine ⟨36925855344864157540923341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24617236896576105027282227 36925855344864157540923341)
                ·
                  refine ⟨13847195754324059077846253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36925855344864157540923341 13847195754324059077846253)
                  ·
                    refine ⟨5192698407871522154192345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13847195754324059077846253 5192698407871522154192345)
                    ·
                      refine ⟨3894523805903641615644259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192698407871522154192345 3894523805903641615644259)
                      ·
                        rfl

theorem cell23_7584558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7584558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584558 prefixEnd_7584558 := by exact prefixLift 7584558
  have htrace : WordTrace (prefixWord ++ tailWord_7584558) baseStart_7584558 baseEnd_7584558 := by
    simpa [prefixWord, tailWord_7584558, baseEnd_7584558] using wordTrace_append hprefix tailTrace_7584558
  have hstable : (prefixWord ++ tailWord_7584558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584558).length < 2 ^ (prefixWord ++ tailWord_7584558).sum := by decide
  have hdescent : baseEnd_7584558 < baseStart_7584558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584582 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7584582 : Nat := 118140960795 + 7584582 * 2 ^ 59
def prefixEnd_7584582 : Nat := 4983230072969 + 3 ^ 40 * 7584582 * 2
def baseEnd_7584582 : Nat := 3894536129439349521744149

theorem tailTrace_7584582 : CollatzResearch.WordTrace tailWord_7584582 prefixEnd_7584582 3894536129439349521744149 := by
  unfold tailWord_7584582
  simp only [CollatzResearch.WordTrace]
  refine ⟨8644763494011319760098375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184421621205574821548765333 8644763494011319760098375)
  ·
    refine ⟨12967145241016979640147563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8644763494011319760098375 12967145241016979640147563)
    ·
      refine ⟨19450717861525469460221345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12967145241016979640147563 19450717861525469460221345)
      ·
        refine ⟨14588038396144102095166009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19450717861525469460221345 14588038396144102095166009)
        ·
          refine ⟨10941028797108076571374507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14588038396144102095166009 10941028797108076571374507)
          ·
            refine ⟨16411543195662114857061761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10941028797108076571374507 16411543195662114857061761)
            ·
              refine ⟨12308657396746586142796321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16411543195662114857061761 12308657396746586142796321)
              ·
                refine ⟨9231493047559939607097241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12308657396746586142796321 9231493047559939607097241)
                ·
                  refine ⟨6923619785669954705322931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9231493047559939607097241 6923619785669954705322931)
                  ·
                    refine ⟨10385429678504932057984397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6923619785669954705322931 10385429678504932057984397)
                    ·
                      refine ⟨3894536129439349521744149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10385429678504932057984397 3894536129439349521744149)
                      ·
                        rfl

theorem cell23_7584582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7584582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584582 prefixEnd_7584582 := by exact prefixLift 7584582
  have htrace : WordTrace (prefixWord ++ tailWord_7584582) baseStart_7584582 baseEnd_7584582 := by
    simpa [prefixWord, tailWord_7584582, baseEnd_7584582] using wordTrace_append hprefix tailTrace_7584582
  have hstable : (prefixWord ++ tailWord_7584582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584582).length < 2 ^ (prefixWord ++ tailWord_7584582).sum := by decide
  have hdescent : baseEnd_7584582 < baseStart_7584582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584587 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 3]
def baseStart_7584587 : Nat := 118140960795 + 7584587 * 2 ^ 59
def prefixEnd_7584587 : Nat := 4983230072969 + 3 ^ 40 * 7584587 * 2
def baseEnd_7584587 : Nat := 3894538696842622002181625

theorem tailTrace_7584587 : CollatzResearch.WordTrace tailWord_7584587 prefixEnd_7584587 3894538696842622002181625 := by
  unfold tailWord_7584587
  simp only [CollatzResearch.WordTrace]
  refine ⟨276632614173344118177080015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184421742782229412118053343 276632614173344118177080015)
  ·
    refine ⟨414948921260016177265620023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276632614173344118177080015 414948921260016177265620023)
    ·
      refine ⟨622423381890024265898430035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414948921260016177265620023 622423381890024265898430035)
      ·
        refine ⟨933635072835036398847645053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622423381890024265898430035 933635072835036398847645053)
        ·
          refine ⟨350113152313138649567866895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 933635072835036398847645053 350113152313138649567866895)
          ·
            refine ⟨525169728469707974351800343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350113152313138649567866895 525169728469707974351800343)
            ·
              refine ⟨787754592704561961527700515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525169728469707974351800343 787754592704561961527700515)
              ·
                refine ⟨1181631889056842942291550773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787754592704561961527700515 1181631889056842942291550773)
                ·
                  refine ⟨110777989599079025839832885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181631889056842942291550773 110777989599079025839832885)
                  ·
                    refine ⟨10385436524913658672484333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110777989599079025839832885 10385436524913658672484333)
                    ·
                      refine ⟨3894538696842622002181625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10385436524913658672484333 3894538696842622002181625)
                      ·
                        rfl

theorem cell23_7584587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 3].length) (baseStart_7584587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584587 prefixEnd_7584587 := by exact prefixLift 7584587
  have htrace : WordTrace (prefixWord ++ tailWord_7584587) baseStart_7584587 baseEnd_7584587 := by
    simpa [prefixWord, tailWord_7584587, baseEnd_7584587] using wordTrace_append hprefix tailTrace_7584587
  have hstable : (prefixWord ++ tailWord_7584587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584587).length < 2 ^ (prefixWord ++ tailWord_7584587).sum := by decide
  have hdescent : baseEnd_7584587 < baseStart_7584587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584588 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 2, 2, 2]
def baseStart_7584588 : Nat := 118140960795 + 7584588 * 2 ^ 59
def prefixEnd_7584588 : Nat := 4983230072969 + 3 ^ 40 * 7584588 * 2
def baseEnd_7584588 : Nat := 3894539210323276498269121

theorem tailTrace_7584588 : CollatzResearch.WordTrace tailWord_7584588 prefixEnd_7584588 3894539210323276498269121 := by
  unfold tailWord_7584588
  simp only [CollatzResearch.WordTrace]
  refine ⟨138316325323170247673933209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184421767097560330231910945 138316325323170247673933209)
  ·
    refine ⟨103737243992377685755449907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138316325323170247673933209 103737243992377685755449907)
    ·
      refine ⟨155605865988566528633174861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103737243992377685755449907 155605865988566528633174861)
      ·
        refine ⟨58352199745712448237440573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155605865988566528633174861 58352199745712448237440573)
        ·
          refine ⟨21882074904642168089040215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58352199745712448237440573 21882074904642168089040215)
          ·
            refine ⟨32823112356963252133560323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21882074904642168089040215 32823112356963252133560323)
            ·
              refine ⟨49234668535444878200340485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32823112356963252133560323 49234668535444878200340485)
              ·
                refine ⟨9231500350395914662563841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49234668535444878200340485 9231500350395914662563841)
                ·
                  refine ⟨6923625262796935996922881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9231500350395914662563841 6923625262796935996922881)
                  ·
                    refine ⟨5192718947097701997692161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6923625262796935996922881 5192718947097701997692161)
                    ·
                      refine ⟨3894539210323276498269121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192718947097701997692161 3894539210323276498269121)
                      ·
                        rfl

theorem cell23_7584588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_7584588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584588 prefixEnd_7584588 := by exact prefixLift 7584588
  have htrace : WordTrace (prefixWord ++ tailWord_7584588) baseStart_7584588 baseEnd_7584588 := by
    simpa [prefixWord, tailWord_7584588, baseEnd_7584588] using wordTrace_append hprefix tailTrace_7584588
  have hstable : (prefixWord ++ tailWord_7584588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584588).length < 2 ^ (prefixWord ++ tailWord_7584588).sum := by decide
  have hdescent : baseEnd_7584588 < baseStart_7584588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584607 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 1, 7]
def baseStart_7584607 : Nat := 118140960795 + 7584607 * 2 ^ 59
def prefixEnd_7584607 : Nat := 4983230072969 + 3 ^ 40 * 7584607 * 2
def baseEnd_7584607 : Nat := 1298182988818570641310511

theorem tailTrace_7584607 : CollatzResearch.WordTrace tailWord_7584607 prefixEnd_7584607 1298182988818570641310511 := by
  unfold tailWord_7584607
  simp only [CollatzResearch.WordTrace]
  refine ⟨276633343633271661592808075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184422229088847774395205383 276633343633271661592808075)
  ·
    refine ⟨414950015449907492389212113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276633343633271661592808075 414950015449907492389212113)
    ·
      refine ⟨311212511587430619291909085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414950015449907492389212113 311212511587430619291909085)
      ·
        refine ⟨116704691845286482234465907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311212511587430619291909085 116704691845286482234465907)
        ·
          refine ⟨175057037767929723351698861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116704691845286482234465907 175057037767929723351698861)
          ·
            refine ⟨65646389162973646256887073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175057037767929723351698861 65646389162973646256887073)
            ·
              refine ⟨49234791872230234692665305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65646389162973646256887073 49234791872230234692665305)
              ·
                refine ⟨36926093904172676019498979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49234791872230234692665305 36926093904172676019498979)
                ·
                  refine ⟨55389140856259014029248469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36926093904172676019498979 55389140856259014029248469)
                  ·
                    refine ⟨1298182988818570641310511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55389140856259014029248469 1298182988818570641310511)
                    ·
                      rfl

theorem cell23_7584607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_7584607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584607 prefixEnd_7584607 := by exact prefixLift 7584607
  have htrace : WordTrace (prefixWord ++ tailWord_7584607) baseStart_7584607 baseEnd_7584607 := by
    simpa [prefixWord, tailWord_7584607, baseEnd_7584607] using wordTrace_append hprefix tailTrace_7584607
  have hstable : (prefixWord ++ tailWord_7584607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584607).length < 2 ^ (prefixWord ++ tailWord_7584607).sum := by decide
  have hdescent : baseEnd_7584607 < baseStart_7584607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584624 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 2, 5]
def baseStart_7584624 : Nat := 118140960795 + 7584624 * 2 ^ 59
def prefixEnd_7584624 : Nat := 4983230072969 + 3 ^ 40 * 7584624 * 2
def baseEnd_7584624 : Nat := 1298185898542279452472985

theorem tailTrace_7584624 : CollatzResearch.WordTrace tailWord_7584624 prefixEnd_7584624 1298185898542279452472985 := by
  unfold tailWord_7584624
  simp only [CollatzResearch.WordTrace]
  refine ⟨138316981837105036748088463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184422642449473382330784617 138316981837105036748088463)
  ·
    refine ⟨207475472755657555122132695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138316981837105036748088463 207475472755657555122132695)
    ·
      refine ⟨311213209133486332683199043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207475472755657555122132695 311213209133486332683199043)
      ·
        refine ⟨466819813700229499024798565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311213209133486332683199043 466819813700229499024798565)
        ·
          refine ⟨87528715068793031067149731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466819813700229499024798565 87528715068793031067149731)
          ·
            refine ⟨131293072603189546600724597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87528715068793031067149731 131293072603189546600724597)
            ·
              refine ⟨12308725556549019993817931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131293072603189546600724597 12308725556549019993817931)
              ·
                refine ⟨18463088334823529990726897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12308725556549019993817931 18463088334823529990726897)
                ·
                  refine ⟨13847316251117647493045173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18463088334823529990726897 13847316251117647493045173)
                  ·
                    refine ⟨1298185898542279452472985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13847316251117647493045173 1298185898542279452472985)
                    ·
                      rfl

theorem cell23_7584624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_7584624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584624 prefixEnd_7584624 := by exact prefixLift 7584624
  have htrace : WordTrace (prefixWord ++ tailWord_7584624) baseStart_7584624 baseEnd_7584624 := by
    simpa [prefixWord, tailWord_7584624, baseEnd_7584624] using wordTrace_append hprefix tailTrace_7584624
  have hstable : (prefixWord ++ tailWord_7584624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584624).length < 2 ^ (prefixWord ++ tailWord_7584624).sum := by decide
  have hdescent : baseEnd_7584624 < baseStart_7584624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584644 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_7584644 : Nat := 118140960795 + 7584644 * 2 ^ 59
def prefixEnd_7584644 : Nat := 4983230072969 + 3 ^ 40 * 7584644 * 2
def baseEnd_7584644 : Nat := 3894567965239928279168863

theorem tailTrace_7584644 : CollatzResearch.WordTrace tailWord_7584644 prefixEnd_7584644 3894567965239928279168863 := by
  unfold tailWord_7584644
  simp only [CollatzResearch.WordTrace]
  refine ⟨138317346567068808455952493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184423128756091744607936657 138317346567068808455952493)
  ·
    refine ⟨51869004962650803170982185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138317346567068808455952493 51869004962650803170982185)
    ·
      refine ⟨38901753721988102378236639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51869004962650803170982185 38901753721988102378236639)
      ·
        refine ⟨58352630582982153567354959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38901753721988102378236639 58352630582982153567354959)
        ·
          refine ⟨87528945874473230351032439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58352630582982153567354959 87528945874473230351032439)
          ·
            refine ⟨131293418811709845526548659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87528945874473230351032439 131293418811709845526548659)
            ·
              refine ⟨196940128217564768289822989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131293418811709845526548659 196940128217564768289822989)
              ·
                refine ⟨73852548081586788108683621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196940128217564768289822989 73852548081586788108683621)
                ·
                  refine ⟨13847352765297522770378179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73852548081586788108683621 13847352765297522770378179)
                  ·
                    refine ⟨20771029147946284155567269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13847352765297522770378179 20771029147946284155567269)
                    ·
                      refine ⟨3894567965239928279168863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20771029147946284155567269 3894567965239928279168863)
                      ·
                        rfl

theorem cell23_7584644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_7584644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584644 prefixEnd_7584644 := by exact prefixLift 7584644
  have htrace : WordTrace (prefixWord ++ tailWord_7584644) baseStart_7584644 baseEnd_7584644 := by
    simpa [prefixWord, tailWord_7584644, baseEnd_7584644] using wordTrace_append hprefix tailTrace_7584644
  have hstable : (prefixWord ++ tailWord_7584644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584644).length < 2 ^ (prefixWord ++ tailWord_7584644).sum := by decide
  have hdescent : baseEnd_7584644 < baseStart_7584644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584657 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_7584657 : Nat := 118140960795 + 7584657 * 2 ^ 59
def prefixEnd_7584657 : Nat := 4983230072969 + 3 ^ 40 * 7584657 * 2
def baseEnd_7584657 : Nat := 3894574640488436728306303

theorem tailTrace_7584657 : CollatzResearch.WordTrace tailWord_7584657 prefixEnd_7584657 3894574640488436728306303 := by
  unfold tailWord_7584657
  simp only [CollatzResearch.WordTrace]
  refine ⟨276635167283090520132128225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184423444855393680088085483 276635167283090520132128225)
  ·
    refine ⟨207476375462317890099096169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276635167283090520132128225 207476375462317890099096169)
    ·
      refine ⟨155607281596738417574322127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207476375462317890099096169 155607281596738417574322127)
      ·
        refine ⟨233410922395107626361483191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155607281596738417574322127 233410922395107626361483191)
        ·
          refine ⟨350116383592661439542224787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233410922395107626361483191 350116383592661439542224787)
          ·
            refine ⟨525174575388992159313337181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350116383592661439542224787 525174575388992159313337181)
            ·
              refine ⟨196940465770872059742501443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525174575388992159313337181 196940465770872059742501443)
              ·
                refine ⟨295410698656308089613752165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196940465770872059742501443 295410698656308089613752165)
                ·
                  refine ⟨55389505998057766802578531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295410698656308089613752165 55389505998057766802578531)
                  ·
                    refine ⟨83084258997086650203867797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55389505998057766802578531 83084258997086650203867797)
                    ·
                      refine ⟨3894574640488436728306303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83084258997086650203867797 3894574640488436728306303)
                      ·
                        rfl

theorem cell23_7584657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_7584657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584657 prefixEnd_7584657 := by exact prefixLift 7584657
  have htrace : WordTrace (prefixWord ++ tailWord_7584657) baseStart_7584657 baseEnd_7584657 := by
    simpa [prefixWord, tailWord_7584657, baseEnd_7584657] using wordTrace_append hprefix tailTrace_7584657
  have hstable : (prefixWord ++ tailWord_7584657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584657).length < 2 ^ (prefixWord ++ tailWord_7584657).sum := by decide
  have hdescent : baseEnd_7584657 < baseStart_7584657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584661 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_7584661 : Nat := 118140960795 + 7584661 * 2 ^ 59
def prefixEnd_7584661 : Nat := 4983230072969 + 3 ^ 40 * 7584661 * 2
def baseEnd_7584661 : Nat := 3894576694411054712656285

theorem tailTrace_7584661 : CollatzResearch.WordTrace tailWord_7584661 prefixEnd_7584661 3894576694411054712656285 := by
  unfold tailWord_7584661
  simp only [CollatzResearch.WordTrace]
  refine ⟨276635313175076028815273837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184423542116717352543515891 276635313175076028815273837)
  ·
    refine ⟨103738242440653510805727689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276635313175076028815273837 103738242440653510805727689)
    ·
      refine ⟨77803681830490133104295767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103738242440653510805727689 77803681830490133104295767)
      ·
        refine ⟨116705522745735199656443651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77803681830490133104295767 116705522745735199656443651)
        ·
          refine ⟨175058284118602799484665477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116705522745735199656443651 175058284118602799484665477)
          ·
            refine ⟨32823428272238024903374777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175058284118602799484665477 32823428272238024903374777)
            ·
              refine ⟨24617571204178518677531083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32823428272238024903374777 24617571204178518677531083)
              ·
                refine ⟨36926356806267778016296625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24617571204178518677531083 36926356806267778016296625)
                ·
                  refine ⟨27694767604700833512222469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36926356806267778016296625 27694767604700833512222469)
                  ·
                    refine ⟨5192768925881406283541713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27694767604700833512222469 5192768925881406283541713)
                    ·
                      refine ⟨3894576694411054712656285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192768925881406283541713 3894576694411054712656285)
                      ·
                        rfl

theorem cell23_7584661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_7584661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584661 prefixEnd_7584661 := by exact prefixLift 7584661
  have htrace : WordTrace (prefixWord ++ tailWord_7584661) baseStart_7584661 baseEnd_7584661 := by
    simpa [prefixWord, tailWord_7584661, baseEnd_7584661] using wordTrace_append hprefix tailTrace_7584661
  have hstable : (prefixWord ++ tailWord_7584661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584661).length < 2 ^ (prefixWord ++ tailWord_7584661).sum := by decide
  have hdescent : baseEnd_7584661 < baseStart_7584661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584671 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 3, 4]
def baseStart_7584671 : Nat := 118140960795 + 7584671 * 2 ^ 59
def prefixEnd_7584671 : Nat := 4983230072969 + 3 ^ 40 * 7584671 * 2
def baseEnd_7584671 : Nat := 1298193943072533224510413

theorem tailTrace_7584671 : CollatzResearch.WordTrace tailWord_7584671 prefixEnd_7584671 1298193943072533224510413 := by
  unfold tailWord_7584671
  simp only [CollatzResearch.WordTrace]
  refine ⟨276635677905039800523137867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184423785270026533682091911 276635677905039800523137867)
  ·
    refine ⟨414953516857559700784706801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276635677905039800523137867 414953516857559700784706801)
    ·
      refine ⟨311215137643169775588530101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414953516857559700784706801 311215137643169775588530101)
      ·
        refine ⟨29176419154047166461424697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311215137643169775588530101 29176419154047166461424697)
        ·
          refine ⟨21882314365535374846068523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29176419154047166461424697 21882314365535374846068523)
          ·
            refine ⟨32823471548303062269102785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21882314365535374846068523 32823471548303062269102785)
            ·
              refine ⟨24617603661227296701827089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32823471548303062269102785 24617603661227296701827089)
              ·
                refine ⟨18463202745920472526370317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24617603661227296701827089 18463202745920472526370317)
                ·
                  refine ⟨6923701029720177197388869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18463202745920472526370317 6923701029720177197388869)
                  ·
                    refine ⟨1298193943072533224510413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6923701029720177197388869 1298193943072533224510413)
                    ·
                      rfl

theorem cell23_7584671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 4].length) (baseStart_7584671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584671 prefixEnd_7584671 := by exact prefixLift 7584671
  have htrace : WordTrace (prefixWord ++ tailWord_7584671) baseStart_7584671 baseEnd_7584671 := by
    simpa [prefixWord, tailWord_7584671, baseEnd_7584671] using wordTrace_append hprefix tailTrace_7584671
  have hstable : (prefixWord ++ tailWord_7584671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584671).length < 2 ^ (prefixWord ++ tailWord_7584671).sum := by decide
  have hdescent : baseEnd_7584671 < baseStart_7584671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584677 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_7584677 : Nat := 118140960795 + 7584677 * 2 ^ 59
def prefixEnd_7584677 : Nat := 4983230072969 + 3 ^ 40 * 7584677 * 2
def baseEnd_7584677 : Nat := 3894584910101526650056211

theorem tailTrace_7584677 : CollatzResearch.WordTrace tailWord_7584677 prefixEnd_7584677 3894584910101526650056211 := by
  unfold tailWord_7584677
  simp only [CollatzResearch.WordTrace]
  refine ⟨276635896743018063547856285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184423931162012042365237523 276635896743018063547856285)
  ·
    refine ⟨103738461278631773830446107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276635896743018063547856285 103738461278631773830446107)
    ·
      refine ⟨155607691917947660745669161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103738461278631773830446107 155607691917947660745669161)
      ·
        refine ⟨116705768938460745559251871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155607691917947660745669161 116705768938460745559251871)
        ·
          refine ⟨175058653407691118338877807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116705768938460745559251871 175058653407691118338877807)
          ·
            refine ⟨262587980111536677508316711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175058653407691118338877807 262587980111536677508316711)
            ·
              refine ⟨393881970167305016262475067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262587980111536677508316711 393881970167305016262475067)
              ·
                refine ⟨590822955250957524393712601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393881970167305016262475067 590822955250957524393712601)
                ·
                  refine ⟨443117216438218143295284451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590822955250957524393712601 443117216438218143295284451)
                  ·
                    refine ⟨664675824657327214942926677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443117216438218143295284451 664675824657327214942926677)
                    ·
                      refine ⟨3894584910101526650056211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 664675824657327214942926677 3894584910101526650056211)
                      ·
                        rfl

theorem cell23_7584677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_7584677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584677 prefixEnd_7584677 := by exact prefixLift 7584677
  have htrace : WordTrace (prefixWord ++ tailWord_7584677) baseStart_7584677 baseEnd_7584677 := by
    simpa [prefixWord, tailWord_7584677, baseEnd_7584677] using wordTrace_append hprefix tailTrace_7584677
  have hstable : (prefixWord ++ tailWord_7584677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584677).length < 2 ^ (prefixWord ++ tailWord_7584677).sum := by decide
  have hdescent : baseEnd_7584677 < baseStart_7584677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584687 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_7584687 : Nat := 118140960795 + 7584687 * 2 ^ 59
def prefixEnd_7584687 : Nat := 4983230072969 + 3 ^ 40 * 7584687 * 2
def baseEnd_7584687 : Nat := 3894590044908071610931165

theorem tailTrace_7584687 : CollatzResearch.WordTrace tailWord_7584687 prefixEnd_7584687 3894590044908071610931165 := by
  unfold tailWord_7584687
  simp only [CollatzResearch.WordTrace]
  refine ⟨276636261472981835255720315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184424174315321223503813543 276636261472981835255720315)
  ·
    refine ⟨414954392209472752883580473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276636261472981835255720315 414954392209472752883580473)
    ·
      refine ⟨311215794157104564662685355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414954392209472752883580473 311215794157104564662685355)
      ·
        refine ⟨466823691235656846994028033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311215794157104564662685355 466823691235656846994028033)
        ·
          refine ⟨350117768426742635245521025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466823691235656846994028033 350117768426742635245521025)
          ·
            refine ⟨262588326320056976434140769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350117768426742635245521025 262588326320056976434140769)
            ·
              refine ⟨196941244740042732325605577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262588326320056976434140769 196941244740042732325605577)
              ·
                refine ⟨147705933555032049244204183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196941244740042732325605577 147705933555032049244204183)
                ·
                  refine ⟨221558900332548073866306275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147705933555032049244204183 221558900332548073866306275)
                  ·
                    refine ⟨332338350498822110799459413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221558900332548073866306275 332338350498822110799459413)
                    ·
                      refine ⟨3894590044908071610931165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 332338350498822110799459413 3894590044908071610931165)
                      ·
                        rfl

theorem cell23_7584687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_7584687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584687 prefixEnd_7584687 := by exact prefixLift 7584687
  have htrace : WordTrace (prefixWord ++ tailWord_7584687) baseStart_7584687 baseEnd_7584687 := by
    simpa [prefixWord, tailWord_7584687, baseEnd_7584687] using wordTrace_append hprefix tailTrace_7584687
  have hstable : (prefixWord ++ tailWord_7584687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584687).length < 2 ^ (prefixWord ++ tailWord_7584687).sum := by decide
  have hdescent : baseEnd_7584687 < baseStart_7584687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584714 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_7584714 : Nat := 118140960795 + 7584714 * 2 ^ 59
def prefixEnd_7584714 : Nat := 4983230072969 + 3 ^ 40 * 7584714 * 2
def baseEnd_7584714 : Nat := 1298201302961914335097847

theorem tailTrace_7584714 : CollatzResearch.WordTrace tailWord_7584714 prefixEnd_7584714 1298201302961914335097847 := by
  unfold tailWord_7584714
  simp only [CollatzResearch.WordTrace]
  refine ⟨69159311560971004716738299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184424830829256012577968797 69159311560971004716738299)
  ·
    refine ⟨103738967341456507075107449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69159311560971004716738299 103738967341456507075107449)
    ·
      refine ⟨77804225506092380306330587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103738967341456507075107449 77804225506092380306330587)
      ·
        refine ⟨116706338259138570459495881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77804225506092380306330587 116706338259138570459495881)
        ·
          refine ⟨87529753694353927844621911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116706338259138570459495881 87529753694353927844621911)
          ·
            refine ⟨131294630541530891766932867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87529753694353927844621911 131294630541530891766932867)
            ·
              refine ⟨196941945812296337650399301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131294630541530891766932867 196941945812296337650399301)
              ·
                refine ⟨36926614839805563309449869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196941945812296337650399301 36926614839805563309449869)
                ·
                  refine ⟨13847480564927086241043701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36926614839805563309449869 13847480564927086241043701)
                  ·
                    refine ⟨1298201302961914335097847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13847480564927086241043701 1298201302961914335097847)
                    ·
                      rfl

theorem cell23_7584714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_7584714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584714 prefixEnd_7584714 := by exact prefixLift 7584714
  have htrace : WordTrace (prefixWord ++ tailWord_7584714) baseStart_7584714 baseEnd_7584714 := by
    simpa [prefixWord, tailWord_7584714, baseEnd_7584714] using wordTrace_append hprefix tailTrace_7584714
  have hstable : (prefixWord ++ tailWord_7584714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584714).length < 2 ^ (prefixWord ++ tailWord_7584714).sum := by decide
  have hdescent : baseEnd_7584714 < baseStart_7584714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584718 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_7584718 : Nat := 118140960795 + 7584718 * 2 ^ 59
def prefixEnd_7584718 : Nat := 4983230072969 + 3 ^ 40 * 7584718 * 2
def baseEnd_7584718 : Nat := 432733995867595665515947

theorem tailTrace_7584718 : CollatzResearch.WordTrace tailWord_7584718 prefixEnd_7584718 432733995867595665515947 := by
  unfold tailWord_7584718
  simp only [CollatzResearch.WordTrace]
  refine ⟨34579674016983690943762351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184424928090579685033399205 34579674016983690943762351)
  ·
    refine ⟨51869511025475536415643527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34579674016983690943762351 51869511025475536415643527)
    ·
      refine ⟨77804266538213304623465291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51869511025475536415643527 77804266538213304623465291)
      ·
        refine ⟨116706399807319956935197937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77804266538213304623465291 116706399807319956935197937)
        ·
          refine ⟨87529799855489967701398453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116706399807319956935197937 87529799855489967701398453)
          ·
            refine ⟨8205918736452184472006105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87529799855489967701398453 8205918736452184472006105)
            ·
              refine ⟨6154439052339138354004579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8205918736452184472006105 6154439052339138354004579)
              ·
                refine ⟨9231658578508707531006869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6154439052339138354004579 9231658578508707531006869)
                ·
                  refine ⟨432733995867595665515947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9231658578508707531006869 432733995867595665515947)
                  ·
                    rfl

theorem cell23_7584718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_7584718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584718 prefixEnd_7584718 := by exact prefixLift 7584718
  have htrace : WordTrace (prefixWord ++ tailWord_7584718) baseStart_7584718 baseEnd_7584718 := by
    simpa [prefixWord, tailWord_7584718, baseEnd_7584718] using wordTrace_append hprefix tailTrace_7584718
  have hstable : (prefixWord ++ tailWord_7584718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584718).length < 2 ^ (prefixWord ++ tailWord_7584718).sum := by decide
  have hdescent : baseEnd_7584718 < baseStart_7584718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584721 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 4, 3, 2]
def baseStart_7584721 : Nat := 118140960795 + 7584721 * 2 ^ 59
def prefixEnd_7584721 : Nat := 4983230072969 + 3 ^ 40 * 7584721 * 2
def baseEnd_7584721 : Nat := 3894607503250324477906009

theorem tailTrace_7584721 : CollatzResearch.WordTrace tailWord_7584721 prefixEnd_7584721 3894607503250324477906009 := by
  unfold tailWord_7584721
  simp only [CollatzResearch.WordTrace]
  refine ⟨276637501554858659062458017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184425001036572439374972011 276637501554858659062458017)
  ·
    refine ⟨207478126166143994296843513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276637501554858659062458017 207478126166143994296843513)
    ·
      refine ⟨155608594624607995722632635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207478126166143994296843513 155608594624607995722632635)
      ·
        refine ⟨233412891936911993583948953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155608594624607995722632635 233412891936911993583948953)
        ·
          refine ⟨175059668952683995187961715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233412891936911993583948953 175059668952683995187961715)
          ·
            refine ⟨262589503429025992781942573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175059668952683995187961715 262589503429025992781942573)
            ·
              refine ⟨98471063785884747293228465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262589503429025992781942573 98471063785884747293228465)
              ·
                refine ⟨73853297839413560469921349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98471063785884747293228465 73853297839413560469921349)
                ·
                  refine ⟨13847493344890042588110253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73853297839413560469921349 13847493344890042588110253)
                  ·
                    refine ⟨5192810004333765970541345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13847493344890042588110253 5192810004333765970541345)
                    ·
                      refine ⟨3894607503250324477906009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192810004333765970541345 3894607503250324477906009)
                      ·
                        rfl

theorem cell23_7584721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_7584721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584721 prefixEnd_7584721 := by exact prefixLift 7584721
  have htrace : WordTrace (prefixWord ++ tailWord_7584721) baseStart_7584721 baseEnd_7584721 := by
    simpa [prefixWord, tailWord_7584721, baseEnd_7584721] using wordTrace_append hprefix tailTrace_7584721
  have hstable : (prefixWord ++ tailWord_7584721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584721).length < 2 ^ (prefixWord ++ tailWord_7584721).sum := by decide
  have hdescent : baseEnd_7584721 < baseStart_7584721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584744 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 3, 6]
def baseStart_7584744 : Nat := 118140960795 + 7584744 * 2 ^ 59
def prefixEnd_7584744 : Nat := 4983230072969 + 3 ^ 40 * 7584744 * 2
def baseEnd_7584744 : Nat := 1298206437768459295972801

theorem tailTrace_7584744 : CollatzResearch.WordTrace tailWord_7584744 prefixEnd_7584744 1298206437768459295972801 := by
  unfold tailWord_7584744
  simp only [CollatzResearch.WordTrace]
  refine ⟨138319170216887666995272643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184425560289183555993696857 138319170216887666995272643)
  ·
    refine ⟨207478755325331500492908965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138319170216887666995272643 207478755325331500492908965)
    ·
      refine ⟨38902266623499656342420431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207478755325331500492908965 38902266623499656342420431)
      ·
        refine ⟨58353399935249484513630647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38902266623499656342420431 58353399935249484513630647)
        ·
          refine ⟨87530099902874226770445971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58353399935249484513630647 87530099902874226770445971)
          ·
            refine ⟨131295149854311340155668957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87530099902874226770445971 131295149854311340155668957)
            ·
              refine ⟨49235681195366752558375859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131295149854311340155668957 49235681195366752558375859)
              ·
                refine ⟨73853521793050128837563789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49235681195366752558375859 73853521793050128837563789)
                ·
                  refine ⟨27695070672393798314086421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73853521793050128837563789 27695070672393798314086421)
                  ·
                    refine ⟨1298206437768459295972801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27695070672393798314086421 1298206437768459295972801)
                    ·
                      rfl

theorem cell23_7584744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_7584744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584744 prefixEnd_7584744 := by exact prefixLift 7584744
  have htrace : WordTrace (prefixWord ++ tailWord_7584744) baseStart_7584744 baseEnd_7584744 := by
    simpa [prefixWord, tailWord_7584744, baseEnd_7584744] using wordTrace_append hprefix tailTrace_7584744
  have hstable : (prefixWord ++ tailWord_7584744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584744).length < 2 ^ (prefixWord ++ tailWord_7584744).sum := by decide
  have hdescent : baseEnd_7584744 < baseStart_7584744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584756 : List Nat := [2, 6, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7584756 : Nat := 118140960795 + 7584756 * 2 ^ 59
def prefixEnd_7584756 : Nat := 4983230072969 + 3 ^ 40 * 7584756 * 2
def baseEnd_7584756 : Nat := 1298208491691077280322783

theorem tailTrace_7584756 : CollatzResearch.WordTrace tailWord_7584756 prefixEnd_7584756 1298208491691077280322783 := by
  unfold tailWord_7584756
  simp only [CollatzResearch.WordTrace]
  refine ⟨138319389054865930019991061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184425852073154573359988081 138319389054865930019991061)
  ·
    refine ⟨6483721361946840469687081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138319389054865930019991061 6483721361946840469687081)
    ·
      refine ⟨4862791021460130352265311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6483721361946840469687081 4862791021460130352265311)
      ·
        refine ⟨7294186532190195528397967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862791021460130352265311 7294186532190195528397967)
        ·
          refine ⟨10941279798285293292596951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7294186532190195528397967 10941279798285293292596951)
          ·
            refine ⟨16411919697427939938895427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10941279798285293292596951 16411919697427939938895427)
            ·
              refine ⟨24617879546141909908343141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16411919697427939938895427 24617879546141909908343141)
              ·
                refine ⟨4615852414901608107814339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24617879546141909908343141 4615852414901608107814339)
                ·
                  refine ⟨6923778622352412161721509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4615852414901608107814339 6923778622352412161721509)
                  ·
                    refine ⟨1298208491691077280322783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6923778622352412161721509 1298208491691077280322783)
                    ·
                      rfl

theorem cell23_7584756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7584756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584756 prefixEnd_7584756 := by exact prefixLift 7584756
  have htrace : WordTrace (prefixWord ++ tailWord_7584756) baseStart_7584756 baseEnd_7584756 := by
    simpa [prefixWord, tailWord_7584756, baseEnd_7584756] using wordTrace_append hprefix tailTrace_7584756
  have hstable : (prefixWord ++ tailWord_7584756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584756).length < 2 ^ (prefixWord ++ tailWord_7584756).sum := by decide
  have hdescent : baseEnd_7584756 < baseStart_7584756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584778 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_7584778 : Nat := 118140960795 + 7584778 * 2 ^ 59
def prefixEnd_7584778 : Nat := 4983230072969 + 3 ^ 40 * 7584778 * 2
def baseEnd_7584778 : Nat := 1298212257215876918297749

theorem tailTrace_7584778 : CollatzResearch.WordTrace tailWord_7584778 prefixEnd_7584778 1298212257215876918297749 := by
  unfold tailWord_7584778
  simp only [CollatzResearch.WordTrace]
  refine ⟨69159895128913039449320747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184426387010434771864855325 69159895128913039449320747)
  ·
    refine ⟨103739842693369559173981121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69159895128913039449320747 103739842693369559173981121)
    ·
      refine ⟨77804882020027169380485841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103739842693369559173981121 77804882020027169380485841)
      ·
        refine ⟨58353661515020377035364381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77804882020027169380485841 58353661515020377035364381)
        ·
          refine ⟨21882623068132641388261643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58353661515020377035364381 21882623068132641388261643)
          ·
            refine ⟨32823934602198962082392465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21882623068132641388261643 32823934602198962082392465)
            ·
              refine ⟨24617950951649221561794349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32823934602198962082392465 24617950951649221561794349)
              ·
                refine ⟨9231731606868458085672881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24617950951649221561794349 9231731606868458085672881)
                ·
                  refine ⟨6923798705151343564254661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9231731606868458085672881 6923798705151343564254661)
                  ·
                    refine ⟨1298212257215876918297749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6923798705151343564254661 1298212257215876918297749)
                    ·
                      rfl

theorem cell23_7584778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_7584778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584778 prefixEnd_7584778 := by exact prefixLift 7584778
  have htrace : WordTrace (prefixWord ++ tailWord_7584778) baseStart_7584778 baseEnd_7584778 := by
    simpa [prefixWord, tailWord_7584778, baseEnd_7584778] using wordTrace_append hprefix tailTrace_7584778
  have hstable : (prefixWord ++ tailWord_7584778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584778).length < 2 ^ (prefixWord ++ tailWord_7584778).sum := by decide
  have hdescent : baseEnd_7584778 < baseStart_7584778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584802 : List Nat := [3, 3, 1, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_7584802 : Nat := 118140960795 + 7584802 * 2 ^ 59
def prefixEnd_7584802 : Nat := 4983230072969 + 3 ^ 40 * 7584802 * 2
def baseEnd_7584802 : Nat := 3894649095183338660993137

theorem tailTrace_7584802 : CollatzResearch.WordTrace tailWord_7584802 prefixEnd_7584802 3894649095183338660993137 := by
  unfold tailWord_7584802
  simp only [CollatzResearch.WordTrace]
  refine ⟨69160113966891302474039165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184426970578376806597437773 69160113966891302474039165)
  ·
    refine ⟨25935042737584238427764687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69160113966891302474039165 25935042737584238427764687)
    ·
      refine ⟨38902564106376357641647031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25935042737584238427764687 38902564106376357641647031)
      ·
        refine ⟨58353846159564536462470547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38902564106376357641647031 58353846159564536462470547)
        ·
          refine ⟨87530769239346804693705821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58353846159564536462470547 87530769239346804693705821)
          ·
            refine ⟨32824038464755051760139683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87530769239346804693705821 32824038464755051760139683)
            ·
              refine ⟨49236057697132577640209525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32824038464755051760139683 49236057697132577640209525)
              ·
                refine ⟨4615880409106179153769643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49236057697132577640209525 4615880409106179153769643)
                ·
                  refine ⟨6923820613659268730654465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4615880409106179153769643 6923820613659268730654465)
                  ·
                    refine ⟨5192865460244451547990849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6923820613659268730654465 5192865460244451547990849)
                    ·
                      refine ⟨3894649095183338660993137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192865460244451547990849 3894649095183338660993137)
                      ·
                        rfl

theorem cell23_7584802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_7584802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584802 prefixEnd_7584802 := by exact prefixLift 7584802
  have htrace : WordTrace (prefixWord ++ tailWord_7584802) baseStart_7584802 baseEnd_7584802 := by
    simpa [prefixWord, tailWord_7584802, baseEnd_7584802] using wordTrace_append hprefix tailTrace_7584802
  have hstable : (prefixWord ++ tailWord_7584802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584802).length < 2 ^ (prefixWord ++ tailWord_7584802).sum := by decide
  have hdescent : baseEnd_7584802 < baseStart_7584802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584818 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_7584818 : Nat := 118140960795 + 7584818 * 2 ^ 59
def prefixEnd_7584818 : Nat := 4983230072969 + 3 ^ 40 * 7584818 * 2
def baseEnd_7584818 : Nat := 3894657310873810598393063

theorem tailTrace_7584818 : CollatzResearch.WordTrace tailWord_7584818 prefixEnd_7584818 3894657310873810598393063 := by
  unfold tailWord_7584818
  simp only [CollatzResearch.WordTrace]
  refine ⟨69160259858876811157184777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184427359623671496419159405 69160259858876811157184777)
  ·
    refine ⟨51870194894157608367888583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69160259858876811157184777 51870194894157608367888583)
    ·
      refine ⟨77805292341236412551832875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51870194894157608367888583 77805292341236412551832875)
      ·
        refine ⟨116707938511854618827749313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77805292341236412551832875 116707938511854618827749313)
        ·
          refine ⟨87530953883890964120811985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116707938511854618827749313 87530953883890964120811985)
          ·
            refine ⟨65648215412918223090608989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87530953883890964120811985 65648215412918223090608989)
            ·
              refine ⟨24618080779844333658978371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65648215412918223090608989 24618080779844333658978371)
              ·
                refine ⟨36927121169766500488467557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24618080779844333658978371 36927121169766500488467557)
                ·
                  refine ⟨6923835219331218841587667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36927121169766500488467557 6923835219331218841587667)
                  ·
                    refine ⟨10385752828996828262381501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6923835219331218841587667 10385752828996828262381501)
                    ·
                      refine ⟨3894657310873810598393063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10385752828996828262381501 3894657310873810598393063)
                      ·
                        rfl

theorem cell23_7584818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_7584818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584818 prefixEnd_7584818 := by exact prefixLift 7584818
  have htrace : WordTrace (prefixWord ++ tailWord_7584818) baseStart_7584818 baseEnd_7584818 := by
    simpa [prefixWord, tailWord_7584818, baseEnd_7584818] using wordTrace_append hprefix tailTrace_7584818
  have hstable : (prefixWord ++ tailWord_7584818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584818).length < 2 ^ (prefixWord ++ tailWord_7584818).sum := by decide
  have hdescent : baseEnd_7584818 < baseStart_7584818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584835 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 2, 1, 3]
def baseStart_7584835 : Nat := 118140960795 + 7584835 * 2 ^ 59
def prefixEnd_7584835 : Nat := 4983230072969 + 3 ^ 40 * 7584835 * 2
def baseEnd_7584835 : Nat := 3894666040044937031880485

theorem tailTrace_7584835 : CollatzResearch.WordTrace tailWord_7584835 prefixEnd_7584835 3894666040044937031880485 := by
  unfold tailWord_7584835
  simp only [CollatzResearch.WordTrace]
  refine ⟨276641659476445656532107959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184427772984297104354738639 276641659476445656532107959)
  ·
    refine ⟨414962489214668484798161939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276641659476445656532107959 414962489214668484798161939)
    ·
      refine ⟨622443733822002727197242909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414962489214668484798161939 622443733822002727197242909)
      ·
        refine ⟨233416400183251022698966091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622443733822002727197242909 233416400183251022698966091)
        ·
          refine ⟨350124600274876534048449137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233416400183251022698966091 350124600274876534048449137)
          ·
            refine ⟨262593450206157400536336853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350124600274876534048449137 262593450206157400536336853)
            ·
              refine ⟨6154533989206814075070395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 262593450206157400536336853 6154533989206814075070395)
              ·
                refine ⟨9231800983810221112605593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6154533989206814075070395 9231800983810221112605593)
                ·
                  refine ⟨6923850737857665834454195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9231800983810221112605593 6923850737857665834454195)
                  ·
                    refine ⟨10385776106786498751681293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6923850737857665834454195 10385776106786498751681293)
                    ·
                      refine ⟨3894666040044937031880485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10385776106786498751681293 3894666040044937031880485)
                      ·
                        rfl

theorem cell23_7584835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_7584835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584835 prefixEnd_7584835 := by exact prefixLift 7584835
  have htrace : WordTrace (prefixWord ++ tailWord_7584835) baseStart_7584835 baseEnd_7584835 := by
    simpa [prefixWord, tailWord_7584835, baseEnd_7584835] using wordTrace_append hprefix tailTrace_7584835
  have hstable : (prefixWord ++ tailWord_7584835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584835).length < 2 ^ (prefixWord ++ tailWord_7584835).sum := by decide
  have hdescent : baseEnd_7584835 < baseStart_7584835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584891 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 3]
def baseStart_7584891 : Nat := 118140960795 + 7584891 * 2 ^ 59
def prefixEnd_7584891 : Nat := 4983230072969 + 3 ^ 40 * 7584891 * 2
def baseEnd_7584891 : Nat := 3894694794961588812780227

theorem tailTrace_7584891 : CollatzResearch.WordTrace tailWord_7584891 prefixEnd_7584891 3894694794961588812780227 := by
  unfold tailWord_7584891
  simp only [CollatzResearch.WordTrace]
  refine ⟨276643701964242778096146527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184429134642828518730764351 276643701964242778096146527)
  ·
    refine ⟨414965552946364167144219791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276643701964242778096146527 414965552946364167144219791)
    ·
      refine ⟨622448329419546250716329687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414965552946364167144219791 622448329419546250716329687)
      ·
        refine ⟨933672494129319376074494531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622448329419546250716329687 933672494129319376074494531)
        ·
          refine ⟨1400508741193979064111741797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933672494129319376074494531 1400508741193979064111741797)
          ·
            refine ⟨262595388973871074520951587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1400508741193979064111741797 262595388973871074520951587)
            ·
              refine ⟨393893083460806611781427381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262595388973871074520951587 393893083460806611781427381)
              ·
                refine ⟨36927476574450619854508817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 393893083460806611781427381 36927476574450619854508817)
                ·
                  refine ⟨27695607430837964890881613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36927476574450619854508817 27695607430837964890881613)
                  ·
                    refine ⟨10385852786564236834080605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27695607430837964890881613 10385852786564236834080605)
                    ·
                      refine ⟨3894694794961588812780227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10385852786564236834080605 3894694794961588812780227)
                      ·
                        rfl

theorem cell23_7584891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 3].length) (baseStart_7584891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584891 prefixEnd_7584891 := by exact prefixLift 7584891
  have htrace : WordTrace (prefixWord ++ tailWord_7584891) baseStart_7584891 baseEnd_7584891 := by
    simpa [prefixWord, tailWord_7584891, baseEnd_7584891] using wordTrace_append hprefix tailTrace_7584891
  have hstable : (prefixWord ++ tailWord_7584891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584891).length < 2 ^ (prefixWord ++ tailWord_7584891).sum := by decide
  have hdescent : baseEnd_7584891 < baseStart_7584891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584932 : List Nat := [2, 3, 1, 2, 3, 3, 2, 2, 5]
def baseStart_7584932 : Nat := 118140960795 + 7584932 * 2 ^ 59
def prefixEnd_7584932 : Nat := 4983230072969 + 3 ^ 40 * 7584932 * 2
def baseEnd_7584932 : Nat := 432746205296491461374171

theorem tailTrace_7584932 : CollatzResearch.WordTrace tailWord_7584932 prefixEnd_7584932 432746205296491461374171 := by
  unfold tailWord_7584932
  simp only [CollatzResearch.WordTrace]
  refine ⟨138322598678547121049194525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184430131571396161398926033 138322598678547121049194525)
  ·
    refine ⟨51870974504455170393447947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138322598678547121049194525 51870974504455170393447947)
    ·
      refine ⟨77806461756682755590171921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51870974504455170393447947 77806461756682755590171921)
      ·
        refine ⟨58354846317512066692628941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77806461756682755590171921 58354846317512066692628941)
        ·
          refine ⟨21883067369067025009735853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58354846317512066692628941 21883067369067025009735853)
          ·
            refine ⟨8206150263400134378650945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21883067369067025009735853 8206150263400134378650945)
            ·
              refine ⟨6154612697550100783988209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8206150263400134378650945 6154612697550100783988209)
              ·
                refine ⟨4615959523162575587991157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6154612697550100783988209 4615959523162575587991157)
                ·
                  refine ⟨432746205296491461374171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4615959523162575587991157 432746205296491461374171)
                  ·
                    rfl

theorem cell23_7584932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_7584932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584932 prefixEnd_7584932 := by exact prefixLift 7584932
  have htrace : WordTrace (prefixWord ++ tailWord_7584932) baseStart_7584932 baseEnd_7584932 := by
    simpa [prefixWord, tailWord_7584932, baseEnd_7584932] using wordTrace_append hprefix tailTrace_7584932
  have hstable : (prefixWord ++ tailWord_7584932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584932).length < 2 ^ (prefixWord ++ tailWord_7584932).sum := by decide
  have hdescent : baseEnd_7584932 < baseStart_7584932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584935 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_7584935 : Nat := 118140960795 + 7584935 * 2 ^ 59
def prefixEnd_7584935 : Nat := 4983230072969 + 3 ^ 40 * 7584935 * 2
def baseEnd_7584935 : Nat := 3894717388110386640630025

theorem tailTrace_7584935 : CollatzResearch.WordTrace tailWord_7584935 prefixEnd_7584935 3894717388110386640630025 := by
  unfold tailWord_7584935
  simp only [CollatzResearch.WordTrace]
  refine ⟨276645306776083373610748259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184430204517388915740498839 276645306776083373610748259)
  ·
    refine ⟨414967960164125060416122389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276645306776083373610748259 414967960164125060416122389)
    ·
      refine ⟨19451623132693362207005737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 414967960164125060416122389 19451623132693362207005737)
      ·
        refine ⟨14588717349520021655254303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19451623132693362207005737 14588717349520021655254303)
        ·
          refine ⟨21883076024280032482881455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14588717349520021655254303 21883076024280032482881455)
          ·
            refine ⟨32824614036420048724322183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21883076024280032482881455 32824614036420048724322183)
            ·
              refine ⟨49236921054630073086483275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32824614036420048724322183 49236921054630073086483275)
              ·
                refine ⟨73855381581945109629724913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49236921054630073086483275 73855381581945109629724913)
                ·
                  refine ⟨55391536186458832222293685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73855381581945109629724913 55391536186458832222293685)
                  ·
                    refine ⟨5192956517480515520840033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55391536186458832222293685 5192956517480515520840033)
                    ·
                      refine ⟨3894717388110386640630025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5192956517480515520840033 3894717388110386640630025)
                      ·
                        rfl

theorem cell23_7584935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_7584935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584935 prefixEnd_7584935 := by exact prefixLift 7584935
  have htrace : WordTrace (prefixWord ++ tailWord_7584935) baseStart_7584935 baseEnd_7584935 := by
    simpa [prefixWord, tailWord_7584935, baseEnd_7584935] using wordTrace_append hprefix tailTrace_7584935
  have hstable : (prefixWord ++ tailWord_7584935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584935).length < 2 ^ (prefixWord ++ tailWord_7584935).sum := by decide
  have hdescent : baseEnd_7584935 < baseStart_7584935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584962 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_7584962 : Nat := 118140960795 + 7584962 * 2 ^ 59
def prefixEnd_7584962 : Nat := 4983230072969 + 3 ^ 40 * 7584962 * 2
def baseEnd_7584962 : Nat := 1298243750696019344997467

theorem tailTrace_7584962 : CollatzResearch.WordTrace tailWord_7584962 prefixEnd_7584962 1298243750696019344997467 := by
  unfold tailWord_7584962
  simp only [CollatzResearch.WordTrace]
  refine ⟨69161572886746389305495285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184430861031323704814654093 69161572886746389305495285)
  ·
    refine ⟨6483897458132473997390183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69161572886746389305495285 6483897458132473997390183)
    ·
      refine ⟨9725846187198710996085275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6483897458132473997390183 9725846187198710996085275)
      ·
        refine ⟨14588769280798066494127913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9725846187198710996085275 14588769280798066494127913)
        ·
          refine ⟨10941576960598549870595935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14588769280798066494127913 10941576960598549870595935)
          ·
            refine ⟨16412365440897824805893903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10941576960598549870595935 16412365440897824805893903)
            ·
              refine ⟨24618548161346737208840855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16412365440897824805893903 24618548161346737208840855)
              ·
                refine ⟨36927822242020105813261283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24618548161346737208840855 36927822242020105813261283)
                ·
                  refine ⟨55391733363030158719891925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36927822242020105813261283 55391733363030158719891925)
                  ·
                    refine ⟨1298243750696019344997467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55391733363030158719891925 1298243750696019344997467)
                    ·
                      rfl

theorem cell23_7584962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_7584962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584962 prefixEnd_7584962 := by exact prefixLift 7584962
  have htrace : WordTrace (prefixWord ++ tailWord_7584962) baseStart_7584962 baseEnd_7584962 := by
    simpa [prefixWord, tailWord_7584962, baseEnd_7584962] using wordTrace_append hprefix tailTrace_7584962
  have hstable : (prefixWord ++ tailWord_7584962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584962).length < 2 ^ (prefixWord ++ tailWord_7584962).sum := by decide
  have hdescent : baseEnd_7584962 < baseStart_7584962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584966 : List Nat := [6, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_7584966 : Nat := 118140960795 + 7584966 * 2 ^ 59
def prefixEnd_7584966 : Nat := 4983230072969 + 3 ^ 40 * 7584966 * 2
def baseEnd_7584966 : Nat := 432748145112297335482487

theorem tailTrace_7584966 : CollatzResearch.WordTrace tailWord_7584966 prefixEnd_7584966 432748145112297335482487 := by
  unfold tailWord_7584966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8645201169967845809535211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184430958292647377270084501 8645201169967845809535211)
  ·
    refine ⟨12967801754951768714302817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8645201169967845809535211 12967801754951768714302817)
    ·
      refine ⟨9725851316213826535727113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12967801754951768714302817 9725851316213826535727113)
      ·
        refine ⟨7294388487160369901795335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9725851316213826535727113 7294388487160369901795335)
        ·
          refine ⟨10941582730740554852693003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7294388487160369901795335 10941582730740554852693003)
          ·
            refine ⟨16412374096110832279039505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10941582730740554852693003 16412374096110832279039505)
            ·
              refine ⟨12309280572083124209279629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16412374096110832279039505 12309280572083124209279629)
              ·
                refine ⟨4615980214531171578479861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12309280572083124209279629 4615980214531171578479861)
                ·
                  refine ⟨432748145112297335482487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4615980214531171578479861 432748145112297335482487)
                  ·
                    rfl

theorem cell23_7584966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_7584966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584966 prefixEnd_7584966 := by exact prefixLift 7584966
  have htrace : WordTrace (prefixWord ++ tailWord_7584966) baseStart_7584966 baseEnd_7584966 := by
    simpa [prefixWord, tailWord_7584966, baseEnd_7584966] using wordTrace_append hprefix tailTrace_7584966
  have hstable : (prefixWord ++ tailWord_7584966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584966).length < 2 ^ (prefixWord ++ tailWord_7584966).sum := by decide
  have hdescent : baseEnd_7584966 < baseStart_7584966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7584991 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_7584991 : Nat := 118140960795 + 7584991 * 2 ^ 59
def prefixEnd_7584991 : Nat := 4983230072969 + 3 ^ 40 * 7584991 * 2
def baseEnd_7584991 : Nat := 3894746143027038421529767

theorem tailTrace_7584991 : CollatzResearch.WordTrace tailWord_7584991 prefixEnd_7584991 3894746143027038421529767 := by
  unfold tailWord_7584991
  simp only [CollatzResearch.WordTrace]
  refine ⟨276647349263880495174786827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184431566175920330116524551 276647349263880495174786827)
  ·
    refine ⟨414971023895820742762180241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276647349263880495174786827 414971023895820742762180241)
    ·
      refine ⟨311228267921865557071635181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414971023895820742762180241 311228267921865557071635181)
      ·
        refine ⟨116710600470699583901863193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311228267921865557071635181 116710600470699583901863193)
        ·
          refine ⟨87532950353024687926397395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116710600470699583901863193 87532950353024687926397395)
          ·
            refine ⟨131299425529537031889596093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87532950353024687926397395 131299425529537031889596093)
            ·
              refine ⟨49237284573576386958598535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131299425529537031889596093 49237284573576386958598535)
              ·
                refine ⟨73855926860364580437897803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49237284573576386958598535 73855926860364580437897803)
                ·
                  refine ⟨110783890290546870656846705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73855926860364580437897803 110783890290546870656846705)
                  ·
                    refine ⟨83087917717910152992635029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110783890290546870656846705 83087917717910152992635029)
                    ·
                      refine ⟨3894746143027038421529767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83087917717910152992635029 3894746143027038421529767)
                      ·
                        rfl

theorem cell23_7584991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_7584991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7584991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7584991 prefixEnd_7584991 := by exact prefixLift 7584991
  have htrace : WordTrace (prefixWord ++ tailWord_7584991) baseStart_7584991 baseEnd_7584991 := by
    simpa [prefixWord, tailWord_7584991, baseEnd_7584991] using wordTrace_append hprefix tailTrace_7584991
  have hstable : (prefixWord ++ tailWord_7584991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7584991).length < 2 ^ (prefixWord ++ tailWord_7584991).sum := by decide
  have hdescent : baseEnd_7584991 < baseStart_7584991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7584991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585025 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_7585025 : Nat := 118140960795 + 7585025 * 2 ^ 59
def prefixEnd_7585025 : Nat := 4983230072969 + 3 ^ 40 * 7585025 * 2
def baseEnd_7585025 : Nat := 3894763601369291288504611

theorem tailTrace_7585025 : CollatzResearch.WordTrace tailWord_7585025 prefixEnd_7585025 3894763601369291288504611 := by
  unfold tailWord_7585025
  simp only [CollatzResearch.WordTrace]
  refine ⟨276648589345757318981524529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184432392897171545987683019 276648589345757318981524529)
  ·
    refine ⟨207486442009317989236143397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276648589345757318981524529 207486442009317989236143397)
    ·
      refine ⟨38903707876747122981776887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207486442009317989236143397 38903707876747122981776887)
      ·
        refine ⟨58355561815120684472665331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38903707876747122981776887 58355561815120684472665331)
        ·
          refine ⟨87533342722681026708997997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58355561815120684472665331 87533342722681026708997997)
          ·
            refine ⟨32825003521005385015874249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87533342722681026708997997 32825003521005385015874249)
            ·
              refine ⟨24618752640754038761905687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32825003521005385015874249 24618752640754038761905687)
              ·
                refine ⟨36928128961131058142858531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24618752640754038761905687 36928128961131058142858531)
                ·
                  refine ⟨55392193441696587214287797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36928128961131058142858531 55392193441696587214287797)
                  ·
                    refine ⟨5193018135159055051339481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55392193441696587214287797 5193018135159055051339481)
                    ·
                      refine ⟨3894763601369291288504611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193018135159055051339481 3894763601369291288504611)
                      ·
                        rfl

theorem cell23_7585025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_7585025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585025 prefixEnd_7585025 := by exact prefixLift 7585025
  have htrace : WordTrace (prefixWord ++ tailWord_7585025) baseStart_7585025 baseEnd_7585025 := by
    simpa [prefixWord, tailWord_7585025, baseEnd_7585025] using wordTrace_append hprefix tailTrace_7585025
  have hstable : (prefixWord ++ tailWord_7585025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585025).length < 2 ^ (prefixWord ++ tailWord_7585025).sum := by decide
  have hdescent : baseEnd_7585025 < baseStart_7585025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585026 : List Nat := [3, 4, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_7585026 : Nat := 118140960795 + 7585026 * 2 ^ 59
def prefixEnd_7585026 : Nat := 4983230072969 + 3 ^ 40 * 7585026 * 2
def baseEnd_7585026 : Nat := 1298254704949981928197369

theorem tailTrace_7585026 : CollatzResearch.WordTrace tailWord_7585026 prefixEnd_7585026 1298254704949981928197369 := by
  unfold tailWord_7585026
  simp only [CollatzResearch.WordTrace]
  refine ⟨69162156454688424038077733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184432417212502464101540621 69162156454688424038077733)
  ·
    refine ⟨12967904335254079507139575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69162156454688424038077733 12967904335254079507139575)
    ·
      refine ⟨19451856502881119260709363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12967904335254079507139575 19451856502881119260709363)
      ·
        refine ⟨29177784754321678891064045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19451856502881119260709363 29177784754321678891064045)
        ·
          refine ⟨10941669282870629584149017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29177784754321678891064045 10941669282870629584149017)
          ·
            refine ⟨8206251962152972188111763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10941669282870629584149017 8206251962152972188111763)
            ·
              refine ⟨12309377943229458282167645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206251962152972188111763 12309377943229458282167645)
              ·
                refine ⟨4616016728711046855812867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12309377943229458282167645 4616016728711046855812867)
                ·
                  refine ⟨6924025093066570283719301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4616016728711046855812867 6924025093066570283719301)
                  ·
                    refine ⟨1298254704949981928197369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6924025093066570283719301 1298254704949981928197369)
                    ·
                      rfl

theorem cell23_7585026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_7585026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585026 prefixEnd_7585026 := by exact prefixLift 7585026
  have htrace : WordTrace (prefixWord ++ tailWord_7585026) baseStart_7585026 baseEnd_7585026 := by
    simpa [prefixWord, tailWord_7585026, baseEnd_7585026] using wordTrace_append hprefix tailTrace_7585026
  have hstable : (prefixWord ++ tailWord_7585026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585026).length < 2 ^ (prefixWord ++ tailWord_7585026).sum := by decide
  have hdescent : baseEnd_7585026 < baseStart_7585026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585068 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_7585068 : Nat := 118140960795 + 7585068 * 2 ^ 59
def prefixEnd_7585068 : Nat := 4983230072969 + 3 ^ 40 * 7585068 * 2
def baseEnd_7585068 : Nat := 3894785681037434620266913

theorem tailTrace_7585068 : CollatzResearch.WordTrace tailWord_7585068 prefixEnd_7585068 3894785681037434620266913 := by
  unfold tailWord_7585068
  simp only [CollatzResearch.WordTrace]
  refine ⟨138325078842300768662669929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184433438456401024883559905 138325078842300768662669929)
  ·
    refine ⟨103743809131725576497002447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138325078842300768662669929 103743809131725576497002447)
    ·
      refine ⟨155615713697588364745503671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103743809131725576497002447 155615713697588364745503671)
      ·
        refine ⟨233423570546382547118255507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155615713697588364745503671 233423570546382547118255507)
        ·
          refine ⟨350135355819573820677383261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233423570546382547118255507 350135355819573820677383261)
          ·
            refine ⟨131300758432340182754018723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350135355819573820677383261 131300758432340182754018723)
            ·
              refine ⟨196951137648510274131028085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131300758432340182754018723 196951137648510274131028085)
              ·
                refine ⟨18464169154547838199783883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196951137648510274131028085 18464169154547838199783883)
                ·
                  refine ⟨27696253731821757299675825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18464169154547838199783883 27696253731821757299675825)
                  ·
                    refine ⟨20772190298866317974756869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27696253731821757299675825 20772190298866317974756869)
                    ·
                      refine ⟨3894785681037434620266913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20772190298866317974756869 3894785681037434620266913)
                      ·
                        rfl

theorem cell23_7585068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_7585068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585068 prefixEnd_7585068 := by exact prefixLift 7585068
  have htrace : WordTrace (prefixWord ++ tailWord_7585068) baseStart_7585068 baseEnd_7585068 := by
    simpa [prefixWord, tailWord_7585068, baseEnd_7585068] using wordTrace_append hprefix tailTrace_7585068
  have hstable : (prefixWord ++ tailWord_7585068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585068).length < 2 ^ (prefixWord ++ tailWord_7585068).sum := by decide
  have hdescent : baseEnd_7585068 < baseStart_7585068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585069 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7585069 : Nat := 118140960795 + 7585069 * 2 ^ 59
def prefixEnd_7585069 : Nat := 4983230072969 + 3 ^ 40 * 7585069 * 2
def baseEnd_7585069 : Nat := 1298262064839363038784803

theorem tailTrace_7585069 : CollatzResearch.WordTrace tailWord_7585069 prefixEnd_7585069 1298262064839363038784803 := by
  unfold tailWord_7585069
  simp only [CollatzResearch.WordTrace]
  refine ⟨276650194157597914496126261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184433462771731942997417507 276650194157597914496126261)
  ·
    refine ⟨25935955702274804484011837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276650194157597914496126261 25935955702274804484011837)
    ·
      refine ⟨9725983388353051681504439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25935955702274804484011837 9725983388353051681504439)
      ·
        refine ⟨14588975082529577522256659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9725983388353051681504439 14588975082529577522256659)
        ·
          refine ⟨21883462623794366283384989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14588975082529577522256659 21883462623794366283384989)
          ·
            refine ⟨8206298483922887356269371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21883462623794366283384989 8206298483922887356269371)
            ·
              refine ⟨12309447725884331034404057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206298483922887356269371 12309447725884331034404057)
              ·
                refine ⟨9232085794413248275803043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12309447725884331034404057 9232085794413248275803043)
                ·
                  refine ⟨13848128691619872413704565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9232085794413248275803043 13848128691619872413704565)
                  ·
                    refine ⟨1298262064839363038784803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13848128691619872413704565 1298262064839363038784803)
                    ·
                      rfl

theorem cell23_7585069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7585069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585069 prefixEnd_7585069 := by exact prefixLift 7585069
  have htrace : WordTrace (prefixWord ++ tailWord_7585069) baseStart_7585069 baseEnd_7585069 := by
    simpa [prefixWord, tailWord_7585069, baseEnd_7585069] using wordTrace_append hprefix tailTrace_7585069
  have hstable : (prefixWord ++ tailWord_7585069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585069).length < 2 ^ (prefixWord ++ tailWord_7585069).sum := by decide
  have hdescent : baseEnd_7585069 < baseStart_7585069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585075 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 3]
def baseStart_7585075 : Nat := 118140960795 + 7585075 * 2 ^ 59
def prefixEnd_7585075 : Nat := 4983230072969 + 3 ^ 40 * 7585075 * 2
def baseEnd_7585075 : Nat := 3894789275402016092879381

theorem tailTrace_7585075 : CollatzResearch.WordTrace tailWord_7585075 prefixEnd_7585075 3894789275402016092879381 := by
  unfold tailWord_7585075
  simp only [CollatzResearch.WordTrace]
  refine ⟨276650412995576177520844679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184433608663717451680563119 276650412995576177520844679)
  ·
    refine ⟨414975619493364266281267019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276650412995576177520844679 414975619493364266281267019)
    ·
      refine ⟨622463429240046399421900529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414975619493364266281267019 622463429240046399421900529)
      ·
        refine ⟨466847571930034799566425397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622463429240046399421900529 466847571930034799566425397)
        ·
          refine ⟨43766959868440762459352381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 466847571930034799566425397 43766959868440762459352381)
          ·
            refine ⟨16412609950665285922257143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43766959868440762459352381 16412609950665285922257143)
            ·
              refine ⟨24618914925997928883385715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16412609950665285922257143 24618914925997928883385715)
              ·
                refine ⟨36928372388996893325078573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24618914925997928883385715 36928372388996893325078573)
                ·
                  refine ⟨13848139645873834996904465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36928372388996893325078573 13848139645873834996904465)
                  ·
                    refine ⟨10386104734405376247678349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13848139645873834996904465 10386104734405376247678349)
                    ·
                      refine ⟨3894789275402016092879381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10386104734405376247678349 3894789275402016092879381)
                      ·
                        rfl

theorem cell23_7585075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_7585075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585075 prefixEnd_7585075 := by exact prefixLift 7585075
  have htrace : WordTrace (prefixWord ++ tailWord_7585075) baseStart_7585075 baseEnd_7585075 := by
    simpa [prefixWord, tailWord_7585075, baseEnd_7585075] using wordTrace_append hprefix tailTrace_7585075
  have hstable : (prefixWord ++ tailWord_7585075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585075).length < 2 ^ (prefixWord ++ tailWord_7585075).sum := by decide
  have hdescent : baseEnd_7585075 < baseStart_7585075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585089 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7585089 : Nat := 118140960795 + 7585089 * 2 ^ 59
def prefixEnd_7585089 : Nat := 4983230072969 + 3 ^ 40 * 7585089 * 2
def baseEnd_7585089 : Nat := 3894796464131179038104317

theorem tailTrace_7585089 : CollatzResearch.WordTrace tailWord_7585089 prefixEnd_7585089 3894796464131179038104317 := by
  unfold tailWord_7585089
  simp only [CollatzResearch.WordTrace]
  refine ⟨276650923617525457911854321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184433949078350305274569547 276650923617525457911854321)
  ·
    refine ⟨207488192713144093433890741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276650923617525457911854321 207488192713144093433890741)
    ·
      refine ⟨19452018066857258759427257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207488192713144093433890741 19452018066857258759427257)
      ·
        refine ⟨14589013550142944069570443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19452018066857258759427257 14589013550142944069570443)
        ·
          refine ⟨21883520325214416104355665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14589013550142944069570443 21883520325214416104355665)
          ·
            refine ⟨16412640243910812078266749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21883520325214416104355665 16412640243910812078266749)
            ·
              refine ⟨6154740091466554529350031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16412640243910812078266749 6154740091466554529350031)
              ·
                refine ⟨9232110137199831794025047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6154740091466554529350031 9232110137199831794025047)
                ·
                  refine ⟨13848165205799747691037571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9232110137199831794025047 13848165205799747691037571)
                  ·
                    refine ⟨20772247808699621536556357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13848165205799747691037571 20772247808699621536556357)
                    ·
                      refine ⟨3894796464131179038104317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20772247808699621536556357 3894796464131179038104317)
                      ·
                        rfl

theorem cell23_7585089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7585089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585089 prefixEnd_7585089 := by exact prefixLift 7585089
  have htrace : WordTrace (prefixWord ++ tailWord_7585089) baseStart_7585089 baseEnd_7585089 := by
    simpa [prefixWord, tailWord_7585089, baseEnd_7585089] using wordTrace_append hprefix tailTrace_7585089
  have hstable : (prefixWord ++ tailWord_7585089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585089).length < 2 ^ (prefixWord ++ tailWord_7585089).sum := by decide
  have hdescent : baseEnd_7585089 < baseStart_7585089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585092 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_7585092 : Nat := 118140960795 + 7585092 * 2 ^ 59
def prefixEnd_7585092 : Nat := 4983230072969 + 3 ^ 40 * 7585092 * 2
def baseEnd_7585092 : Nat := 3894798004573142526366803

theorem tailTrace_7585092 : CollatzResearch.WordTrace tailWord_7585092 prefixEnd_7585092 3894798004573142526366803 := by
  unfold tailWord_7585092
  simp only [CollatzResearch.WordTrace]
  refine ⟨138325516518257294712106765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184434022024343059616142353 138325516518257294712106765)
  ·
    refine ⟨51872068694346485517040037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138325516518257294712106765 51872068694346485517040037)
    ·
      refine ⟨9726012880189966034445007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51872068694346485517040037 9726012880189966034445007)
      ·
        refine ⟨14589019320284949051667511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9726012880189966034445007 14589019320284949051667511)
        ·
          refine ⟨21883528980427423577501267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14589019320284949051667511 21883528980427423577501267)
          ·
            refine ⟨32825293470641135366251901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21883528980427423577501267 32825293470641135366251901)
            ·
              refine ⟨12309485051490425762344463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32825293470641135366251901 12309485051490425762344463)
              ·
                refine ⟨18464227577235638643516695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12309485051490425762344463 18464227577235638643516695)
                ·
                  refine ⟨27696341365853457965275043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18464227577235638643516695 27696341365853457965275043)
                  ·
                    refine ⟨41544512048780186947912565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27696341365853457965275043 41544512048780186947912565)
                    ·
                      refine ⟨3894798004573142526366803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41544512048780186947912565 3894798004573142526366803)
                      ·
                        rfl

theorem cell23_7585092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_7585092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585092 prefixEnd_7585092 := by exact prefixLift 7585092
  have htrace : WordTrace (prefixWord ++ tailWord_7585092) baseStart_7585092 baseEnd_7585092 := by
    simpa [prefixWord, tailWord_7585092, baseEnd_7585092] using wordTrace_append hprefix tailTrace_7585092
  have hstable : (prefixWord ++ tailWord_7585092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585092).length < 2 ^ (prefixWord ++ tailWord_7585092).sum := by decide
  have hdescent : baseEnd_7585092 < baseStart_7585092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585108 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_7585108 : Nat := 118140960795 + 7585108 * 2 ^ 59
def prefixEnd_7585108 : Nat := 4983230072969 + 3 ^ 40 * 7585108 * 2
def baseEnd_7585108 : Nat := 1298268740087871487922243

theorem tailTrace_7585108 : CollatzResearch.WordTrace tailWord_7585108 prefixEnd_7585108 1298268740087871487922243 := by
  unfold tailWord_7585108
  simp only [CollatzResearch.WordTrace]
  refine ⟨138325808302228312078397989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184434411069637749437863985 138325808302228312078397989)
  ·
    refine ⟨25936089056667808514699623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138325808302228312078397989 25936089056667808514699623)
    ·
      refine ⟨38904133585001712772049435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25936089056667808514699623 38904133585001712772049435)
      ·
        refine ⟨58356200377502569158074153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38904133585001712772049435 58356200377502569158074153)
        ·
          refine ⟨43767150283126926868555615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58356200377502569158074153 43767150283126926868555615)
          ·
            refine ⟨65650725424690390302833423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43767150283126926868555615 65650725424690390302833423)
            ·
              refine ⟨98476088137035585454250135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65650725424690390302833423 98476088137035585454250135)
              ·
                refine ⟨147714132205553378181375203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98476088137035585454250135 147714132205553378181375203)
                ·
                  refine ⟨221571198308330067272062805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147714132205553378181375203 221571198308330067272062805)
                  ·
                    refine ⟨1298268740087871487922243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 221571198308330067272062805 1298268740087871487922243)
                    ·
                      rfl

theorem cell23_7585108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_7585108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585108 prefixEnd_7585108 := by exact prefixLift 7585108
  have htrace : WordTrace (prefixWord ++ tailWord_7585108) baseStart_7585108 baseEnd_7585108 := by
    simpa [prefixWord, tailWord_7585108, baseEnd_7585108] using wordTrace_append hprefix tailTrace_7585108
  have hstable : (prefixWord ++ tailWord_7585108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585108).length < 2 ^ (prefixWord ++ tailWord_7585108).sum := by decide
  have hdescent : baseEnd_7585108 < baseStart_7585108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585122 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_7585122 : Nat := 118140960795 + 7585122 * 2 ^ 59
def prefixEnd_7585122 : Nat := 4983230072969 + 3 ^ 40 * 7585122 * 2
def baseEnd_7585122 : Nat := 3894813408992777408991665

theorem tailTrace_7585122 : CollatzResearch.WordTrace tailWord_7585122 prefixEnd_7585122 3894813408992777408991665 := by
  unfold tailWord_7585122
  simp only [CollatzResearch.WordTrace]
  refine ⟨69163031806601476136951405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184434751484270603031870413 69163031806601476136951405)
  ·
    refine ⟨25936136927475553551356777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69163031806601476136951405 25936136927475553551356777)
    ·
      refine ⟨19452102695606665163517583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25936136927475553551356777 19452102695606665163517583)
      ·
        refine ⟨29178154043409997745276375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19452102695606665163517583 29178154043409997745276375)
        ·
          refine ⟨43767231065114996617914563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29178154043409997745276375 43767231065114996617914563)
          ·
            refine ⟨65650846597672494926871845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43767231065114996617914563 65650846597672494926871845)
            ·
              refine ⟨12309533737063592798788471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65650846597672494926871845 12309533737063592798788471)
              ·
                refine ⟨18464300605595389198182707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12309533737063592798788471 18464300605595389198182707)
                ·
                  refine ⟨27696450908393083797274061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18464300605595389198182707 27696450908393083797274061)
                  ·
                    refine ⟨10386169090647406423977773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27696450908393083797274061 10386169090647406423977773)
                    ·
                      refine ⟨3894813408992777408991665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10386169090647406423977773 3894813408992777408991665)
                      ·
                        rfl

theorem cell23_7585122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_7585122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585122 prefixEnd_7585122 := by exact prefixLift 7585122
  have htrace : WordTrace (prefixWord ++ tailWord_7585122) baseStart_7585122 baseEnd_7585122 := by
    simpa [prefixWord, tailWord_7585122, baseEnd_7585122] using wordTrace_append hprefix tailTrace_7585122
  have hstable : (prefixWord ++ tailWord_7585122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585122).length < 2 ^ (prefixWord ++ tailWord_7585122).sum := by decide
  have hdescent : baseEnd_7585122 < baseStart_7585122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585132 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 3, 3, 2]
def baseStart_7585132 : Nat := 118140960795 + 7585132 * 2 ^ 59
def prefixEnd_7585132 : Nat := 4983230072969 + 3 ^ 40 * 7585132 * 2
def baseEnd_7585132 : Nat := 3894818543799322369866619

theorem tailTrace_7585132 : CollatzResearch.WordTrace tailWord_7585132 prefixEnd_7585132 3894818543799322369866619 := by
  unfold tailWord_7585132
  simp only [CollatzResearch.WordTrace]
  refine ⟨138326245978184838127834825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184434994637579784170446433 138326245978184838127834825)
  ·
    refine ⟨103744684483638628595876119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138326245978184838127834825 103744684483638628595876119)
    ·
      refine ⟨155617026725457942893814179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103744684483638628595876119 155617026725457942893814179)
      ·
        refine ⟨233425540088186914340721269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155617026725457942893814179 233425540088186914340721269)
        ·
          refine ⟨21883644383267523219442619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233425540088186914340721269 21883644383267523219442619)
          ·
            refine ⟨32825466574901284829163929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21883644383267523219442619 32825466574901284829163929)
            ·
              refine ⟨24619099931175963621872947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32825466574901284829163929 24619099931175963621872947)
              ·
                refine ⟨36928649896763945432809421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24619099931175963621872947 36928649896763945432809421)
                ·
                  refine ⟨13848243711286479537303533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36928649896763945432809421 13848243711286479537303533)
                  ·
                    refine ⟨5193091391732429826488825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13848243711286479537303533 5193091391732429826488825)
                    ·
                      refine ⟨3894818543799322369866619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193091391732429826488825 3894818543799322369866619)
                      ·
                        rfl

theorem cell23_7585132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_7585132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585132 prefixEnd_7585132 := by exact prefixLift 7585132
  have htrace : WordTrace (prefixWord ++ tailWord_7585132) baseStart_7585132 baseEnd_7585132 := by
    simpa [prefixWord, tailWord_7585132, baseEnd_7585132] using wordTrace_append hprefix tailTrace_7585132
  have hstable : (prefixWord ++ tailWord_7585132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585132).length < 2 ^ (prefixWord ++ tailWord_7585132).sum := by decide
  have hdescent : baseEnd_7585132 < baseStart_7585132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585138 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_7585138 : Nat := 118140960795 + 7585138 * 2 ^ 59
def prefixEnd_7585138 : Nat := 4983230072969 + 3 ^ 40 * 7585138 * 2
def baseEnd_7585138 : Nat := 1298273874894416448797197

theorem tailTrace_7585138 : CollatzResearch.WordTrace tailWord_7585138 prefixEnd_7585138 1298273874894416448797197 := by
  unfold tailWord_7585138
  simp only [CollatzResearch.WordTrace]
  refine ⟨69163177698586984820097017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184435140529565292853592045 69163177698586984820097017)
  ·
    refine ⟨51872383273940238615072763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69163177698586984820097017 51872383273940238615072763)
    ·
      refine ⟨77808574910910357922609145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51872383273940238615072763 77808574910910357922609145)
      ·
        refine ⟨58356431183182768441956859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77808574910910357922609145 58356431183182768441956859)
        ·
          refine ⟨87534646774774152662935289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58356431183182768441956859 87534646774774152662935289)
          ·
            refine ⟨65650985081080614497201467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87534646774774152662935289 65650985081080614497201467)
            ·
              refine ⟨98476477621620921745802201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65650985081080614497201467 98476477621620921745802201)
              ·
                refine ⟨73857358216215691309351651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98476477621620921745802201 73857358216215691309351651)
                ·
                  refine ⟨110786037324323536964027477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73857358216215691309351651 110786037324323536964027477)
                  ·
                    refine ⟨1298273874894416448797197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110786037324323536964027477 1298273874894416448797197)
                    ·
                      rfl

theorem cell23_7585138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_7585138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585138 prefixEnd_7585138 := by exact prefixLift 7585138
  have htrace : WordTrace (prefixWord ++ tailWord_7585138) baseStart_7585138 baseEnd_7585138 := by
    simpa [prefixWord, tailWord_7585138, baseEnd_7585138] using wordTrace_append hprefix tailTrace_7585138
  have hstable : (prefixWord ++ tailWord_7585138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585138).length < 2 ^ (prefixWord ++ tailWord_7585138).sum := by decide
  have hdescent : baseEnd_7585138 < baseStart_7585138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585148 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_7585148 : Nat := 118140960795 + 7585148 * 2 ^ 59
def prefixEnd_7585148 : Nat := 4983230072969 + 3 ^ 40 * 7585148 * 2
def baseEnd_7585148 : Nat := 3894826759489794307266545

theorem tailTrace_7585148 : CollatzResearch.WordTrace tailWord_7585148 prefixEnd_7585148 3894826759489794307266545 := by
  unfold tailWord_7585148
  simp only [CollatzResearch.WordTrace]
  refine ⟨138326537762155855494126049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184435383682874473992168065 138326537762155855494126049)
  ·
    refine ⟨103744903321616891620594537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138326537762155855494126049 103744903321616891620594537)
    ·
      refine ⟨77808677491212668715445903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103744903321616891620594537 77808677491212668715445903)
      ·
        refine ⟨116713016236819003073168855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77808677491212668715445903 116713016236819003073168855)
        ·
          refine ⟨175069524355228504609753283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116713016236819003073168855 175069524355228504609753283)
          ·
            refine ⟨262604286532842756914629925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175069524355228504609753283 262604286532842756914629925)
            ·
              refine ⟨49238303724908016921493111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262604286532842756914629925 49238303724908016921493111)
              ·
                refine ⟨73857455587362025382239667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49238303724908016921493111 73857455587362025382239667)
                ·
                  refine ⟨110786183381043038073359501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73857455587362025382239667 110786183381043038073359501)
                  ·
                    refine ⟨41544818767891139277509813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110786183381043038073359501 41544818767891139277509813)
                    ·
                      refine ⟨3894826759489794307266545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41544818767891139277509813 3894826759489794307266545)
                      ·
                        rfl

theorem cell23_7585148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_7585148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585148 prefixEnd_7585148 := by exact prefixLift 7585148
  have htrace : WordTrace (prefixWord ++ tailWord_7585148) baseStart_7585148 baseEnd_7585148 := by
    simpa [prefixWord, tailWord_7585148, baseEnd_7585148] using wordTrace_append hprefix tailTrace_7585148
  have hstable : (prefixWord ++ tailWord_7585148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585148).length < 2 ^ (prefixWord ++ tailWord_7585148).sum := by decide
  have hdescent : baseEnd_7585148 < baseStart_7585148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585269 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7585269 : Nat := 118140960795 + 7585269 * 2 ^ 59
def prefixEnd_7585269 : Nat := 4983230072969 + 3 ^ 40 * 7585269 * 2
def baseEnd_7585269 : Nat := 3894888890648988333853489

theorem tailTrace_7585269 : CollatzResearch.WordTrace tailWord_7585269 prefixEnd_7585269 3894888890648988333853489 := by
  unfold tailWord_7585269
  simp only [CollatzResearch.WordTrace]
  refine ⟨276657488756873348653406861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184438325837915565768937907 276657488756873348653406861)
  ·
    refine ⟨103746558283827505745027573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276657488756873348653406861 103746558283827505745027573)
    ·
      refine ⟨9726239839108828663596335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103746558283827505745027573 9726239839108828663596335)
      ·
        refine ⟨14589359758663242995394503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9726239839108828663596335 14589359758663242995394503)
        ·
          refine ⟨21884039637994864493091755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14589359758663242995394503 21884039637994864493091755)
          ·
            refine ⟨32826059456992296739637633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21884039637994864493091755 32826059456992296739637633)
            ·
              refine ⟨24619544592744222554728225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32826059456992296739637633 24619544592744222554728225)
              ·
                refine ⟨18464658444558166916046169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24619544592744222554728225 18464658444558166916046169)
                ·
                  refine ⟨13848493833418625187034627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18464658444558166916046169 13848493833418625187034627)
                  ·
                    refine ⟨20772740750127937780551941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13848493833418625187034627 20772740750127937780551941)
                    ·
                      refine ⟨3894888890648988333853489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20772740750127937780551941 3894888890648988333853489)
                      ·
                        rfl

theorem cell23_7585269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7585269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585269 prefixEnd_7585269 := by exact prefixLift 7585269
  have htrace : WordTrace (prefixWord ++ tailWord_7585269) baseStart_7585269 baseEnd_7585269 := by
    simpa [prefixWord, tailWord_7585269, baseEnd_7585269] using wordTrace_append hprefix tailTrace_7585269
  have hstable : (prefixWord ++ tailWord_7585269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585269).length < 2 ^ (prefixWord ++ tailWord_7585269).sum := by decide
  have hdescent : baseEnd_7585269 < baseStart_7585269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585272 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_7585272 : Nat := 118140960795 + 7585272 * 2 ^ 59
def prefixEnd_7585272 : Nat := 4983230072969 + 3 ^ 40 * 7585272 * 2
def baseEnd_7585272 : Nat := 3894890431090951822115975

theorem tailTrace_7585272 : CollatzResearch.WordTrace tailWord_7585272 prefixEnd_7585272 3894890431090951822115975 := by
  unfold tailWord_7585272
  simp only [CollatzResearch.WordTrace]
  refine ⟨138328799087931240082883035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184438398783908320110510713 138328799087931240082883035)
  ·
    refine ⟨207493198631896860124324553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138328799087931240082883035 207493198631896860124324553)
    ·
      refine ⟨155619898973922645093243415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207493198631896860124324553 155619898973922645093243415)
      ·
        refine ⟨233429848460883967639865123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155619898973922645093243415 233429848460883967639865123)
        ·
          refine ⟨350144772691325951459797685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233429848460883967639865123 350144772691325951459797685)
          ·
            refine ⟨32826072439811807949356033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350144772691325951459797685 32826072439811807949356033)
            ·
              refine ⟨24619554329858855962017025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32826072439811807949356033 24619554329858855962017025)
              ·
                refine ⟨18464665747394141971512769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24619554329858855962017025 18464665747394141971512769)
                ·
                  refine ⟨13848499310545606478634577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18464665747394141971512769 13848499310545606478634577)
                  ·
                    refine ⟨10386374482909204858975933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13848499310545606478634577 10386374482909204858975933)
                    ·
                      refine ⟨3894890431090951822115975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10386374482909204858975933 3894890431090951822115975)
                      ·
                        rfl

theorem cell23_7585272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_7585272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585272 prefixEnd_7585272 := by exact prefixLift 7585272
  have htrace : WordTrace (prefixWord ++ tailWord_7585272) baseStart_7585272 baseEnd_7585272 := by
    simpa [prefixWord, tailWord_7585272, baseEnd_7585272] using wordTrace_append hprefix tailTrace_7585272
  have hstable : (prefixWord ++ tailWord_7585272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585272).length < 2 ^ (prefixWord ++ tailWord_7585272).sum := by decide
  have hdescent : baseEnd_7585272 < baseStart_7585272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585285 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_7585285 : Nat := 118140960795 + 7585285 * 2 ^ 59
def prefixEnd_7585285 : Nat := 4983230072969 + 3 ^ 40 * 7585285 * 2
def baseEnd_7585285 : Nat := 3894897106339460271253415

theorem tailTrace_7585285 : CollatzResearch.WordTrace tailWord_7585285 prefixEnd_7585285 3894897106339460271253415 := by
  unfold tailWord_7585285
  simp only [CollatzResearch.WordTrace]
  refine ⟨276658072324815383385989309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184438714883210255590659539 276658072324815383385989309)
  ·
    refine ⟨103746777121805768769745991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276658072324815383385989309 103746777121805768769745991)
    ·
      refine ⟨155620165682708653154618987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103746777121805768769745991 155620165682708653154618987)
      ·
        refine ⟨233430248524062979731928481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155620165682708653154618987 233430248524062979731928481)
        ·
          refine ⟨175072686393047234798946361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233430248524062979731928481 175072686393047234798946361)
          ·
            refine ⟨131304514794785426099209771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175072686393047234798946361 131304514794785426099209771)
            ·
              refine ⟨196956772192178139148814657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131304514794785426099209771 196956772192178139148814657)
              ·
                refine ⟨147717579144133604361610993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196956772192178139148814657 147717579144133604361610993)
                ·
                  refine ⟨110788184358100203271208245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147717579144133604361610993 110788184358100203271208245)
                  ·
                    refine ⟨10386392283571894056675773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110788184358100203271208245 10386392283571894056675773)
                    ·
                      refine ⟨3894897106339460271253415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10386392283571894056675773 3894897106339460271253415)
                      ·
                        rfl

theorem cell23_7585285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_7585285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585285 prefixEnd_7585285 := by exact prefixLift 7585285
  have htrace : WordTrace (prefixWord ++ tailWord_7585285) baseStart_7585285 baseEnd_7585285 := by
    simpa [prefixWord, tailWord_7585285, baseEnd_7585285] using wordTrace_append hprefix tailTrace_7585285
  have hstable : (prefixWord ++ tailWord_7585285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585285).length < 2 ^ (prefixWord ++ tailWord_7585285).sum := by decide
  have hdescent : baseEnd_7585285 < baseStart_7585285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585336 : List Nat := [2, 1, 2, 1, 4, 2, 2, 4, 1, 1, 3]
def baseStart_7585336 : Nat := 118140960795 + 7585336 * 2 ^ 59
def prefixEnd_7585336 : Nat := 4983230072969 + 3 ^ 40 * 7585336 * 2
def baseEnd_7585336 : Nat := 3894923293852839571715681

theorem tailTrace_7585336 : CollatzResearch.WordTrace tailWord_7585336 prefixEnd_7585336 3894923293852839571715681 := by
  unfold tailWord_7585336
  simp only [CollatzResearch.WordTrace]
  refine ⟨138329966223815309548047931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184439954965087079397397241 138329966223815309548047931)
  ·
    refine ⟨207494949335722964322071897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138329966223815309548047931 207494949335722964322071897)
    ·
      refine ⟨155621212001792223241553923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207494949335722964322071897 155621212001792223241553923)
      ·
        refine ⟨233431818002688334862330885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155621212001792223241553923 233431818002688334862330885)
        ·
          refine ⟨43768465875504062786687041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233431818002688334862330885 43768465875504062786687041)
          ·
            refine ⟨32826349406628047090015281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43768465875504062786687041 32826349406628047090015281)
            ·
              refine ⟨24619762054971035317511461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32826349406628047090015281 24619762054971035317511461)
              ·
                refine ⟨4616205385307069122033399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24619762054971035317511461 4616205385307069122033399)
                ·
                  refine ⟨6924308077960603683050099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4616205385307069122033399 6924308077960603683050099)
                  ·
                    refine ⟨10386462116940905524575149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6924308077960603683050099 10386462116940905524575149)
                    ·
                      refine ⟨3894923293852839571715681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10386462116940905524575149 3894923293852839571715681)
                      ·
                        rfl

theorem cell23_7585336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 1, 3].length) (baseStart_7585336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585336 prefixEnd_7585336 := by exact prefixLift 7585336
  have htrace : WordTrace (prefixWord ++ tailWord_7585336) baseStart_7585336 baseEnd_7585336 := by
    simpa [prefixWord, tailWord_7585336, baseEnd_7585336] using wordTrace_append hprefix tailTrace_7585336
  have hstable : (prefixWord ++ tailWord_7585336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585336).length < 2 ^ (prefixWord ++ tailWord_7585336).sum := by decide
  have hdescent : baseEnd_7585336 < baseStart_7585336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585379 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 3]
def baseStart_7585379 : Nat := 118140960795 + 7585379 * 2 ^ 59
def prefixEnd_7585379 : Nat := 4983230072969 + 3 ^ 40 * 7585379 * 2
def baseEnd_7585379 : Nat := 3894945373520982903477983

theorem tailTrace_7585379 : CollatzResearch.WordTrace tailWord_7585379 prefixEnd_7585379 3894945373520982903477983 := by
  unfold tailWord_7585379
  simp only [CollatzResearch.WordTrace]
  refine ⟨276661500786474837439911191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184441000524316558293274127 276661500786474837439911191)
  ·
    refine ⟨414992251179712256159866787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276661500786474837439911191 414992251179712256159866787)
    ·
      refine ⟨622488376769568384239800181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414992251179712256159866787 622488376769568384239800181)
      ·
        refine ⟨58358285322147036022481267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 622488376769568384239800181 58358285322147036022481267)
        ·
          refine ⟨87537427983220554033721901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58358285322147036022481267 87537427983220554033721901)
          ·
            refine ⟨32826535493707707762645713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87537427983220554033721901 32826535493707707762645713)
            ·
              refine ⟨24619901620280780821984285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32826535493707707762645713 24619901620280780821984285)
              ·
                refine ⟨9232463107605292808244107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24619901620280780821984285 9232463107605292808244107)
                ·
                  refine ⟨13848694661407939212366161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9232463107605292808244107 13848694661407939212366161)
                  ·
                    refine ⟨10386520996055954409274621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13848694661407939212366161 10386520996055954409274621)
                    ·
                      refine ⟨3894945373520982903477983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10386520996055954409274621 3894945373520982903477983)
                      ·
                        rfl

theorem cell23_7585379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_7585379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585379 prefixEnd_7585379 := by exact prefixLift 7585379
  have htrace : WordTrace (prefixWord ++ tailWord_7585379) baseStart_7585379 baseEnd_7585379 := by
    simpa [prefixWord, tailWord_7585379, baseEnd_7585379] using wordTrace_append hprefix tailTrace_7585379
  have hstable : (prefixWord ++ tailWord_7585379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585379).length < 2 ^ (prefixWord ++ tailWord_7585379).sum := by decide
  have hdescent : baseEnd_7585379 < baseStart_7585379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585419 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 3, 3, 2]
def baseStart_7585419 : Nat := 118140960795 + 7585419 * 2 ^ 59
def prefixEnd_7585419 : Nat := 4983230072969 + 3 ^ 40 * 7585419 * 2
def baseEnd_7585419 : Nat := 3894965912747162746977799

theorem tailTrace_7585419 : CollatzResearch.WordTrace tailWord_7585419 prefixEnd_7585419 3894965912747162746977799 := by
  unfold tailWord_7585419
  simp only [CollatzResearch.WordTrace]
  refine ⟨276662959706329924271367311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184441973137553282847578207 276662959706329924271367311)
  ·
    refine ⟨414994439559494886407050967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276662959706329924271367311 414994439559494886407050967)
    ·
      refine ⟨622491659339242329610576451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414994439559494886407050967 622491659339242329610576451)
      ·
        refine ⟨933737489008863494415864677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622491659339242329610576451 933737489008863494415864677)
        ·
          refine ⟨175075779189161905202974627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 933737489008863494415864677 175075779189161905202974627)
          ·
            refine ⟨262613668783742857804461941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175075779189161905202974627 262613668783742857804461941)
            ·
              refine ⟨24620031448475892919168307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262613668783742857804461941 24620031448475892919168307)
              ·
                refine ⟨36930047172713839378752461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24620031448475892919168307 36930047172713839378752461)
                ·
                  refine ⟨13848767689767689767032173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36930047172713839378752461 13848767689767689767032173)
                  ·
                    refine ⟨5193287883662883662637065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13848767689767689767032173 5193287883662883662637065)
                    ·
                      refine ⟨3894965912747162746977799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193287883662883662637065 3894965912747162746977799)
                      ·
                        rfl

theorem cell23_7585419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 3, 2].length) (baseStart_7585419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585419 prefixEnd_7585419 := by exact prefixLift 7585419
  have htrace : WordTrace (prefixWord ++ tailWord_7585419) baseStart_7585419 baseEnd_7585419 := by
    simpa [prefixWord, tailWord_7585419, baseEnd_7585419] using wordTrace_append hprefix tailTrace_7585419
  have hstable : (prefixWord ++ tailWord_7585419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585419).length < 2 ^ (prefixWord ++ tailWord_7585419).sum := by decide
  have hdescent : baseEnd_7585419 < baseStart_7585419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585425 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 3, 8]
def baseStart_7585425 : Nat := 118140960795 + 7585425 * 2 ^ 59
def prefixEnd_7585425 : Nat := 4983230072969 + 3 ^ 40 * 7585425 * 2
def baseEnd_7585425 : Nat := 1298322997877029907834257

theorem tailTrace_7585425 : CollatzResearch.WordTrace tailWord_7585425 prefixEnd_7585425 1298322997877029907834257 := by
  unfold tailWord_7585425
  simp only [CollatzResearch.WordTrace]
  refine ⟨276663178544308187296085729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184442119029538791530723819 276663178544308187296085729)
  ·
    refine ⟨207497383908231140472064297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276663178544308187296085729 207497383908231140472064297)
    ·
      refine ⟨155623037931173355354048223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207497383908231140472064297 155623037931173355354048223)
      ·
        refine ⟨233434556896760033031072335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155623037931173355354048223 233434556896760033031072335)
        ·
          refine ⟨350151835345140049546608503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233434556896760033031072335 350151835345140049546608503)
          ·
            refine ⟨525227753017710074319912755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350151835345140049546608503 525227753017710074319912755)
            ·
              refine ⟨787841629526565111479869133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525227753017710074319912755 787841629526565111479869133)
              ·
                refine ⟨295440611072461916804950925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787841629526565111479869133 295440611072461916804950925)
                ·
                  refine ⟨110790229152173218801856597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295440611072461916804950925 110790229152173218801856597)
                  ·
                    refine ⟨1298322997877029907834257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110790229152173218801856597 1298322997877029907834257)
                    ·
                      rfl

theorem cell23_7585425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_7585425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585425 prefixEnd_7585425 := by exact prefixLift 7585425
  have htrace : WordTrace (prefixWord ++ tailWord_7585425) baseStart_7585425 baseEnd_7585425 := by
    simpa [prefixWord, tailWord_7585425, baseEnd_7585425] using wordTrace_append hprefix tailTrace_7585425
  have hstable : (prefixWord ++ tailWord_7585425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585425).length < 2 ^ (prefixWord ++ tailWord_7585425).sum := by decide
  have hdescent : baseEnd_7585425 < baseStart_7585425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585426 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_7585426 : Nat := 118140960795 + 7585426 * 2 ^ 59
def prefixEnd_7585426 : Nat := 4983230072969 + 3 ^ 40 * 7585426 * 2
def baseEnd_7585426 : Nat := 3894969507111744219590267

theorem tailTrace_7585426 : CollatzResearch.WordTrace tailWord_7585426 prefixEnd_7585426 3894969507111744219590267 := by
  unfold tailWord_7585426
  simp only [CollatzResearch.WordTrace]
  refine ⟨69165803754326141116718033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184442143344869709644581421 69165803754326141116718033)
  ·
    refine ⟨51874352815744605837538525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69165803754326141116718033 51874352815744605837538525)
    ·
      refine ⟨19452882305904227189076947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51874352815744605837538525 19452882305904227189076947)
      ·
        refine ⟨29179323458856340783615421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19452882305904227189076947 29179323458856340783615421)
        ·
          refine ⟨10942246297071127793855783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29179323458856340783615421 10942246297071127793855783)
          ·
            refine ⟨16413369445606691690783675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10942246297071127793855783 16413369445606691690783675)
            ·
              refine ⟨24620054168410037536175513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16413369445606691690783675 24620054168410037536175513)
              ·
                refine ⟨18465040626307528152131635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24620054168410037536175513 18465040626307528152131635)
                ·
                  refine ⟨27697560939461292228197453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18465040626307528152131635 27697560939461292228197453)
                  ·
                    refine ⟨10386585352297984585574045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27697560939461292228197453 10386585352297984585574045)
                    ·
                      refine ⟨3894969507111744219590267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10386585352297984585574045 3894969507111744219590267)
                      ·
                        rfl

theorem cell23_7585426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_7585426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585426 prefixEnd_7585426 := by exact prefixLift 7585426
  have htrace : WordTrace (prefixWord ++ tailWord_7585426) baseStart_7585426 baseEnd_7585426 := by
    simpa [prefixWord, tailWord_7585426, baseEnd_7585426] using wordTrace_append hprefix tailTrace_7585426
  have hstable : (prefixWord ++ tailWord_7585426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585426).length < 2 ^ (prefixWord ++ tailWord_7585426).sum := by decide
  have hdescent : baseEnd_7585426 < baseStart_7585426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585466 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2]
def baseStart_7585466 : Nat := 118140960795 + 7585466 * 2 ^ 59
def prefixEnd_7585466 : Nat := 4983230072969 + 3 ^ 40 * 7585466 * 2
def baseEnd_7585466 : Nat := 3894990046337924063090083

theorem tailTrace_7585466 : CollatzResearch.WordTrace tailWord_7585466 prefixEnd_7585466 3894990046337924063090083 := by
  unfold tailWord_7585466
  simp only [CollatzResearch.WordTrace]
  refine ⟨69166168484289912824582063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184443115958106434198885501 69166168484289912824582063)
  ·
    refine ⟨103749252726434869236873095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69166168484289912824582063 103749252726434869236873095)
    ·
      refine ⟨155623879089652303855309643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103749252726434869236873095 155623879089652303855309643)
      ·
        refine ⟨233435818634478455782964465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155623879089652303855309643 233435818634478455782964465)
        ·
          refine ⟨175076863975858841837223349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233435818634478455782964465 175076863975858841837223349)
          ·
            refine ⟨16413455997736766422239689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175076863975858841837223349 16413455997736766422239689)
            ·
              refine ⟨12310091998302574816679767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16413455997736766422239689 12310091998302574816679767)
              ·
                refine ⟨18465137997453862225019651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12310091998302574816679767 18465137997453862225019651)
                ·
                  refine ⟨27697706996180793337529477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18465137997453862225019651 27697706996180793337529477)
                  ·
                    refine ⟨5193320061783898750786777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27697706996180793337529477 5193320061783898750786777)
                    ·
                      refine ⟨3894990046337924063090083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193320061783898750786777 3894990046337924063090083)
                      ·
                        rfl

theorem cell23_7585466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_7585466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585466 prefixEnd_7585466 := by exact prefixLift 7585466
  have htrace : WordTrace (prefixWord ++ tailWord_7585466) baseStart_7585466 baseEnd_7585466 := by
    simpa [prefixWord, tailWord_7585466, baseEnd_7585466] using wordTrace_append hprefix tailTrace_7585466
  have hstable : (prefixWord ++ tailWord_7585466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585466).length < 2 ^ (prefixWord ++ tailWord_7585466).sum := by decide
  have hdescent : baseEnd_7585466 < baseStart_7585466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585472 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 7]
def baseStart_7585472 : Nat := 118140960795 + 7585472 * 2 ^ 59
def prefixEnd_7585472 : Nat := 4983230072969 + 3 ^ 40 * 7585472 * 2
def baseEnd_7585472 : Nat := 432777014135761226623895

theorem tailTrace_7585472 : CollatzResearch.WordTrace tailWord_7585472 prefixEnd_7585472 432777014135761226623895 := by
  unfold tailWord_7585472
  simp only [CollatzResearch.WordTrace]
  refine ⟨138332446387568957161523335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184443261850091942882031113 138332446387568957161523335)
  ·
    refine ⟨207498669581353435742285003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138332446387568957161523335 207498669581353435742285003)
    ·
      refine ⟨311248004372030153613427505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207498669581353435742285003 311248004372030153613427505)
      ·
        refine ⟨233436003279022615210070629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311248004372030153613427505 233436003279022615210070629)
        ·
          refine ⟨43769250614816740351888243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233436003279022615210070629 43769250614816740351888243)
          ·
            refine ⟨65653875922225110527832365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43769250614816740351888243 65653875922225110527832365)
            ·
              refine ⟨24620203470834416447937137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65653875922225110527832365 24620203470834416447937137)
              ·
                refine ⟨18465152603125812335952853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24620203470834416447937137 18465152603125812335952853)
                ·
                  refine ⟨432777014135761226623895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18465152603125812335952853 432777014135761226623895)
                  ·
                    rfl

theorem cell23_7585472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 7].length) (baseStart_7585472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585472 prefixEnd_7585472 := by exact prefixLift 7585472
  have htrace : WordTrace (prefixWord ++ tailWord_7585472) baseStart_7585472 baseEnd_7585472 := by
    simpa [prefixWord, tailWord_7585472, baseEnd_7585472] using wordTrace_append hprefix tailTrace_7585472
  have hstable : (prefixWord ++ tailWord_7585472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585472).length < 2 ^ (prefixWord ++ tailWord_7585472).sum := by decide
  have hdescent : baseEnd_7585472 < baseStart_7585472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585489 : List Nat := [1, 2, 2, 1, 2, 4, 1, 5, 5]
def baseStart_7585489 : Nat := 118140960795 + 7585489 * 2 ^ 59
def prefixEnd_7585489 : Nat := 4983230072969 + 3 ^ 40 * 7585489 * 2
def baseEnd_7585489 : Nat := 432777984043664163678053

theorem tailTrace_7585489 : CollatzResearch.WordTrace tailWord_7585489 prefixEnd_7585489 432777984043664163678053 := by
  unfold tailWord_7585489
  simp only [CollatzResearch.WordTrace]
  refine ⟨276665512816076326226415521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184443675210717550817610347 276665512816076326226415521)
  ·
    refine ⟨207499134612057244669811641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276665512816076326226415521 207499134612057244669811641)
    ·
      refine ⟨155624350959042933502358731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207499134612057244669811641 155624350959042933502358731)
      ·
        refine ⟨233436526438564400253538097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155624350959042933502358731 233436526438564400253538097)
        ·
          refine ⟨175077394828923300190153573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233436526438564400253538097 175077394828923300190153573)
          ·
            refine ⟨32827011530423118785653795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175077394828923300190153573 32827011530423118785653795)
            ·
              refine ⟨49240517295634678178480693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32827011530423118785653795 49240517295634678178480693)
              ·
                refine ⟨4616298496465751079232565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49240517295634678178480693 4616298496465751079232565)
                ·
                  refine ⟨432777984043664163678053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4616298496465751079232565 432777984043664163678053)
                  ·
                    rfl

theorem cell23_7585489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 5].length) (baseStart_7585489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585489 prefixEnd_7585489 := by exact prefixLift 7585489
  have htrace : WordTrace (prefixWord ++ tailWord_7585489) baseStart_7585489 baseEnd_7585489 := by
    simpa [prefixWord, tailWord_7585489, baseEnd_7585489] using wordTrace_append hprefix tailTrace_7585489
  have hstable : (prefixWord ++ tailWord_7585489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585489).length < 2 ^ (prefixWord ++ tailWord_7585489).sum := by decide
  have hdescent : baseEnd_7585489 < baseStart_7585489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585494 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7585494 : Nat := 118140960795 + 7585494 * 2 ^ 59
def prefixEnd_7585494 : Nat := 4983230072969 + 3 ^ 40 * 7585494 * 2
def baseEnd_7585494 : Nat := 3895004423796249953539955

theorem tailTrace_7585494 : CollatzResearch.WordTrace tailWord_7585494 prefixEnd_7585494 3895004423796249953539955 := by
  unfold tailWord_7585494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17291605948816138255021721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184443796787372141386898357 17291605948816138255021721)
  ·
    refine ⟨12968704461612103691266291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17291605948816138255021721 12968704461612103691266291)
    ·
      refine ⟨19453056692418155536899437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12968704461612103691266291 19453056692418155536899437)
      ·
        refine ⟨7294896259656808326337289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19453056692418155536899437 7294896259656808326337289)
        ·
          refine ⟨5471172194742606244752967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7294896259656808326337289 5471172194742606244752967)
          ·
            refine ⟨8206758292113909367129451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471172194742606244752967 8206758292113909367129451)
            ·
              refine ⟨12310137438170864050694177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206758292113909367129451 12310137438170864050694177)
              ·
                refine ⟨9232603078628148038020633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12310137438170864050694177 9232603078628148038020633)
                ·
                  refine ⟨6924452308971111028515475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9232603078628148038020633 6924452308971111028515475)
                  ·
                    refine ⟨10386678463456666542773213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6924452308971111028515475 10386678463456666542773213)
                    ·
                      refine ⟨3895004423796249953539955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10386678463456666542773213 3895004423796249953539955)
                      ·
                        rfl

theorem cell23_7585494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7585494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585494 prefixEnd_7585494 := by exact prefixLift 7585494
  have htrace : WordTrace (prefixWord ++ tailWord_7585494) baseStart_7585494 baseEnd_7585494 := by
    simpa [prefixWord, tailWord_7585494, baseEnd_7585494] using wordTrace_append hprefix tailTrace_7585494
  have hstable : (prefixWord ++ tailWord_7585494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585494).length < 2 ^ (prefixWord ++ tailWord_7585494).sum := by decide
  have hdescent : baseEnd_7585494 < baseStart_7585494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585500 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7585500 : Nat := 118140960795 + 7585500 * 2 ^ 59
def prefixEnd_7585500 : Nat := 4983230072969 + 3 ^ 40 * 7585500 * 2
def baseEnd_7585500 : Nat := 3895007504680176930064927

theorem tailTrace_7585500 : CollatzResearch.WordTrace tailWord_7585500 prefixEnd_7585500 3895007504680176930064927 := by
  unfold tailWord_7585500
  simp only [CollatzResearch.WordTrace]
  refine ⟨138332957009518237552532977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184443942679357650070043969 138332957009518237552532977)
  ·
    refine ⟨103749717757138678164399733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138332957009518237552532977 103749717757138678164399733)
    ·
      refine ⟨9726536039731751077912475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103749717757138678164399733 9726536039731751077912475)
      ·
        refine ⟨14589804059597626616868713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9726536039731751077912475 14589804059597626616868713)
        ·
          refine ⟨10942353044698219962651535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14589804059597626616868713 10942353044698219962651535)
          ·
            refine ⟨16413529567047329943977303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10942353044698219962651535 16413529567047329943977303)
            ·
              refine ⟨24620294350570994915965955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16413529567047329943977303 24620294350570994915965955)
              ·
                refine ⟨36930441525856492373948933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24620294350570994915965955 36930441525856492373948933)
                ·
                  refine ⟨6924457786098092320115425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36930441525856492373948933 6924457786098092320115425)
                  ·
                    refine ⟨5193343339573569240086569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6924457786098092320115425 5193343339573569240086569)
                    ·
                      refine ⟨3895007504680176930064927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193343339573569240086569 3895007504680176930064927)
                      ·
                        rfl

theorem cell23_7585500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7585500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585500 prefixEnd_7585500 := by exact prefixLift 7585500
  have htrace : WordTrace (prefixWord ++ tailWord_7585500) baseStart_7585500 baseEnd_7585500 := by
    simpa [prefixWord, tailWord_7585500, baseEnd_7585500] using wordTrace_append hprefix tailTrace_7585500
  have hstable : (prefixWord ++ tailWord_7585500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585500).length < 2 ^ (prefixWord ++ tailWord_7585500).sum := by decide
  have hdescent : baseEnd_7585500 < baseStart_7585500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585532 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_7585532 : Nat := 118140960795 + 7585532 * 2 ^ 59
def prefixEnd_7585532 : Nat := 4983230072969 + 3 ^ 40 * 7585532 * 2
def baseEnd_7585532 : Nat := 1298341312020373601621593

theorem tailTrace_7585532 : CollatzResearch.WordTrace tailWord_7585532 prefixEnd_7585532 1298341312020373601621593 := by
  unfold tailWord_7585532
  simp only [CollatzResearch.WordTrace]
  refine ⟨138333540577460272285115425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184444720769947029713487233 138333540577460272285115425)
  ·
    refine ⟨103750155433095204213836569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138333540577460272285115425 103750155433095204213836569)
    ·
      refine ⟨77812616574821403160377427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103750155433095204213836569 77812616574821403160377427)
      ·
        refine ⟨116718924862232104740566141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77812616574821403160377427 116718924862232104740566141)
        ·
          refine ⟨43769596823337039277712303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116718924862232104740566141 43769596823337039277712303)
          ·
            refine ⟨65654395235005558916568455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43769596823337039277712303 65654395235005558916568455)
            ·
              refine ⟨98481592852508338374852683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65654395235005558916568455 98481592852508338374852683)
              ·
                refine ⟨147722389278762507562279025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98481592852508338374852683 147722389278762507562279025)
                ·
                  refine ⟨110791791959071880671709269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147722389278762507562279025 110791791959071880671709269)
                  ·
                    refine ⟨1298341312020373601621593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110791791959071880671709269 1298341312020373601621593)
                    ·
                      rfl

theorem cell23_7585532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_7585532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585532 prefixEnd_7585532 := by exact prefixLift 7585532
  have htrace : WordTrace (prefixWord ++ tailWord_7585532) baseStart_7585532 baseEnd_7585532 := by
    simpa [prefixWord, tailWord_7585532, baseEnd_7585532] using wordTrace_append hprefix tailTrace_7585532
  have hstable : (prefixWord ++ tailWord_7585532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585532).length < 2 ^ (prefixWord ++ tailWord_7585532).sum := by decide
  have hdescent : baseEnd_7585532 < baseStart_7585532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585539 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 1, 6, 2]
def baseStart_7585539 : Nat := 118140960795 + 7585539 * 2 ^ 59
def prefixEnd_7585539 : Nat := 4983230072969 + 3 ^ 40 * 7585539 * 2
def baseEnd_7585539 : Nat := 3895027530425702277477247

theorem tailTrace_7585539 : CollatzResearch.WordTrace tailWord_7585539 prefixEnd_7585539 3895027530425702277477247 := by
  unfold tailWord_7585539
  simp only [CollatzResearch.WordTrace]
  refine ⟨276667336465895184765735671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184444890977263456510490447 276667336465895184765735671)
  ·
    refine ⟨415001004698842777148603507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276667336465895184765735671 415001004698842777148603507)
    ·
      refine ⟨622501507048264165722905261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415001004698842777148603507 622501507048264165722905261)
      ·
        refine ⟨233438065143099062146089473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622501507048264165722905261 233438065143099062146089473)
        ·
          refine ⟨175078548857324296609567105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233438065143099062146089473 175078548857324296609567105)
          ·
            refine ⟨131308911642993222457175329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175078548857324296609567105 131308911642993222457175329)
            ·
              refine ⟨98481683732244916842881497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131308911642993222457175329 98481683732244916842881497)
              ·
                refine ⟨73861262799183687632161123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98481683732244916842881497 73861262799183687632161123)
                ·
                  refine ⟨110791894198775531448241685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73861262799183687632161123 110791894198775531448241685)
                  ·
                    refine ⟨5193370040567603036636329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110791894198775531448241685 5193370040567603036636329)
                    ·
                      refine ⟨3895027530425702277477247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193370040567603036636329 3895027530425702277477247)
                      ·
                        rfl

theorem cell23_7585539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_7585539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585539 prefixEnd_7585539 := by exact prefixLift 7585539
  have htrace : WordTrace (prefixWord ++ tailWord_7585539) baseStart_7585539 baseEnd_7585539 := by
    simpa [prefixWord, tailWord_7585539, baseEnd_7585539] using wordTrace_append hprefix tailTrace_7585539
  have hstable : (prefixWord ++ tailWord_7585539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585539).length < 2 ^ (prefixWord ++ tailWord_7585539).sum := by decide
  have hdescent : baseEnd_7585539 < baseStart_7585539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585613 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 6]
def baseStart_7585613 : Nat := 118140960795 + 7585613 * 2 ^ 59
def prefixEnd_7585613 : Nat := 4983230072969 + 3 ^ 40 * 7585613 * 2
def baseEnd_7585613 : Nat := 432785058666014998661323

theorem tailTrace_7585613 : CollatzResearch.WordTrace tailWord_7585613 prefixEnd_7585613 432785058666014998661323 := by
  unfold tailWord_7585613
  simp only [CollatzResearch.WordTrace]
  refine ⟨276670035467627095403929493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184446690311751396935952995 276670035467627095403929493)
  ·
    refine ⟨12968907912545020097059195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 276670035467627095403929493 12968907912545020097059195)
    ·
      refine ⟨19453361868817530145588793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12968907912545020097059195 19453361868817530145588793)
      ·
        refine ⟨14590021401613147609191595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19453361868817530145588793 14590021401613147609191595)
        ·
          refine ⟨21885032102419721413787393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14590021401613147609191595 21885032102419721413787393)
          ·
            refine ⟨16413774076814791060340545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21885032102419721413787393 16413774076814791060340545)
            ·
              refine ⟨12310330557611093295255409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16413774076814791060340545 12310330557611093295255409)
              ·
                refine ⟨9232747918208319971441557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12310330557611093295255409 9232747918208319971441557)
                ·
                  refine ⟨432785058666014998661323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9232747918208319971441557 432785058666014998661323)
                  ·
                    rfl

theorem cell23_7585613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_7585613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585613 prefixEnd_7585613 := by exact prefixLift 7585613
  have htrace : WordTrace (prefixWord ++ tailWord_7585613) baseStart_7585613 baseEnd_7585613 := by
    simpa [prefixWord, tailWord_7585613, baseEnd_7585613] using wordTrace_append hprefix tailTrace_7585613
  have hstable : (prefixWord ++ tailWord_7585613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585613).length < 2 ^ (prefixWord ++ tailWord_7585613).sum := by decide
  have hdescent : baseEnd_7585613 < baseStart_7585613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585690 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_7585690 : Nat := 118140960795 + 7585690 * 2 ^ 59
def prefixEnd_7585690 : Nat := 4983230072969 + 3 ^ 40 * 7585690 * 2
def baseEnd_7585690 : Nat := 1298368355334843728896351

theorem tailTrace_7585690 : CollatzResearch.WordTrace tailWord_7585690 prefixEnd_7585690 1298368355334843728896351 := by
  unfold tailWord_7585690
  simp only [CollatzResearch.WordTrace]
  refine ⟨69168210972087034388620631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184448562592232091702988349 69168210972087034388620631)
  ·
    refine ⟨103752316458130551582930947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69168210972087034388620631 103752316458130551582930947)
    ·
      refine ⟨155628474687195827374396421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103752316458130551582930947 155628474687195827374396421)
      ·
        refine ⟨29180339003849217632699329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155628474687195827374396421 29180339003849217632699329)
        ·
          refine ⟨21885254252886913224524497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29180339003849217632699329 21885254252886913224524497)
          ·
            refine ⟨16413940689665184918393373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21885254252886913224524497 16413940689665184918393373)
            ·
              refine ⟨6155227758624444344397515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16413940689665184918393373 6155227758624444344397515)
              ·
                refine ⟨9232841637936666516596273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6155227758624444344397515 9232841637936666516596273)
                ·
                  refine ⟨6924631228452499887447205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9232841637936666516596273 6924631228452499887447205)
                  ·
                    refine ⟨1298368355334843728896351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6924631228452499887447205 1298368355334843728896351)
                    ·
                      rfl

theorem cell23_7585690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_7585690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585690 prefixEnd_7585690 := by exact prefixLift 7585690
  have htrace : WordTrace (prefixWord ++ tailWord_7585690) baseStart_7585690 baseEnd_7585690 := by
    simpa [prefixWord, tailWord_7585690, baseEnd_7585690] using wordTrace_append hprefix tailTrace_7585690
  have hstable : (prefixWord ++ tailWord_7585690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585690).length < 2 ^ (prefixWord ++ tailWord_7585690).sum := by decide
  have hdescent : baseEnd_7585690 < baseStart_7585690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585693 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_7585693 : Nat := 118140960795 + 7585693 * 2 ^ 59
def prefixEnd_7585693 : Nat := 4983230072969 + 3 ^ 40 * 7585693 * 2
def baseEnd_7585693 : Nat := 3895106606446494674951539

theorem tailTrace_7585693 : CollatzResearch.WordTrace tailWord_7585693 prefixEnd_7585693 3895106606446494674951539 := by
  unfold tailWord_7585693
  simp only [CollatzResearch.WordTrace]
  refine ⟨276672953307337269066841733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184448635538224846044561155 276672953307337269066841733)
  ·
    refine ⟨51876178745125737950032825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276672953307337269066841733 51876178745125737950032825)
    ·
      refine ⟨38907134058844303462524619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51876178745125737950032825 38907134058844303462524619)
      ·
        refine ⟨58360701088266455193786929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38907134058844303462524619 58360701088266455193786929)
        ·
          refine ⟨43770525816199841395340197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58360701088266455193786929 43770525816199841395340197)
          ·
            refine ⟨8206973590537470261626287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43770525816199841395340197 8206973590537470261626287)
            ·
              refine ⟨12310460385806205392439431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206973590537470261626287 12310460385806205392439431)
              ·
                refine ⟨18465690578709308088659147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12310460385806205392439431 18465690578709308088659147)
                ·
                  refine ⟨27698535868063962132988721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18465690578709308088659147 27698535868063962132988721)
                  ·
                    refine ⟨20773901901047971599741541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27698535868063962132988721 20773901901047971599741541)
                    ·
                      refine ⟨3895106606446494674951539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20773901901047971599741541 3895106606446494674951539)
                      ·
                        rfl

theorem cell23_7585693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_7585693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585693 prefixEnd_7585693 := by exact prefixLift 7585693
  have htrace : WordTrace (prefixWord ++ tailWord_7585693) baseStart_7585693 baseEnd_7585693 := by
    simpa [prefixWord, tailWord_7585693, baseEnd_7585693] using wordTrace_append hprefix tailTrace_7585693
  have hstable : (prefixWord ++ tailWord_7585693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585693).length < 2 ^ (prefixWord ++ tailWord_7585693).sum := by decide
  have hdescent : baseEnd_7585693 < baseStart_7585693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585703 : List Nat := [1, 1, 6, 1, 2, 3, 2, 7]
def baseStart_7585703 : Nat := 118140960795 + 7585703 * 2 ^ 59
def prefixEnd_7585703 : Nat := 4983230072969 + 3 ^ 40 * 7585703 * 2
def baseEnd_7585703 : Nat := 144263397824186653178759

theorem tailTrace_7585703 : CollatzResearch.WordTrace tailWord_7585703 prefixEnd_7585703 144263397824186653178759 := by
  unfold tailWord_7585703
  simp only [CollatzResearch.WordTrace]
  refine ⟨276673318037301040774705763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184448878691534027183137175 276673318037301040774705763)
  ·
    refine ⟨415009977055951561162058645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276673318037301040774705763 415009977055951561162058645)
    ·
      refine ⟨19453592674497729429471499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 415009977055951561162058645 19453592674497729429471499)
      ·
        refine ⟨29180389011746594144207249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19453592674497729429471499 29180389011746594144207249)
        ·
          refine ⟨21885291758809945608155437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29180389011746594144207249 21885291758809945608155437)
          ·
            refine ⟨8206984409553729603058289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21885291758809945608155437 8206984409553729603058289)
            ·
              refine ⟨6155238307165297202293717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8206984409553729603058289 6155238307165297202293717)
              ·
                refine ⟨144263397824186653178759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6155238307165297202293717 144263397824186653178759)
                ·
                  rfl

theorem cell23_7585703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 7].length) (baseStart_7585703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585703 prefixEnd_7585703 := by exact prefixLift 7585703
  have htrace : WordTrace (prefixWord ++ tailWord_7585703) baseStart_7585703 baseEnd_7585703 := by
    simpa [prefixWord, tailWord_7585703, baseEnd_7585703] using wordTrace_append hprefix tailTrace_7585703
  have hstable : (prefixWord ++ tailWord_7585703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585703).length < 2 ^ (prefixWord ++ tailWord_7585703).sum := by decide
  have hdescent : baseEnd_7585703 < baseStart_7585703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585713 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 3]
def baseStart_7585713 : Nat := 118140960795 + 7585713 * 2 ^ 59
def prefixEnd_7585713 : Nat := 4983230072969 + 3 ^ 40 * 7585713 * 2
def baseEnd_7585713 : Nat := 3895116876059584596701447

theorem tailTrace_7585713 : CollatzResearch.WordTrace tailWord_7585713 prefixEnd_7585713 3895116876059584596701447 := by
  unfold tailWord_7585713
  simp only [CollatzResearch.WordTrace]
  refine ⟨276673682767264812482569793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184449121844843208321713195 276673682767264812482569793)
  ·
    refine ⟨207505262075448609361927345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276673682767264812482569793 207505262075448609361927345)
    ·
      refine ⟨155628946556586457021445509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207505262075448609361927345 155628946556586457021445509)
      ·
        refine ⟨29180427479359960691521033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155628946556586457021445509 29180427479359960691521033)
        ·
          refine ⟨21885320609519970518640775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29180427479359960691521033 21885320609519970518640775)
          ·
            refine ⟨32827980914279955777961163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21885320609519970518640775 32827980914279955777961163)
            ·
              refine ⟨49241971371419933666941745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32827980914279955777961163 49241971371419933666941745)
              ·
                refine ⟨36931478528564950250206309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49241971371419933666941745 36931478528564950250206309)
                ·
                  refine ⟨6924652224105928171913683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36931478528564950250206309 6924652224105928171913683)
                  ·
                    refine ⟨10386978336158892257870525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6924652224105928171913683 10386978336158892257870525)
                    ·
                      refine ⟨3895116876059584596701447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10386978336158892257870525 3895116876059584596701447)
                      ·
                        rfl

theorem cell23_7585713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_7585713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585713 prefixEnd_7585713 := by exact prefixLift 7585713
  have htrace : WordTrace (prefixWord ++ tailWord_7585713) baseStart_7585713 baseEnd_7585713 := by
    simpa [prefixWord, tailWord_7585713, baseEnd_7585713] using wordTrace_append hprefix tailTrace_7585713
  have hstable : (prefixWord ++ tailWord_7585713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585713).length < 2 ^ (prefixWord ++ tailWord_7585713).sum := by decide
  have hdescent : baseEnd_7585713 < baseStart_7585713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585719 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_7585719 : Nat := 118140960795 + 7585719 * 2 ^ 59
def prefixEnd_7585719 : Nat := 4983230072969 + 3 ^ 40 * 7585719 * 2
def baseEnd_7585719 : Nat := 3895119956943511573226419

theorem tailTrace_7585719 : CollatzResearch.WordTrace tailWord_7585719 prefixEnd_7585719 3895119956943511573226419 := by
  unfold tailWord_7585719
  simp only [CollatzResearch.WordTrace]
  refine ⟨276673901605243075507288211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184449267736828717004858807 276673901605243075507288211)
  ·
    refine ⟨415010852407864613260932317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276673901605243075507288211 415010852407864613260932317)
    ·
      refine ⟨155629069652949229972849619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415010852407864613260932317 155629069652949229972849619)
      ·
        refine ⟨233443604479423844959274429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155629069652949229972849619 233443604479423844959274429)
        ·
          refine ⟨87541351679783941859727911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233443604479423844959274429 87541351679783941859727911)
          ·
            refine ⟨131312027519675912789591867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87541351679783941859727911 131312027519675912789591867)
            ·
              refine ⟨196968041279513869184387801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131312027519675912789591867 196968041279513869184387801)
              ·
                refine ⟨147726030959635401888290851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196968041279513869184387801 147726030959635401888290851)
                ·
                  refine ⟨221589046439453102832436277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147726030959635401888290851 221589046439453102832436277)
                  ·
                    refine ⟨20773973103698728390540901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 221589046439453102832436277 20773973103698728390540901)
                    ·
                      refine ⟨3895119956943511573226419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20773973103698728390540901 3895119956943511573226419)
                      ·
                        rfl

theorem cell23_7585719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_7585719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585719 prefixEnd_7585719 := by exact prefixLift 7585719
  have htrace : WordTrace (prefixWord ++ tailWord_7585719) baseStart_7585719 baseEnd_7585719 := by
    simpa [prefixWord, tailWord_7585719, baseEnd_7585719] using wordTrace_append hprefix tailTrace_7585719
  have hstable : (prefixWord ++ tailWord_7585719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585719).length < 2 ^ (prefixWord ++ tailWord_7585719).sum := by decide
  have hdescent : baseEnd_7585719 < baseStart_7585719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585739 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 5]
def baseStart_7585739 : Nat := 118140960795 + 7585739 * 2 ^ 59
def prefixEnd_7585739 : Nat := 4983230072969 + 3 ^ 40 * 7585739 * 2
def baseEnd_7585739 : Nat := 3895130226556601494976327

theorem tailTrace_7585739 : CollatzResearch.WordTrace tailWord_7585739 prefixEnd_7585739 3895130226556601494976327 := by
  unfold tailWord_7585739
  simp only [CollatzResearch.WordTrace]
  refine ⟨276674631065170618923016271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184449754043447079282010847 276674631065170618923016271)
  ·
    refine ⟨415011946597755928384524407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276674631065170618923016271 415011946597755928384524407)
    ·
      refine ⟨622517919896633892576786611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415011946597755928384524407 622517919896633892576786611)
      ·
        refine ⟨933776879844950838865179917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622517919896633892576786611 933776879844950838865179917)
        ·
          refine ⟨350166329941856564574442469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 933776879844950838865179917 350166329941856564574442469)
          ·
            refine ⟨65656186864098105857707963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350166329941856564574442469 65656186864098105857707963)
            ·
              refine ⟨98484280296147158786561945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65656186864098105857707963 98484280296147158786561945)
              ·
                refine ⟨73863210222110369089921459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98484280296147158786561945 73863210222110369089921459)
                ·
                  refine ⟨110794815333165553634882189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73863210222110369089921459 110794815333165553634882189)
                  ·
                    refine ⟨41548055749937082613080821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110794815333165553634882189 41548055749937082613080821)
                    ·
                      refine ⟨3895130226556601494976327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41548055749937082613080821 3895130226556601494976327)
                      ·
                        rfl

theorem cell23_7585739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_7585739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585739 prefixEnd_7585739 := by exact prefixLift 7585739
  have htrace : WordTrace (prefixWord ++ tailWord_7585739) baseStart_7585739 baseEnd_7585739 := by
    simpa [prefixWord, tailWord_7585739, baseEnd_7585739] using wordTrace_append hprefix tailTrace_7585739
  have hstable : (prefixWord ++ tailWord_7585739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585739).length < 2 ^ (prefixWord ++ tailWord_7585739).sum := by decide
  have hdescent : baseEnd_7585739 < baseStart_7585739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585793 : List Nat := [1, 2, 4, 1, 2, 1, 3, 4, 5]
def baseStart_7585793 : Nat := 118140960795 + 7585793 * 2 ^ 59
def prefixEnd_7585793 : Nat := 4983230072969 + 3 ^ 40 * 7585793 * 2
def baseEnd_7585793 : Nat := 432795328279104920411231

theorem tailTrace_7585793 : CollatzResearch.WordTrace tailWord_7585793 prefixEnd_7585793 432795328279104920411231 := by
  unfold tailWord_7585793
  simp only [CollatzResearch.WordTrace]
  refine ⟨276676600606974986145482033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184451067071316657430321355 276676600606974986145482033)
  ·
    refine ⟨207507450455231239609111525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276676600606974986145482033 207507450455231239609111525)
    ·
      refine ⟨38907646960355857426708411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207507450455231239609111525 38907646960355857426708411)
      ·
        refine ⟨58361470440533786140062617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38907646960355857426708411 58361470440533786140062617)
        ·
          refine ⟨43771102830400339605046963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58361470440533786140062617 43771102830400339605046963)
          ·
            refine ⟨65656654245600509407570445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43771102830400339605046963 65656654245600509407570445)
            ·
              refine ⟨24621245342100191027838917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65656654245600509407570445 24621245342100191027838917)
              ·
                refine ⟨4616483501643785817719797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24621245342100191027838917 4616483501643785817719797)
                ·
                  refine ⟨432795328279104920411231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4616483501643785817719797 432795328279104920411231)
                  ·
                    rfl

theorem cell23_7585793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 5].length) (baseStart_7585793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585793 prefixEnd_7585793 := by exact prefixLift 7585793
  have htrace : WordTrace (prefixWord ++ tailWord_7585793) baseStart_7585793 baseEnd_7585793 := by
    simpa [prefixWord, tailWord_7585793, baseEnd_7585793] using wordTrace_append hprefix tailTrace_7585793
  have hstable : (prefixWord ++ tailWord_7585793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585793).length < 2 ^ (prefixWord ++ tailWord_7585793).sum := by decide
  have hdescent : baseEnd_7585793 < baseStart_7585793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585806 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_7585806 : Nat := 118140960795 + 7585806 * 2 ^ 59
def prefixEnd_7585806 : Nat := 4983230072969 + 3 ^ 40 * 7585806 * 2
def baseEnd_7585806 : Nat := 1298388209920150910946173

theorem tailTrace_7585806 : CollatzResearch.WordTrace tailWord_7585806 prefixEnd_7585806 1298388209920150910946173 := by
  unfold tailWord_7585806
  simp only [CollatzResearch.WordTrace]
  refine ⟨34584634344490986170713159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184451383170618592910470181 34584634344490986170713159)
  ·
    refine ⟨51876951516736479256069739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34584634344490986170713159 51876951516736479256069739)
    ·
      refine ⟨77815427275104718884104609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51876951516736479256069739 77815427275104718884104609)
      ·
        refine ⟨58361570456328539163078457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77815427275104718884104609 58361570456328539163078457)
        ·
          refine ⟨43771177842246404372308843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58361570456328539163078457 43771177842246404372308843)
          ·
            refine ⟨65656766763369606558463265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43771177842246404372308843 65656766763369606558463265)
            ·
              refine ⟨49242575072527204918847449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65656766763369606558463265 49242575072527204918847449)
              ·
                refine ⟨36931931304395403689135587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49242575072527204918847449 36931931304395403689135587)
                ·
                  refine ⟨55397896956593105533703381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36931931304395403689135587 55397896956593105533703381)
                  ·
                    refine ⟨1298388209920150910946173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55397896956593105533703381 1298388209920150910946173)
                    ·
                      rfl

theorem cell23_7585806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_7585806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585806 prefixEnd_7585806 := by exact prefixLift 7585806
  have htrace : WordTrace (prefixWord ++ tailWord_7585806) baseStart_7585806 baseEnd_7585806 := by
    simpa [prefixWord, tailWord_7585806, baseEnd_7585806] using wordTrace_append hprefix tailTrace_7585806
  have hstable : (prefixWord ++ tailWord_7585806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585806).length < 2 ^ (prefixWord ++ tailWord_7585806).sum := by decide
  have hdescent : baseEnd_7585806 < baseStart_7585806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585819 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 1, 10]
def baseStart_7585819 : Nat := 118140960795 + 7585819 * 2 ^ 59
def prefixEnd_7585819 : Nat := 4983230072969 + 3 ^ 40 * 7585819 * 2
def baseEnd_7585819 : Nat := 1298390435002987060658653

theorem tailTrace_7585819 : CollatzResearch.WordTrace tailWord_7585819 prefixEnd_7585819 1298390435002987060658653 := by
  unfold tailWord_7585819
  simp only [CollatzResearch.WordTrace]
  refine ⟨276677548904880792585928511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184451699269920528390619007 276677548904880792585928511)
  ·
    refine ⟨415016323357321188878892767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276677548904880792585928511 415016323357321188878892767)
    ·
      refine ⟨622524485035981783318339151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415016323357321188878892767 622524485035981783318339151)
      ·
        refine ⟨933786727553972674977508727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622524485035981783318339151 933786727553972674977508727)
        ·
          refine ⟨1400680091330959012466263091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933786727553972674977508727 1400680091330959012466263091)
          ·
            refine ⟨2101020136996438518699394637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400680091330959012466263091 2101020136996438518699394637)
            ·
              refine ⟨787882551373664444512272989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2101020136996438518699394637 787882551373664444512272989)
              ·
                refine ⟨295455956765124166692102371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787882551373664444512272989 295455956765124166692102371)
                ·
                  refine ⟨443183935147686250038153557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295455956765124166692102371 443183935147686250038153557)
                  ·
                    refine ⟨1298390435002987060658653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 443183935147686250038153557 1298390435002987060658653)
                    ·
                      rfl

theorem cell23_7585819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 10].length) (baseStart_7585819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585819 prefixEnd_7585819 := by exact prefixLift 7585819
  have htrace : WordTrace (prefixWord ++ tailWord_7585819) baseStart_7585819 baseEnd_7585819 := by
    simpa [prefixWord, tailWord_7585819, baseEnd_7585819] using wordTrace_append hprefix tailTrace_7585819
  have hstable : (prefixWord ++ tailWord_7585819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585819).length < 2 ^ (prefixWord ++ tailWord_7585819).sum := by decide
  have hdescent : baseEnd_7585819 < baseStart_7585819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585843 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 2, 4, 2]
def baseStart_7585843 : Nat := 118140960795 + 7585843 * 2 ^ 59
def prefixEnd_7585843 : Nat := 4983230072969 + 3 ^ 40 * 7585843 * 2
def baseEnd_7585843 : Nat := 3895183628544669088075849

theorem tailTrace_7585843 : CollatzResearch.WordTrace tailWord_7585843 prefixEnd_7585843 3895183628544669088075849 := by
  unfold tailWord_7585843
  simp only [CollatzResearch.WordTrace]
  refine ⟨276678424256793844684802183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184452282837862563123201455 276678424256793844684802183)
  ·
    refine ⟨415017636385190767027203275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276678424256793844684802183 415017636385190767027203275)
    ·
      refine ⟨622526454577786150540804913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415017636385190767027203275 622526454577786150540804913)
      ·
        refine ⟨466894840933339612905603685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622526454577786150540804913 466894840933339612905603685)
        ·
          refine ⟨87542782675001177419800691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466894840933339612905603685 87542782675001177419800691)
          ·
            refine ⟨131314174012501766129701037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87542782675001177419800691 131314174012501766129701037)
            ·
              refine ⟨49242815254688162298637889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131314174012501766129701037 49242815254688162298637889)
              ·
                refine ⟨36932111441016121723978417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49242815254688162298637889 36932111441016121723978417)
                ·
                  refine ⟨27699083580762091292983813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36932111441016121723978417 27699083580762091292983813)
                  ·
                    refine ⟨5193578171392892117434465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27699083580762091292983813 5193578171392892117434465)
                    ·
                      refine ⟨3895183628544669088075849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193578171392892117434465 3895183628544669088075849)
                      ·
                        rfl

theorem cell23_7585843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 4, 2].length) (baseStart_7585843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585843 prefixEnd_7585843 := by exact prefixLift 7585843
  have htrace : WordTrace (prefixWord ++ tailWord_7585843) baseStart_7585843 baseEnd_7585843 := by
    simpa [prefixWord, tailWord_7585843, baseEnd_7585843] using wordTrace_append hprefix tailTrace_7585843
  have hstable : (prefixWord ++ tailWord_7585843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585843).length < 2 ^ (prefixWord ++ tailWord_7585843).sum := by decide
  have hdescent : baseEnd_7585843 < baseStart_7585843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585930 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_7585930 : Nat := 118140960795 + 7585930 * 2 ^ 59
def prefixEnd_7585930 : Nat := 4983230072969 + 3 ^ 40 * 7585930 * 2
def baseEnd_7585930 : Nat := 1298409433787203415895983

theorem tailTrace_7585930 : CollatzResearch.WordTrace tailWord_7585930 prefixEnd_7585930 1298409433787203415895983 := by
  unfold tailWord_7585930
  simp only [CollatzResearch.WordTrace]
  refine ⟨69170399351869664635804811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184454398271652439028812829 69170399351869664635804811)
  ·
    refine ⟨103755599027804496953707217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69170399351869664635804811 103755599027804496953707217)
    ·
      refine ⟨77816699270853372715280413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103755599027804496953707217 77816699270853372715280413)
      ·
        refine ⟨29181262226570014768230155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77816699270853372715280413 29181262226570014768230155)
        ·
          refine ⟨43771893339855022152345233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29181262226570014768230155 43771893339855022152345233)
          ·
            refine ⟨32828920004891266614258925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43771893339855022152345233 32828920004891266614258925)
            ·
              refine ⟨12310845001834224980347097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32828920004891266614258925 12310845001834224980347097)
              ·
                refine ⟨9233133751375668735260323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12310845001834224980347097 9233133751375668735260323)
                ·
                  refine ⟨13849700627063503102890485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9233133751375668735260323 13849700627063503102890485)
                  ·
                    refine ⟨1298409433787203415895983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13849700627063503102890485 1298409433787203415895983)
                    ·
                      rfl

theorem cell23_7585930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_7585930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585930 prefixEnd_7585930 := by exact prefixLift 7585930
  have htrace : WordTrace (prefixWord ++ tailWord_7585930) baseStart_7585930 baseEnd_7585930 := by
    simpa [prefixWord, tailWord_7585930, baseEnd_7585930] using wordTrace_append hprefix tailTrace_7585930
  have hstable : (prefixWord ++ tailWord_7585930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585930).length < 2 ^ (prefixWord ++ tailWord_7585930).sum := by decide
  have hdescent : baseEnd_7585930 < baseStart_7585930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7585956 : List Nat := [2, 3, 1, 2, 15]
def baseStart_7585956 : Nat := 118140960795 + 7585956 * 2 ^ 59
def prefixEnd_7585956 : Nat := 4983230072969 + 3 ^ 40 * 7585956 * 2
def baseEnd_7585956 : Nat := 5343267012151751914901

theorem tailTrace_7585956 : CollatzResearch.WordTrace tailWord_7585956 prefixEnd_7585956 5343267012151751914901 := by
  unfold tailWord_7585956
  simp only [CollatzResearch.WordTrace]
  refine ⟨138341272852692232491832861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184455030470256309989110481 138341272852692232491832861)
  ·
    refine ⟨51877977319759587184437323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138341272852692232491832861 51877977319759587184437323)
    ·
      refine ⟨77816965979639380776655985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51877977319759587184437323 77816965979639380776655985)
      ·
        refine ⟨58362724484729535582491989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77816965979639380776655985 58362724484729535582491989)
        ·
          refine ⟨5343267012151751914901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 58362724484729535582491989 5343267012151751914901)
          ·
            rfl

theorem cell23_7585956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 15].length) (baseStart_7585956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7585956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7585956 prefixEnd_7585956 := by exact prefixLift 7585956
  have htrace : WordTrace (prefixWord ++ tailWord_7585956) baseStart_7585956 baseEnd_7585956 := by
    simpa [prefixWord, tailWord_7585956, baseEnd_7585956] using wordTrace_append hprefix tailTrace_7585956
  have hstable : (prefixWord ++ tailWord_7585956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7585956).length < 2 ^ (prefixWord ++ tailWord_7585956).sum := by decide
  have hdescent : baseEnd_7585956 < baseStart_7585956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7585956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586033 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 2, 6]
def baseStart_7586033 : Nat := 118140960795 + 7586033 * 2 ^ 59
def prefixEnd_7586033 : Nat := 4983230072969 + 3 ^ 40 * 7586033 * 2
def baseEnd_7586033 : Nat := 1298427063289674448233325

theorem tailTrace_7586033 : CollatzResearch.WordTrace tailWord_7586033 prefixEnd_7586033 1298427063289674448233325 := by
  unfold tailWord_7586033
  simp only [CollatzResearch.WordTrace]
  refine ⟨276685354126105507134218753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184456902750737004756145835 276685354126105507134218753)
  ·
    refine ⟨207514015594579130350664065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276685354126105507134218753 207514015594579130350664065)
    ·
      refine ⟨155635511695934347762998049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207514015594579130350664065 155635511695934347762998049)
      ·
        refine ⟨116726633771950760822248537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155635511695934347762998049 116726633771950760822248537)
        ·
          refine ⟨87544975328963070616686403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116726633771950760822248537 87544975328963070616686403)
          ·
            refine ⟨131317462993444605925029605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87544975328963070616686403 131317462993444605925029605)
            ·
              refine ⟨24622024311270863610943051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131317462993444605925029605 24622024311270863610943051)
              ·
                refine ⟨36933036466906295416414577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24622024311270863610943051 36933036466906295416414577)
                ·
                  refine ⟨27699777350179721562310933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36933036466906295416414577 27699777350179721562310933)
                  ·
                    refine ⟨1298427063289674448233325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27699777350179721562310933 1298427063289674448233325)
                    ·
                      rfl

theorem cell23_7586033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_7586033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586033 prefixEnd_7586033 := by exact prefixLift 7586033
  have htrace : WordTrace (prefixWord ++ tailWord_7586033) baseStart_7586033 baseEnd_7586033 := by
    simpa [prefixWord, tailWord_7586033, baseEnd_7586033] using wordTrace_append hprefix tailTrace_7586033
  have hstable : (prefixWord ++ tailWord_7586033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586033).length < 2 ^ (prefixWord ++ tailWord_7586033).sum := by decide
  have hdescent : baseEnd_7586033 < baseStart_7586033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586044 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_7586044 : Nat := 118140960795 + 7586044 * 2 ^ 59
def prefixEnd_7586044 : Nat := 4983230072969 + 3 ^ 40 * 7586044 * 2
def baseEnd_7586044 : Nat := 3895286838156222801662425

theorem tailTrace_7586044 : CollatzResearch.WordTrace tailWord_7586044 prefixEnd_7586044 3895286838156222801662425 := by
  unfold tailWord_7586044
  simp only [CollatzResearch.WordTrace]
  refine ⟨138342877664532828006434593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184457170219377104008579457 138342877664532828006434593)
  ·
    refine ⟨103757158248399621004825945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138342877664532828006434593 103757158248399621004825945)
    ·
      refine ⟨77817868686299715753619459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103757158248399621004825945 77817868686299715753619459)
      ·
        refine ⟨116726803029449573630429189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77817868686299715753619459 116726803029449573630429189)
        ·
          refine ⟨21886275568021795055705473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116726803029449573630429189 21886275568021795055705473)
          ·
            refine ⟨16414706676016346291779105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21886275568021795055705473 16414706676016346291779105)
            ·
              refine ⟨12311030007012259718834329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16414706676016346291779105 12311030007012259718834329)
              ·
                refine ⟨9233272505259194789125747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12311030007012259718834329 9233272505259194789125747)
                ·
                  refine ⟨13849908757888792183688621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9233272505259194789125747 13849908757888792183688621)
                  ·
                    refine ⟨5193715784208297068883233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13849908757888792183688621 5193715784208297068883233)
                    ·
                      refine ⟨3895286838156222801662425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193715784208297068883233 3895286838156222801662425)
                      ·
                        rfl

theorem cell23_7586044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_7586044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586044 prefixEnd_7586044 := by exact prefixLift 7586044
  have htrace : WordTrace (prefixWord ++ tailWord_7586044) baseStart_7586044 baseEnd_7586044 := by
    simpa [prefixWord, tailWord_7586044, baseEnd_7586044] using wordTrace_append hprefix tailTrace_7586044
  have hstable : (prefixWord ++ tailWord_7586044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586044).length < 2 ^ (prefixWord ++ tailWord_7586044).sum := by decide
  have hdescent : baseEnd_7586044 < baseStart_7586044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586053 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_7586053 : Nat := 118140960795 + 7586053 * 2 ^ 59
def prefixEnd_7586053 : Nat := 4983230072969 + 3 ^ 40 * 7586053 * 2
def baseEnd_7586053 : Nat := 3895291459482113266449883

theorem tailTrace_7586053 : CollatzResearch.WordTrace tailWord_7586053 prefixEnd_7586053 3895291459482113266449883 := by
  unfold tailWord_7586053
  simp only [CollatzResearch.WordTrace]
  refine ⟨276686083586033050549946813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184457389057355367033297875 276686083586033050549946813)
  ·
    refine ⟨103757281344762393956230055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276686083586033050549946813 103757281344762393956230055)
    ·
      refine ⟨155635922017143590934345083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103757281344762393956230055 155635922017143590934345083)
      ·
        refine ⟨233453883025715386401517625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155635922017143590934345083 233453883025715386401517625)
        ·
          refine ⟨175090412269286539801138219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233453883025715386401517625 175090412269286539801138219)
          ·
            refine ⟨262635618403929809701707329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175090412269286539801138219 262635618403929809701707329)
            ·
              refine ⟨196976713802947357276280497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262635618403929809701707329 196976713802947357276280497)
              ·
                refine ⟨147732535352210517957210373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196976713802947357276280497 147732535352210517957210373)
                ·
                  refine ⟨27699850378539472116976945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147732535352210517957210373 27699850378539472116976945)
                  ·
                    refine ⟨20774887783904604087732709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27699850378539472116976945 20774887783904604087732709)
                    ·
                      refine ⟨3895291459482113266449883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20774887783904604087732709 3895291459482113266449883)
                      ·
                        rfl

theorem cell23_7586053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_7586053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586053 prefixEnd_7586053 := by exact prefixLift 7586053
  have htrace : WordTrace (prefixWord ++ tailWord_7586053) baseStart_7586053 baseEnd_7586053 := by
    simpa [prefixWord, tailWord_7586053, baseEnd_7586053] using wordTrace_append hprefix tailTrace_7586053
  have hstable : (prefixWord ++ tailWord_7586053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586053).length < 2 ^ (prefixWord ++ tailWord_7586053).sum := by decide
  have hdescent : baseEnd_7586053 < baseStart_7586053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586057 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 4, 2, 2]
def baseStart_7586057 : Nat := 118140960795 + 7586057 * 2 ^ 59
def prefixEnd_7586057 : Nat := 4983230072969 + 3 ^ 40 * 7586057 * 2
def baseEnd_7586057 : Nat := 3895293513404731250799865

theorem tailTrace_7586057 : CollatzResearch.WordTrace tailWord_7586057 prefixEnd_7586057 3895293513404731250799865 := by
  unfold tailWord_7586057
  simp only [CollatzResearch.WordTrace]
  refine ⟨276686229478018559233092425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184457486318679039488728283 276686229478018559233092425)
  ·
    refine ⟨207514672108513919424819319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276686229478018559233092425 207514672108513919424819319)
    ·
      refine ⟨311272008162770879137228979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207514672108513919424819319 311272008162770879137228979)
      ·
        refine ⟨466908012244156318705843469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311272008162770879137228979 466908012244156318705843469)
        ·
          refine ⟨175090504591558619514691301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466908012244156318705843469 175090504591558619514691301)
          ·
            refine ⟨32829469610917241159004619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175090504591558619514691301 32829469610917241159004619)
            ·
              refine ⟨49244204416375861738506929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32829469610917241159004619 49244204416375861738506929)
              ·
                refine ⟨36933153312281896303880197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49244204416375861738506929 36933153312281896303880197)
                ·
                  refine ⟨6924966246052855556977537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36933153312281896303880197 6924966246052855556977537)
                  ·
                    refine ⟨5193724684539641667733153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6924966246052855556977537 5193724684539641667733153)
                    ·
                      refine ⟨3895293513404731250799865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193724684539641667733153 3895293513404731250799865)
                      ·
                        rfl

theorem cell23_7586057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 2, 2].length) (baseStart_7586057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586057 prefixEnd_7586057 := by exact prefixLift 7586057
  have htrace : WordTrace (prefixWord ++ tailWord_7586057) baseStart_7586057 baseEnd_7586057 := by
    simpa [prefixWord, tailWord_7586057, baseEnd_7586057] using wordTrace_append hprefix tailTrace_7586057
  have hstable : (prefixWord ++ tailWord_7586057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586057).length < 2 ^ (prefixWord ++ tailWord_7586057).sum := by decide
  have hdescent : baseEnd_7586057 < baseStart_7586057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586080 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 7]
def baseStart_7586080 : Nat := 118140960795 + 7586080 * 2 ^ 59
def prefixEnd_7586080 : Nat := 4983230072969 + 3 ^ 40 * 7586080 * 2
def baseEnd_7586080 : Nat := 432811702606642740090251

theorem tailTrace_7586080 : CollatzResearch.WordTrace tailWord_7586080 prefixEnd_7586080 432811702606642740090251 := by
  unfold tailWord_7586080
  simp only [CollatzResearch.WordTrace]
  refine ⟨138343534178467617080589847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184458045571290156107453129 138343534178467617080589847)
  ·
    refine ⟨207515301267701425620884771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138343534178467617080589847 207515301267701425620884771)
    ·
      refine ⟨311272951901552138431327157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207515301267701425620884771 311272951901552138431327157)
      ·
        refine ⟨29181839240770512977936921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311272951901552138431327157 29181839240770512977936921)
        ·
          refine ⟨21886379430577884733452691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29181839240770512977936921 21886379430577884733452691)
          ·
            refine ⟨32829569145866827100179037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21886379430577884733452691 32829569145866827100179037)
            ·
              refine ⟨12311088429700060162567139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32829569145866827100179037 12311088429700060162567139)
              ·
                refine ⟨18466632644550090243850709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12311088429700060162567139 18466632644550090243850709)
                ·
                  refine ⟨432811702606642740090251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18466632644550090243850709 432811702606642740090251)
                  ·
                    rfl

theorem cell23_7586080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 7].length) (baseStart_7586080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586080 prefixEnd_7586080 := by exact prefixLift 7586080
  have htrace : WordTrace (prefixWord ++ tailWord_7586080) baseStart_7586080 baseEnd_7586080 := by
    simpa [prefixWord, tailWord_7586080, baseEnd_7586080] using wordTrace_append hprefix tailTrace_7586080
  have hstable : (prefixWord ++ tailWord_7586080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586080).length < 2 ^ (prefixWord ++ tailWord_7586080).sum := by decide
  have hdescent : baseEnd_7586080 < baseStart_7586080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586147 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 2, 4, 2]
def baseStart_7586147 : Nat := 118140960795 + 7586147 * 2 ^ 59
def prefixEnd_7586147 : Nat := 4983230072969 + 3 ^ 40 * 7586147 * 2
def baseEnd_7586147 : Nat := 3895339726663635898674451

theorem tailTrace_7586147 : CollatzResearch.WordTrace tailWord_7586147 prefixEnd_7586147 3895339726663635898674451 := by
  unfold tailWord_7586147
  simp only [CollatzResearch.WordTrace]
  refine ⟨276689512047692504603868695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184459674698461669735912463 276689512047692504603868695)
  ·
    refine ⟨415034268071538756905803043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276689512047692504603868695 415034268071538756905803043)
    ·
      refine ⟨622551402107308135358704565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415034268071538756905803043 622551402107308135358704565)
      ·
        refine ⟨58364193947560137689878553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 622551402107308135358704565 58364193947560137689878553)
        ·
          refine ⟨43773145460670103267408915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58364193947560137689878553 43773145460670103267408915)
          ·
            refine ⟨65659718191005154901113373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43773145460670103267408915 65659718191005154901113373)
            ·
              refine ⟨24622394321626933087917515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65659718191005154901113373 24622394321626933087917515)
              ·
                refine ⟨36933591482440399631876273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24622394321626933087917515 36933591482440399631876273)
                ·
                  refine ⟨27700193611830299723907205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36933591482440399631876273 27700193611830299723907205)
                  ·
                    refine ⟨5193786302218181198232601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27700193611830299723907205 5193786302218181198232601)
                    ·
                      refine ⟨3895339726663635898674451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193786302218181198232601 3895339726663635898674451)
                      ·
                        rfl

theorem cell23_7586147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_7586147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586147 prefixEnd_7586147 := by exact prefixLift 7586147
  have htrace : WordTrace (prefixWord ++ tailWord_7586147) baseStart_7586147 baseEnd_7586147 := by
    simpa [prefixWord, tailWord_7586147, baseEnd_7586147] using wordTrace_append hprefix tailTrace_7586147
  have hstable : (prefixWord ++ tailWord_7586147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586147).length < 2 ^ (prefixWord ++ tailWord_7586147).sum := by decide
  have hdescent : baseEnd_7586147 < baseStart_7586147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586157 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_7586157 : Nat := 118140960795 + 7586157 * 2 ^ 59
def prefixEnd_7586157 : Nat := 4983230072969 + 3 ^ 40 * 7586157 * 2
def baseEnd_7586157 : Nat := 1298448287156726953183135

theorem tailTrace_7586157 : CollatzResearch.WordTrace tailWord_7586157 prefixEnd_7586157 1298448287156726953183135 := by
  unfold tailWord_7586157
  simp only [CollatzResearch.WordTrace]
  refine ⟨276689876777656276311732725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184459917851770850874488483 276689876777656276311732725)
  ·
    refine ⟨25939675947905275904224943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276689876777656276311732725 25939675947905275904224943)
    ·
      refine ⟨38909513921857913856337415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25939675947905275904224943 38909513921857913856337415)
      ·
        refine ⟨58364270882786870784506123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38909513921857913856337415 58364270882786870784506123)
        ·
          refine ⟨87546406324180306176759185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58364270882786870784506123 87546406324180306176759185)
          ·
            refine ⟨65659804743135229632569389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87546406324180306176759185 65659804743135229632569389)
            ·
              refine ⟨24622426778675711112213521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65659804743135229632569389 24622426778675711112213521)
              ·
                refine ⟨18466820084006783334160141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24622426778675711112213521 18466820084006783334160141)
                ·
                  refine ⟨6925057531502543750310053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18466820084006783334160141 6925057531502543750310053)
                  ·
                    refine ⟨1298448287156726953183135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6925057531502543750310053 1298448287156726953183135)
                    ·
                      rfl

theorem cell23_7586157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_7586157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586157 prefixEnd_7586157 := by exact prefixLift 7586157
  have htrace : WordTrace (prefixWord ++ tailWord_7586157) baseStart_7586157 baseEnd_7586157 := by
    simpa [prefixWord, tailWord_7586157, baseEnd_7586157] using wordTrace_append hprefix tailTrace_7586157
  have hstable : (prefixWord ++ tailWord_7586157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586157).length < 2 ^ (prefixWord ++ tailWord_7586157).sum := by decide
  have hdescent : baseEnd_7586157 < baseStart_7586157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586187 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 6]
def baseStart_7586187 : Nat := 118140960795 + 7586187 * 2 ^ 59
def prefixEnd_7586187 : Nat := 4983230072969 + 3 ^ 40 * 7586187 * 2
def baseEnd_7586187 : Nat := 432817807321090638019363

theorem tailTrace_7586187 : CollatzResearch.WordTrace tailWord_7586187 prefixEnd_7586187 432817807321090638019363 := by
  unfold tailWord_7586187
  simp only [CollatzResearch.WordTrace]
  refine ⟨276690970967547591435324815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184460647311698394290216543 276690970967547591435324815)
  ·
    refine ⟨415036456451321387152987223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276690970967547591435324815 415036456451321387152987223)
    ·
      refine ⟨622554684676982080729480835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415036456451321387152987223 622554684676982080729480835)
      ·
        refine ⟨933832027015473121094221253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622554684676982080729480835 933832027015473121094221253)
        ·
          refine ⟨175093505065401210205166485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 933832027015473121094221253 175093505065401210205166485)
          ·
            refine ⟨8207508049940681728367179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175093505065401210205166485 8207508049940681728367179)
            ·
              refine ⟨12311262074911022592550769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207508049940681728367179 12311262074911022592550769)
              ·
                refine ⟨9233446556183266944413077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12311262074911022592550769 9233446556183266944413077)
                ·
                  refine ⟨432817807321090638019363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9233446556183266944413077 432817807321090638019363)
                  ·
                    rfl

theorem cell23_7586187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 6].length) (baseStart_7586187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586187 prefixEnd_7586187 := by exact prefixLift 7586187
  have htrace : WordTrace (prefixWord ++ tailWord_7586187) baseStart_7586187 baseEnd_7586187 := by
    simpa [prefixWord, tailWord_7586187, baseEnd_7586187] using wordTrace_append hprefix tailTrace_7586187
  have hstable : (prefixWord ++ tailWord_7586187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586187).length < 2 ^ (prefixWord ++ tailWord_7586187).sum := by decide
  have hdescent : baseEnd_7586187 < baseStart_7586187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586207 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 3, 5, 2]
def baseStart_7586207 : Nat := 118140960795 + 7586207 * 2 ^ 59
def prefixEnd_7586207 : Nat := 4983230072969 + 3 ^ 40 * 7586207 * 2
def baseEnd_7586207 : Nat := 3895370535502905663924175

theorem tailTrace_7586207 : CollatzResearch.WordTrace tailWord_7586207 prefixEnd_7586207 3895370535502905663924175 := by
  unfold tailWord_7586207
  simp only [CollatzResearch.WordTrace]
  refine ⟨276691700427475134851052875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184461133618316756567368583 276691700427475134851052875)
  ·
    refine ⟨415037550641212702276579313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276691700427475134851052875 415037550641212702276579313)
    ·
      refine ⟨311278162980909526707434485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415037550641212702276579313 311278162980909526707434485)
      ·
        refine ⟨29182327779460268128821983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311278162980909526707434485 29182327779460268128821983)
        ·
          refine ⟨43773491669190402193232975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29182327779460268128821983 43773491669190402193232975)
          ·
            refine ⟨65660237503785603289849463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43773491669190402193232975 65660237503785603289849463)
            ·
              refine ⟨98490356255678404934774195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65660237503785603289849463 98490356255678404934774195)
              ·
                refine ⟨147735534383517607402161293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98490356255678404934774195 147735534383517607402161293)
                ·
                  refine ⟨55400825393819102775810485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147735534383517607402161293 55400825393819102775810485)
                  ·
                    refine ⟨5193827380670540885232233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55400825393819102775810485 5193827380670540885232233)
                    ·
                      refine ⟨3895370535502905663924175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193827380670540885232233 3895370535502905663924175)
                      ·
                        rfl

theorem cell23_7586207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_7586207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586207 prefixEnd_7586207 := by exact prefixLift 7586207
  have htrace : WordTrace (prefixWord ++ tailWord_7586207) baseStart_7586207 baseEnd_7586207 := by
    simpa [prefixWord, tailWord_7586207, baseEnd_7586207] using wordTrace_append hprefix tailTrace_7586207
  have hstable : (prefixWord ++ tailWord_7586207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586207).length < 2 ^ (prefixWord ++ tailWord_7586207).sum := by decide
  have hdescent : baseEnd_7586207 < baseStart_7586207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586231 : List Nat := [1, 1, 3, 1, 3, 3, 3, 3, 1, 1, 3]
def baseStart_7586231 : Nat := 118140960795 + 7586231 * 2 ^ 59
def prefixEnd_7586231 : Nat := 4983230072969 + 3 ^ 40 * 7586231 * 2
def baseEnd_7586231 : Nat := 3895382859038613570024065

theorem tailTrace_7586231 : CollatzResearch.WordTrace tailWord_7586231 prefixEnd_7586231 3895382859038613570024065 := by
  unfold tailWord_7586231
  simp only [CollatzResearch.WordTrace]
  refine ⟨276692575779388186949926547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184461717186258791299951031 276692575779388186949926547)
  ·
    refine ⟨415038863669082280424889821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276692575779388186949926547 415038863669082280424889821)
    ·
      refine ⟨155639573875905855159333683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415038863669082280424889821 155639573875905855159333683)
      ·
        refine ⟨233459360813858782739000525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155639573875905855159333683 233459360813858782739000525)
        ·
          refine ⟨87547260305197043527125197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233459360813858782739000525 87547260305197043527125197)
          ·
            refine ⟨32830222614448891322671949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87547260305197043527125197 32830222614448891322671949)
            ·
              refine ⟨12311333480418334246001981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32830222614448891322671949 12311333480418334246001981)
              ·
                refine ⟨4616750055156875342250743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12311333480418334246001981 4616750055156875342250743)
                ·
                  refine ⟨6925125082735313013376115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4616750055156875342250743 6925125082735313013376115)
                  ·
                    refine ⟨10387687624102969520064173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6925125082735313013376115 10387687624102969520064173)
                    ·
                      refine ⟨3895382859038613570024065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10387687624102969520064173 3895382859038613570024065)
                      ·
                        rfl

theorem cell23_7586231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 1, 3].length) (baseStart_7586231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586231 prefixEnd_7586231 := by exact prefixLift 7586231
  have htrace : WordTrace (prefixWord ++ tailWord_7586231) baseStart_7586231 baseEnd_7586231 := by
    simpa [prefixWord, tailWord_7586231, baseEnd_7586231] using wordTrace_append hprefix tailTrace_7586231
  have hstable : (prefixWord ++ tailWord_7586231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586231).length < 2 ^ (prefixWord ++ tailWord_7586231).sum := by decide
  have hdescent : baseEnd_7586231 < baseStart_7586231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586247 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 4, 4]
def baseStart_7586247 : Nat := 118140960795 + 7586247 * 2 ^ 59
def prefixEnd_7586247 : Nat := 4983230072969 + 3 ^ 40 * 7586247 * 2
def baseEnd_7586247 : Nat := 1298463691576361835807997

theorem tailTrace_7586247 : CollatzResearch.WordTrace tailWord_7586247 prefixEnd_7586247 1298463691576361835807997 := by
  unfold tailWord_7586247
  simp only [CollatzResearch.WordTrace]
  refine ⟨276693159347330221682508995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184462106231553481121672663 276693159347330221682508995)
  ·
    refine ⟨415039739020995332523763493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276693159347330221682508995 415039739020995332523763493)
    ·
      refine ⟨77819951066436624848205655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415039739020995332523763493 77819951066436624848205655)
      ·
        refine ⟨116729926599654937272308483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77819951066436624848205655 116729926599654937272308483)
        ·
          refine ⟨175094889899482405908462725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116729926599654937272308483 175094889899482405908462725)
          ·
            refine ⟨32830291856152951107836761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175094889899482405908462725 32830291856152951107836761)
            ·
              refine ⟨24622718892114713330877571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32830291856152951107836761 24622718892114713330877571)
              ·
                refine ⟨36934078338172069996316357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24622718892114713330877571 36934078338172069996316357)
                ·
                  refine ⟨6925139688407263124309317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36934078338172069996316357 6925139688407263124309317)
                  ·
                    refine ⟨1298463691576361835807997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6925139688407263124309317 1298463691576361835807997)
                    ·
                      rfl

theorem cell23_7586247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_7586247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586247 prefixEnd_7586247 := by exact prefixLift 7586247
  have htrace : WordTrace (prefixWord ++ tailWord_7586247) baseStart_7586247 baseEnd_7586247 := by
    simpa [prefixWord, tailWord_7586247, baseEnd_7586247] using wordTrace_append hprefix tailTrace_7586247
  have hstable : (prefixWord ++ tailWord_7586247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586247).length < 2 ^ (prefixWord ++ tailWord_7586247).sum := by decide
  have hdescent : baseEnd_7586247 < baseStart_7586247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586248 : List Nat := [2, 1, 3, 1, 3, 3, 3, 2, 1, 1, 3]
def baseStart_7586248 : Nat := 118140960795 + 7586248 * 2 ^ 59
def prefixEnd_7586248 : Nat := 4983230072969 + 3 ^ 40 * 7586248 * 2
def baseEnd_7586248 : Nat := 3895391588209740003511487

theorem tailTrace_7586248 : CollatzResearch.WordTrace tailWord_7586248 prefixEnd_7586248 3895391588209740003511487 := by
  unfold tailWord_7586248
  simp only [CollatzResearch.WordTrace]
  refine ⟨138346597910163299426647699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184462130546884399235530265 138346597910163299426647699)
  ·
    refine ⟨207519896865244949139971549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138346597910163299426647699 207519896865244949139971549)
    ·
      refine ⟨77819961324466855927489331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207519896865244949139971549 77819961324466855927489331)
      ·
        refine ⟨116729941986700283891233997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77819961324466855927489331 116729941986700283891233997)
        ·
          refine ⟨43773728245012606459212749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116729941986700283891233997 43773728245012606459212749)
          ·
            refine ⟨16415148091879727422204781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43773728245012606459212749 16415148091879727422204781)
            ·
              refine ⟨6155680534454897783326793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16415148091879727422204781 6155680534454897783326793)
              ·
                refine ⟨4616760400841173337495095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6155680534454897783326793 4616760400841173337495095)
                ·
                  refine ⟨6925140601261760006242643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4616760400841173337495095 6925140601261760006242643)
                  ·
                    refine ⟨10387710901892640009363965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6925140601261760006242643 10387710901892640009363965)
                    ·
                      refine ⟨3895391588209740003511487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10387710901892640009363965 3895391588209740003511487)
                      ·
                        rfl

theorem cell23_7586248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_7586248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586248 prefixEnd_7586248 := by exact prefixLift 7586248
  have htrace : WordTrace (prefixWord ++ tailWord_7586248) baseStart_7586248 baseEnd_7586248 := by
    simpa [prefixWord, tailWord_7586248, baseEnd_7586248] using wordTrace_append hprefix tailTrace_7586248
  have hstable : (prefixWord ++ tailWord_7586248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586248).length < 2 ^ (prefixWord ++ tailWord_7586248).sum := by decide
  have hdescent : baseEnd_7586248 < baseStart_7586248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586250 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_7586250 : Nat := 118140960795 + 7586250 * 2 ^ 59
def prefixEnd_7586250 : Nat := 4983230072969 + 3 ^ 40 * 7586250 * 2
def baseEnd_7586250 : Nat := 3895392615171048995686477

theorem tailTrace_7586250 : CollatzResearch.WordTrace tailWord_7586250 prefixEnd_7586250 3895392615171048995686477 := by
  unfold tailWord_7586250
  simp only [CollatzResearch.WordTrace]
  refine ⟨69173317191579838298717051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184462179177546235463245469 69173317191579838298717051)
  ·
    refine ⟨103759975787369757448075577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69173317191579838298717051 103759975787369757448075577)
    ·
      refine ⟨77819981840527318086056683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103759975787369757448075577 77819981840527318086056683)
      ·
        refine ⟨116729972760790977129085025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77819981840527318086056683 116729972760790977129085025)
        ·
          refine ⟨87547479570593232846813769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116729972760790977129085025 87547479570593232846813769)
          ·
            refine ⟨65660609677944924635110327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87547479570593232846813769 65660609677944924635110327)
            ·
              refine ⟨98490914516917386952665491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65660609677944924635110327 98490914516917386952665491)
              ·
                refine ⟨147736371775376080428998237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98490914516917386952665491 147736371775376080428998237)
                ·
                  refine ⟨55401139415766030160874339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147736371775376080428998237 55401139415766030160874339)
                  ·
                    refine ⟨83101709123649045241311509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55401139415766030160874339 83101709123649045241311509)
                    ·
                      refine ⟨3895392615171048995686477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83101709123649045241311509 3895392615171048995686477)
                      ·
                        rfl

theorem cell23_7586250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_7586250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586250 prefixEnd_7586250 := by exact prefixLift 7586250
  have htrace : WordTrace (prefixWord ++ tailWord_7586250) baseStart_7586250 baseEnd_7586250 := by
    simpa [prefixWord, tailWord_7586250, baseEnd_7586250] using wordTrace_append hprefix tailTrace_7586250
  have hstable : (prefixWord ++ tailWord_7586250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586250).length < 2 ^ (prefixWord ++ tailWord_7586250).sum := by decide
  have hdescent : baseEnd_7586250 < baseStart_7586250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586305 : List Nat := [1, 2, 4, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_7586305 : Nat := 118140960795 + 7586305 * 2 ^ 59
def prefixEnd_7586305 : Nat := 4983230072969 + 3 ^ 40 * 7586305 * 2
def baseEnd_7586305 : Nat := 3895420856607046280498725

theorem tailTrace_7586305 : CollatzResearch.WordTrace tailWord_7586305 prefixEnd_7586305 3895420856607046280498725 := by
  unfold tailWord_7586305
  simp only [CollatzResearch.WordTrace]
  refine ⟨276695274781120097588120369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184463516520746731725413579 276695274781120097588120369)
  ·
    refine ⟨207521456085840073191090277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276695274781120097588120369 207521456085840073191090277)
    ·
      refine ⟨38910273016095013723329427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207521456085840073191090277 38910273016095013723329427)
      ·
        refine ⟨58365409524142520584994141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38910273016095013723329427 58365409524142520584994141)
        ·
          refine ⟨21887028571553445219372803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58365409524142520584994141 21887028571553445219372803)
          ·
            refine ⟨32830542857330167829059205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21887028571553445219372803 32830542857330167829059205)
            ·
              refine ⟨6155726785749406467948601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32830542857330167829059205 6155726785749406467948601)
              ·
                refine ⟨4616795089312054850961451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6155726785749406467948601 4616795089312054850961451)
                ·
                  refine ⟨6925192633968082276442177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4616795089312054850961451 6925192633968082276442177)
                  ·
                    refine ⟨5193894475476061707331633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6925192633968082276442177 5193894475476061707331633)
                    ·
                      refine ⟨3895420856607046280498725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193894475476061707331633 3895420856607046280498725)
                      ·
                        rfl

theorem cell23_7586305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_7586305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586305 prefixEnd_7586305 := by exact prefixLift 7586305
  have htrace : WordTrace (prefixWord ++ tailWord_7586305) baseStart_7586305 baseEnd_7586305 := by
    simpa [prefixWord, tailWord_7586305, baseEnd_7586305] using wordTrace_append hprefix tailTrace_7586305
  have hstable : (prefixWord ++ tailWord_7586305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586305).length < 2 ^ (prefixWord ++ tailWord_7586305).sum := by decide
  have hdescent : baseEnd_7586305 < baseStart_7586305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586314 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_7586314 : Nat := 118140960795 + 7586314 * 2 ^ 59
def prefixEnd_7586314 : Nat := 4983230072969 + 3 ^ 40 * 7586314 * 2
def baseEnd_7586314 : Nat := 3895425477932936745286183

theorem tailTrace_7586314 : CollatzResearch.WordTrace tailWord_7586314 prefixEnd_7586314 3895425477932936745286183 := by
  unfold tailWord_7586314
  simp only [CollatzResearch.WordTrace]
  refine ⟨69173900759521873031299499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184463735358724994750131997 69173900759521873031299499)
  ·
    refine ⟨103760851139282809546949249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69173900759521873031299499 103760851139282809546949249)
    ·
      refine ⟨77820638354462107160211937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103760851139282809546949249 77820638354462107160211937)
      ·
        refine ⟨58365478765846580370158953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77820638354462107160211937 58365478765846580370158953)
        ·
          refine ⟨43774109074384935277619215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58365478765846580370158953 43774109074384935277619215)
          ·
            refine ⟨65661163611577402916428823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43774109074384935277619215 65661163611577402916428823)
            ·
              refine ⟨98491745417366104374643235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65661163611577402916428823 98491745417366104374643235)
              ·
                refine ⟨147737618126049156561964853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98491745417366104374643235 147737618126049156561964853)
                ·
                  refine ⟨13850401699317108427684205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147737618126049156561964853 13850401699317108427684205)
                  ·
                    refine ⟨5193900637243915660381577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13850401699317108427684205 5193900637243915660381577)
                    ·
                      refine ⟨3895425477932936745286183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193900637243915660381577 3895425477932936745286183)
                      ·
                        rfl

theorem cell23_7586314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_7586314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586314 prefixEnd_7586314 := by exact prefixLift 7586314
  have htrace : WordTrace (prefixWord ++ tailWord_7586314) baseStart_7586314 baseEnd_7586314 := by
    simpa [prefixWord, tailWord_7586314, baseEnd_7586314] using wordTrace_append hprefix tailTrace_7586314
  have hstable : (prefixWord ++ tailWord_7586314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586314).length < 2 ^ (prefixWord ++ tailWord_7586314).sum := by decide
  have hdescent : baseEnd_7586314 < baseStart_7586314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586357 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_7586357 : Nat := 118140960795 + 7586357 * 2 ^ 59
def prefixEnd_7586357 : Nat := 4983230072969 + 3 ^ 40 * 7586357 * 2
def baseEnd_7586357 : Nat := 3895447557601080077048485

theorem tailTrace_7586357 : CollatzResearch.WordTrace tailWord_7586357 prefixEnd_7586357 3895447557601080077048485 := by
  unfold tailWord_7586357
  simp only [CollatzResearch.WordTrace]
  refine ⟨276697171376931710469013325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184464780917954473646008883 276697171376931710469013325)
  ·
    refine ⟨103761439266349391425879997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276697171376931710469013325 103761439266349391425879997)
    ·
      refine ⟨38910539724881021784704999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103761439266349391425879997 38910539724881021784704999)
      ·
        refine ⟨58365809587321532677057499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38910539724881021784704999 58365809587321532677057499)
        ·
          refine ⟨87548714380982299015586249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58365809587321532677057499 87548714380982299015586249)
          ·
            refine ⟨65661535785736724261689687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87548714380982299015586249 65661535785736724261689687)
            ·
              refine ⟨98492303678605086392534531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65661535785736724261689687 98492303678605086392534531)
              ·
                refine ⟨147738455517907629588801797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98492303678605086392534531 147738455517907629588801797)
                ·
                  refine ⟨27700960409607680547900337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147738455517907629588801797 27700960409607680547900337)
                  ·
                    refine ⟨20775720307205760410925253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27700960409607680547900337 20775720307205760410925253)
                    ·
                      refine ⟨3895447557601080077048485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20775720307205760410925253 3895447557601080077048485)
                      ·
                        rfl

theorem cell23_7586357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_7586357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586357 prefixEnd_7586357 := by exact prefixLift 7586357
  have htrace : WordTrace (prefixWord ++ tailWord_7586357) baseStart_7586357 baseEnd_7586357 := by
    simpa [prefixWord, tailWord_7586357, baseEnd_7586357] using wordTrace_append hprefix tailTrace_7586357
  have hstable : (prefixWord ++ tailWord_7586357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586357).length < 2 ^ (prefixWord ++ tailWord_7586357).sum := by decide
  have hdescent : baseEnd_7586357 < baseStart_7586357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586361 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 4, 2, 2]
def baseStart_7586361 : Nat := 118140960795 + 7586361 * 2 ^ 59
def prefixEnd_7586361 : Nat := 4983230072969 + 3 ^ 40 * 7586361 * 2
def baseEnd_7586361 : Nat := 3895449611523698061398467

theorem tailTrace_7586361 : CollatzResearch.WordTrace tailWord_7586361 prefixEnd_7586361 3895449611523698061398467 := by
  unfold tailWord_7586361
  simp only [CollatzResearch.WordTrace]
  refine ⟨276697317268917219152158937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184464878179278146101439291 276697317268917219152158937)
  ·
    refine ⟨207522987951687914364119203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276697317268917219152158937 207522987951687914364119203)
    ·
      refine ⟨311284481927531871546178805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207522987951687914364119203 311284481927531871546178805)
      ·
        refine ⟨29182920180706112957454263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311284481927531871546178805 29182920180706112957454263)
        ·
          refine ⟨43774380271059169436181395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29182920180706112957454263 43774380271059169436181395)
          ·
            refine ⟨65661570406588754154272093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43774380271059169436181395 65661570406588754154272093)
            ·
              refine ⟨24623088902470782807852035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65661570406588754154272093 24623088902470782807852035)
              ·
                refine ⟨36934633353706174211778053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24623088902470782807852035 36934633353706174211778053)
                ·
                  refine ⟨6925243753819907664708385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36934633353706174211778053 6925243753819907664708385)
                  ·
                    refine ⟨5193932815364930748531289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6925243753819907664708385 5193932815364930748531289)
                    ·
                      refine ⟨3895449611523698061398467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5193932815364930748531289 3895449611523698061398467)
                      ·
                        rfl

theorem cell23_7586361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_7586361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586361 prefixEnd_7586361 := by exact prefixLift 7586361
  have htrace : WordTrace (prefixWord ++ tailWord_7586361) baseStart_7586361 baseEnd_7586361 := by
    simpa [prefixWord, tailWord_7586361, baseEnd_7586361] using wordTrace_append hprefix tailTrace_7586361
  have hstable : (prefixWord ++ tailWord_7586361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586361).length < 2 ^ (prefixWord ++ tailWord_7586361).sum := by decide
  have hdescent : baseEnd_7586361 < baseStart_7586361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586367 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 7]
def baseStart_7586367 : Nat := 118140960795 + 7586367 * 2 ^ 59
def prefixEnd_7586367 : Nat := 4983230072969 + 3 ^ 40 * 7586367 * 2
def baseEnd_7586367 : Nat := 432828076934180559769271

theorem tailTrace_7586367 : CollatzResearch.WordTrace tailWord_7586367 prefixEnd_7586367 432828076934180559769271 := by
  unfold tailWord_7586367
  simp only [CollatzResearch.WordTrace]
  refine ⟨276697536106895482176877355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184465024071263654784584903 276697536106895482176877355)
  ·
    refine ⟨415046304160343223265316033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276697536106895482176877355 415046304160343223265316033)
    ·
      refine ⟨311284728120257417448987025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415046304160343223265316033 311284728120257417448987025)
      ·
        refine ⟨233463546090193063086740269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311284728120257417448987025 233463546090193063086740269)
        ·
          refine ⟨87548829783822398657527601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233463546090193063086740269 87548829783822398657527601)
          ·
            refine ⟨65661622337866798993145701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87548829783822398657527601 65661622337866798993145701)
            ·
              refine ⟨12311554188350024811214819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65661622337866798993145701 12311554188350024811214819)
              ·
                refine ⟨18467331282525037216822229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12311554188350024811214819 18467331282525037216822229)
                ·
                  refine ⟨432828076934180559769271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18467331282525037216822229 432828076934180559769271)
                  ·
                    rfl

theorem cell23_7586367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 7].length) (baseStart_7586367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586367 prefixEnd_7586367 := by exact prefixLift 7586367
  have htrace : WordTrace (prefixWord ++ tailWord_7586367) baseStart_7586367 baseEnd_7586367 := by
    simpa [prefixWord, tailWord_7586367, baseEnd_7586367] using wordTrace_append hprefix tailTrace_7586367
  have hstable : (prefixWord ++ tailWord_7586367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586367).length < 2 ^ (prefixWord ++ tailWord_7586367).sum := by decide
  have hdescent : baseEnd_7586367 < baseStart_7586367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586372 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7586372 : Nat := 118140960795 + 7586372 * 2 ^ 59
def prefixEnd_7586372 : Nat := 4983230072969 + 3 ^ 40 * 7586372 * 2
def baseEnd_7586372 : Nat := 3895455259810897518360917

theorem tailTrace_7586372 : CollatzResearch.WordTrace tailWord_7586372 prefixEnd_7586372 3895455259810897518360917 := by
  unfold tailWord_7586372
  simp only [CollatzResearch.WordTrace]
  refine ⟨138348859235938684015404685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184465145647918245353872913 138348859235938684015404685)
  ·
    refine ⟨51880822213477006505776757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138348859235938684015404685 51880822213477006505776757)
    ·
      refine ⟨4863827082513469359916571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51880822213477006505776757 4863827082513469359916571)
      ·
        refine ⟨7295740623770204039874857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863827082513469359916571 7295740623770204039874857)
        ·
          refine ⟨5471805467827653029906143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7295740623770204039874857 5471805467827653029906143)
          ·
            refine ⟨8207708201741479544859215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471805467827653029906143 8207708201741479544859215)
            ·
              refine ⟨12311562302612219317288823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207708201741479544859215 12311562302612219317288823)
              ·
                refine ⟨18467343453918328975933235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12311562302612219317288823 18467343453918328975933235)
                ·
                  refine ⟨27701015180877493463899853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18467343453918328975933235 27701015180877493463899853)
                  ·
                    refine ⟨10387880692829060048962445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27701015180877493463899853 10387880692829060048962445)
                    ·
                      refine ⟨3895455259810897518360917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10387880692829060048962445 3895455259810897518360917)
                      ·
                        rfl

theorem cell23_7586372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7586372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586372 prefixEnd_7586372 := by exact prefixLift 7586372
  have htrace : WordTrace (prefixWord ++ tailWord_7586372) baseStart_7586372 baseEnd_7586372 := by
    simpa [prefixWord, tailWord_7586372, baseEnd_7586372] using wordTrace_append hprefix tailTrace_7586372
  have hstable : (prefixWord ++ tailWord_7586372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586372).length < 2 ^ (prefixWord ++ tailWord_7586372).sum := by decide
  have hdescent : baseEnd_7586372 < baseStart_7586372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586401 : List Nat := [1, 2, 3, 1, 1, 6, 1, 3, 5]
def baseStart_7586401 : Nat := 118140960795 + 7586401 * 2 ^ 59
def prefixEnd_7586401 : Nat := 4983230072969 + 3 ^ 40 * 7586401 * 2
def baseEnd_7586401 : Nat := 432830016749986433877587

theorem tailTrace_7586401 : CollatzResearch.WordTrace tailWord_7586401 prefixEnd_7586401 432830016749986433877587 := by
  unfold tailWord_7586401
  simp only [CollatzResearch.WordTrace]
  refine ⟨276698776188772305983615057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184465850792514870655743371 276698776188772305983615057)
  ·
    refine ⟨207524082141579229487711293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276698776188772305983615057 207524082141579229487711293)
    ·
      refine ⟨77821530803092211057891735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207524082141579229487711293 77821530803092211057891735)
      ·
        refine ⟨116732296204638316586837603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77821530803092211057891735 116732296204638316586837603)
        ·
          refine ⟨175098444306957474880256405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116732296204638316586837603 175098444306957474880256405)
          ·
            refine ⟨8207739576888631635012019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175098444306957474880256405 8207739576888631635012019)
            ·
              refine ⟨12311609365332947452518029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207739576888631635012019 12311609365332947452518029)
              ·
                refine ⟨4616853511999855294694261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12311609365332947452518029 4616853511999855294694261)
                ·
                  refine ⟨432830016749986433877587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4616853511999855294694261 432830016749986433877587)
                  ·
                    rfl

theorem cell23_7586401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 5].length) (baseStart_7586401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586401 prefixEnd_7586401 := by exact prefixLift 7586401
  have htrace : WordTrace (prefixWord ++ tailWord_7586401) baseStart_7586401 baseEnd_7586401 := by
    simpa [prefixWord, tailWord_7586401, baseEnd_7586401] using wordTrace_append hprefix tailTrace_7586401
  have hstable : (prefixWord ++ tailWord_7586401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586401).length < 2 ^ (prefixWord ++ tailWord_7586401).sum := by decide
  have hdescent : baseEnd_7586401 < baseStart_7586401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586407 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_7586407 : Nat := 118140960795 + 7586407 * 2 ^ 59
def prefixEnd_7586407 : Nat := 4983230072969 + 3 ^ 40 * 7586407 * 2
def baseEnd_7586407 : Nat := 3895473231633804881423255

theorem tailTrace_7586407 : CollatzResearch.WordTrace tailWord_7586407 prefixEnd_7586407 3895473231633804881423255 := by
  unfold tailWord_7586407
  simp only [CollatzResearch.WordTrace]
  refine ⟨276698995026750569008333475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184465996684500379338888983 276698995026750569008333475)
  ·
    refine ⟨415048492540125853512500213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276698995026750569008333475 415048492540125853512500213)
    ·
      refine ⟨38910796175636798766796895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 415048492540125853512500213 38910796175636798766796895)
      ·
        refine ⟨58366194263455198150195343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38910796175636798766796895 58366194263455198150195343)
        ·
          refine ⟨87549291395182797225293015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58366194263455198150195343 87549291395182797225293015)
          ·
            refine ⟨131323937092774195837939523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87549291395182797225293015 131323937092774195837939523)
            ·
              refine ⟨196985905639161293756909285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131323937092774195837939523 196985905639161293756909285)
              ·
                refine ⟨36934857307342742579420491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196985905639161293756909285 36934857307342742579420491)
                ·
                  refine ⟨55402285961014113869130737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36934857307342742579420491 55402285961014113869130737)
                  ·
                    refine ⟨41551714470760585401848053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55402285961014113869130737 41551714470760585401848053)
                    ·
                      refine ⟨3895473231633804881423255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41551714470760585401848053 3895473231633804881423255)
                      ·
                        rfl

theorem cell23_7586407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_7586407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586407 prefixEnd_7586407 := by exact prefixLift 7586407
  have htrace : WordTrace (prefixWord ++ tailWord_7586407) baseStart_7586407 baseEnd_7586407 := by
    simpa [prefixWord, tailWord_7586407, baseEnd_7586407] using wordTrace_append hprefix tailTrace_7586407
  have hstable : (prefixWord ++ tailWord_7586407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586407).length < 2 ^ (prefixWord ++ tailWord_7586407).sum := by decide
  have hdescent : baseEnd_7586407 < baseStart_7586407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586414 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_7586414 : Nat := 118140960795 + 7586414 * 2 ^ 59
def prefixEnd_7586414 : Nat := 4983230072969 + 3 ^ 40 * 7586414 * 2
def baseEnd_7586414 : Nat := 1298492275332795451345241

theorem tailTrace_7586414 : CollatzResearch.WordTrace tailWord_7586414 prefixEnd_7586414 1298492275332795451345241 := by
  unfold tailWord_7586414
  simp only [CollatzResearch.WordTrace]
  refine ⟨34587406292215651150479787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184466166891816806135892197 34587406292215651150479787)
  ·
    refine ⟨51881109438323476725719681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34587406292215651150479787 51881109438323476725719681)
    ·
      refine ⟨38910832078742607544289761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51881109438323476725719681 38910832078742607544289761)
      ·
        refine ⟨29183124059056955658217321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38910832078742607544289761 29183124059056955658217321)
        ·
          refine ⟨21887343044292716743662991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29183124059056955658217321 21887343044292716743662991)
          ·
            refine ⟨32831014566439075115494487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21887343044292716743662991 32831014566439075115494487)
            ·
              refine ⟨49246521849658612673241731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32831014566439075115494487 49246521849658612673241731)
              ·
                refine ⟨73869782774487919009862597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49246521849658612673241731 73869782774487919009862597)
                ·
                  refine ⟨13850584270216484814349237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73869782774487919009862597 13850584270216484814349237)
                  ·
                    refine ⟨1298492275332795451345241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13850584270216484814349237 1298492275332795451345241)
                    ·
                      rfl

theorem cell23_7586414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_7586414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586414 prefixEnd_7586414 := by exact prefixLift 7586414
  have htrace : WordTrace (prefixWord ++ tailWord_7586414) baseStart_7586414 baseEnd_7586414 := by
    simpa [prefixWord, tailWord_7586414, baseEnd_7586414] using wordTrace_append hprefix tailTrace_7586414
  have hstable : (prefixWord ++ tailWord_7586414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586414).length < 2 ^ (prefixWord ++ tailWord_7586414).sum := by decide
  have hdescent : baseEnd_7586414 < baseStart_7586414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586418 : List Nat := [3, 2, 1, 2, 4, 1, 3, 2, 5]
def baseStart_7586418 : Nat := 118140960795 + 7586418 * 2 ^ 59
def prefixEnd_7586418 : Nat := 4983230072969 + 3 ^ 40 * 7586418 * 2
def baseEnd_7586418 : Nat := 432830986657889370931745

theorem tailTrace_7586418 : CollatzResearch.WordTrace tailWord_7586418 prefixEnd_7586418 432830986657889370931745 := by
  unfold tailWord_7586418
  simp only [CollatzResearch.WordTrace]
  refine ⟨69174849057427679471745977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184466264153140478591322605 69174849057427679471745977)
  ·
    refine ⟨51881136793070759603809483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69174849057427679471745977 51881136793070759603809483)
    ·
      refine ⟨77821705189606139405714225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51881136793070759603809483 77821705189606139405714225)
      ·
        refine ⟨58366278892204604554285669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77821705189606139405714225 58366278892204604554285669)
        ·
          refine ⟨10943677292288363353928563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58366278892204604554285669 10943677292288363353928563)
          ·
            refine ⟨16415515938432545030892845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10943677292288363353928563 16415515938432545030892845)
            ·
              refine ⟨6155818476912204386584817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16415515938432545030892845 6155818476912204386584817)
              ·
                refine ⟨4616863857684153289938613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6155818476912204386584817 4616863857684153289938613)
                ·
                  refine ⟨432830986657889370931745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4616863857684153289938613 432830986657889370931745)
                  ·
                    rfl

theorem cell23_7586418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_7586418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586418 prefixEnd_7586418 := by exact prefixLift 7586418
  have htrace : WordTrace (prefixWord ++ tailWord_7586418) baseStart_7586418 baseEnd_7586418 := by
    simpa [prefixWord, tailWord_7586418, baseEnd_7586418] using wordTrace_append hprefix tailTrace_7586418
  have hstable : (prefixWord ++ tailWord_7586418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586418).length < 2 ^ (prefixWord ++ tailWord_7586418).sum := by decide
  have hdescent : baseEnd_7586418 < baseStart_7586418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586502 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_7586502 : Nat := 118140960795 + 7586502 * 2 ^ 59
def prefixEnd_7586502 : Nat := 4983230072969 + 3 ^ 40 * 7586502 * 2
def baseEnd_7586502 : Nat := 3895522012295982009735319

theorem tailTrace_7586502 : CollatzResearch.WordTrace tailWord_7586502 prefixEnd_7586502 3895522012295982009735319 := by
  unfold tailWord_7586502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8646951873793950007282555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184468306640937600155361173 8646951873793950007282555)
  ·
    refine ⟨12970427810690925010923833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8646951873793950007282555 12970427810690925010923833)
    ·
      refine ⟨9727820858018193758192875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12970427810690925010923833 9727820858018193758192875)
      ·
        refine ⟨14591731287027290637289313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9727820858018193758192875 14591731287027290637289313)
        ·
          refine ⟨10943798465270467977966985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14591731287027290637289313 10943798465270467977966985)
          ·
            refine ⟨8207848848952850983475239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10943798465270467977966985 8207848848952850983475239)
            ·
              refine ⟨12311773273429276475212859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207848848952850983475239 12311773273429276475212859)
              ·
                refine ⟨18467659910143914712819289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12311773273429276475212859 18467659910143914712819289)
                ·
                  refine ⟨13850744932607936034614467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18467659910143914712819289 13850744932607936034614467)
                  ·
                    refine ⟨20776117398911904051921701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13850744932607936034614467 20776117398911904051921701)
                    ·
                      refine ⟨3895522012295982009735319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20776117398911904051921701 3895522012295982009735319)
                      ·
                        rfl

theorem cell23_7586502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_7586502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586502 prefixEnd_7586502 := by exact prefixLift 7586502
  have htrace : WordTrace (prefixWord ++ tailWord_7586502) baseStart_7586502 baseEnd_7586502 := by
    simpa [prefixWord, tailWord_7586502, baseEnd_7586502] using wordTrace_append hprefix tailTrace_7586502
  have hstable : (prefixWord ++ tailWord_7586502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586502).length < 2 ^ (prefixWord ++ tailWord_7586502).sum := by decide
  have hdescent : baseEnd_7586502 < baseStart_7586502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586504 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 3, 5]
def baseStart_7586504 : Nat := 118140960795 + 7586504 * 2 ^ 59
def prefixEnd_7586504 : Nat := 4983230072969 + 3 ^ 40 * 7586504 * 2
def baseEnd_7586504 : Nat := 1298507679752430333970103

theorem tailTrace_7586504 : CollatzResearch.WordTrace tailWord_7586504 prefixEnd_7586504 1298507679752430333970103 := by
  unfold tailWord_7586504
  simp only [CollatzResearch.WordTrace]
  refine ⟨138351266453699577287307283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184468355271599436383076377 138351266453699577287307283)
  ·
    refine ⟨207526899680549365930960925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138351266453699577287307283 207526899680549365930960925)
    ·
      refine ⟨77822587380206012224110347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207526899680549365930960925 77822587380206012224110347)
      ·
        refine ⟨116733881070309018336165521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77822587380206012224110347 116733881070309018336165521)
        ·
          refine ⟨87550410802731763752124141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116733881070309018336165521 87550410802731763752124141)
          ·
            refine ⟨32831404051024411407046553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87550410802731763752124141 32831404051024411407046553)
            ·
              refine ⟨24623553038268308555284915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32831404051024411407046553 24623553038268308555284915)
              ·
                refine ⟨36935329557402462832927373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24623553038268308555284915 36935329557402462832927373)
                ·
                  refine ⟨13850748584025923562347765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36935329557402462832927373 13850748584025923562347765)
                  ·
                    refine ⟨1298507679752430333970103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13850748584025923562347765 1298507679752430333970103)
                    ·
                      rfl

theorem cell23_7586504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_7586504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586504 prefixEnd_7586504 := by exact prefixLift 7586504
  have htrace : WordTrace (prefixWord ++ tailWord_7586504) baseStart_7586504 baseEnd_7586504 := by
    simpa [prefixWord, tailWord_7586504, baseEnd_7586504] using wordTrace_append hprefix tailTrace_7586504
  have hstable : (prefixWord ++ tailWord_7586504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586504).length < 2 ^ (prefixWord ++ tailWord_7586504).sum := by decide
  have hdescent : baseEnd_7586504 < baseStart_7586504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586544 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_7586544 : Nat := 118140960795 + 7586544 * 2 ^ 59
def prefixEnd_7586544 : Nat := 4983230072969 + 3 ^ 40 * 7586544 * 2
def baseEnd_7586544 : Nat := 3895543578483470845410125

theorem tailTrace_7586544 : CollatzResearch.WordTrace tailWord_7586544 prefixEnd_7586544 3895543578483470845410125 := by
  unfold tailWord_7586544
  simp only [CollatzResearch.WordTrace]
  refine ⟨138351995913627120703035343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184469327884836160937380457 138351995913627120703035343)
  ·
    refine ⟨207527993870440681054553015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138351995913627120703035343 207527993870440681054553015)
    ·
      refine ⟨311291990805661021581829523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207527993870440681054553015 311291990805661021581829523)
      ·
        refine ⟨466937986208491532372744285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311291990805661021581829523 466937986208491532372744285)
        ·
          refine ⟨175101744828184324639779107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466937986208491532372744285 175101744828184324639779107)
          ·
            refine ⟨262652617242276486959668661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175101744828184324639779107 262652617242276486959668661)
            ·
              refine ⟨24623682866463420652468937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262652617242276486959668661 24623682866463420652468937)
              ·
                refine ⟨18467762149847565489351703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24623682866463420652468937 18467762149847565489351703)
                ·
                  refine ⟨27701643224771348234027555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18467762149847565489351703 27701643224771348234027555)
                  ·
                    refine ⟨41552464837157022351041333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27701643224771348234027555 41552464837157022351041333)
                    ·
                      refine ⟨3895543578483470845410125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41552464837157022351041333 3895543578483470845410125)
                      ·
                        rfl

theorem cell23_7586544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_7586544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586544 prefixEnd_7586544 := by exact prefixLift 7586544
  have htrace : WordTrace (prefixWord ++ tailWord_7586544) baseStart_7586544 baseEnd_7586544 := by
    simpa [prefixWord, tailWord_7586544, baseEnd_7586544] using wordTrace_append hprefix tailTrace_7586544
  have hstable : (prefixWord ++ tailWord_7586544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586544).length < 2 ^ (prefixWord ++ tailWord_7586544).sum := by decide
  have hdescent : baseEnd_7586544 < baseStart_7586544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586547 : List Nat := [1, 1, 1, 2, 2, 3, 1, 12]
def baseStart_7586547 : Nat := 118140960795 + 7586547 * 2 ^ 59
def prefixEnd_7586547 : Nat := 4983230072969 + 3 ^ 40 * 7586547 * 2
def baseEnd_7586547 : Nat := 144279448849090160506393

theorem tailTrace_7586547 : CollatzResearch.WordTrace tailWord_7586547 prefixEnd_7586547 144279448849090160506393 := by
  unfold tailWord_7586547
  simp only [CollatzResearch.WordTrace]
  refine ⟨276704101246243372918429895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184469400830828915278953263 276704101246243372918429895)
  ·
    refine ⟨415056151869365059377644843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276704101246243372918429895 415056151869365059377644843)
    ·
      refine ⟨622584227804047589066467265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415056151869365059377644843 622584227804047589066467265)
      ·
        refine ⟨466938170853035691799850449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622584227804047589066467265 466938170853035691799850449)
        ·
          refine ⟨350203628139776768849887837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466938170853035691799850449 350203628139776768849887837)
          ·
            refine ⟨131326360552416288318707939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350203628139776768849887837 131326360552416288318707939)
            ·
              refine ⟨196989540828624432478061909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131326360552416288318707939 196989540828624432478061909)
              ·
                refine ⟨144279448849090160506393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 196989540828624432478061909 144279448849090160506393)
                ·
                  rfl

theorem cell23_7586547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 12].length) (baseStart_7586547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586547 prefixEnd_7586547 := by exact prefixLift 7586547
  have htrace : WordTrace (prefixWord ++ tailWord_7586547) baseStart_7586547 baseEnd_7586547 := by
    simpa [prefixWord, tailWord_7586547, baseEnd_7586547] using wordTrace_append hprefix tailTrace_7586547
  have hstable : (prefixWord ++ tailWord_7586547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586547).length < 2 ^ (prefixWord ++ tailWord_7586547).sum := by decide
  have hdescent : baseEnd_7586547 < baseStart_7586547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586558 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_7586558 : Nat := 118140960795 + 7586558 * 2 ^ 59
def prefixEnd_7586558 : Nat := 4983230072969 + 3 ^ 40 * 7586558 * 2
def baseEnd_7586558 : Nat := 3895550767212633790635061

theorem tailTrace_7586558 : CollatzResearch.WordTrace tailWord_7586558 prefixEnd_7586558 3895550767212633790635061 := by
  unfold tailWord_7586558
  simp only [CollatzResearch.WordTrace]
  refine ⟨34588062806150440224635041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184469668299469014531386885 34588062806150440224635041)
  ·
    refine ⟨25941047104612830168476281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34588062806150440224635041 25941047104612830168476281)
    ·
      refine ⟨19455785328459622626357211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25941047104612830168476281 19455785328459622626357211)
      ·
        refine ⟨29183677992689433939535817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19455785328459622626357211 29183677992689433939535817)
        ·
          refine ⟨21887758494517075454651863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29183677992689433939535817 21887758494517075454651863)
          ·
            refine ⟨32831637741775613181977795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21887758494517075454651863 32831637741775613181977795)
            ·
              refine ⟨49247456612663419772966693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32831637741775613181977795 49247456612663419772966693)
              ·
                refine ⟨9233898114874391207431255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49247456612663419772966693 9233898114874391207431255)
                ·
                  refine ⟨13850847172311586811146883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9233898114874391207431255 13850847172311586811146883)
                  ·
                    refine ⟨20776270758467380216720325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13850847172311586811146883 20776270758467380216720325)
                    ·
                      refine ⟨3895550767212633790635061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20776270758467380216720325 3895550767212633790635061)
                      ·
                        rfl

theorem cell23_7586558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_7586558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586558 prefixEnd_7586558 := by exact prefixLift 7586558
  have htrace : WordTrace (prefixWord ++ tailWord_7586558) baseStart_7586558 baseEnd_7586558 := by
    simpa [prefixWord, tailWord_7586558, baseEnd_7586558] using wordTrace_append hprefix tailTrace_7586558
  have hstable : (prefixWord ++ tailWord_7586558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586558).length < 2 ^ (prefixWord ++ tailWord_7586558).sum := by decide
  have hdescent : baseEnd_7586558 < baseStart_7586558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586564 : List Nat := [2, 3, 2, 2, 1, 1, 3, 9]
def baseStart_7586564 : Nat := 118140960795 + 7586564 * 2 ^ 59
def prefixEnd_7586564 : Nat := 4983230072969 + 3 ^ 40 * 7586564 * 2
def baseEnd_7586564 : Nat := 144279772151724472857779

theorem tailTrace_7586564 : CollatzResearch.WordTrace tailWord_7586564 prefixEnd_7586564 144279772151724472857779 := by
  unfold tailWord_7586564
  simp only [CollatzResearch.WordTrace]
  refine ⟨138352360643590892410899373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184469814191454523214532497 138352360643590892410899373)
  ·
    refine ⟨51882135241346584654087265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138352360643590892410899373 51882135241346584654087265)
    ·
      refine ⟨38911601431009938490565449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51882135241346584654087265 38911601431009938490565449)
      ·
        refine ⟨29183701073257453867924087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38911601431009938490565449 29183701073257453867924087)
        ·
          refine ⟨43775551609886180801886131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29183701073257453867924087 43775551609886180801886131)
          ·
            refine ⟨65663327414829271202829197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43775551609886180801886131 65663327414829271202829197)
            ·
              refine ⟨24623747780560976701060949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65663327414829271202829197 24623747780560976701060949)
              ·
                refine ⟨144279772151724472857779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24623747780560976701060949 144279772151724472857779)
                ·
                  rfl

theorem cell23_7586564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 9].length) (baseStart_7586564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586564 prefixEnd_7586564 := by exact prefixLift 7586564
  have htrace : WordTrace (prefixWord ++ tailWord_7586564) baseStart_7586564 baseEnd_7586564 := by
    simpa [prefixWord, tailWord_7586564, baseEnd_7586564] using wordTrace_append hprefix tailTrace_7586564
  have hstable : (prefixWord ++ tailWord_7586564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586564).length < 2 ^ (prefixWord ++ tailWord_7586564).sum := by decide
  have hdescent : baseEnd_7586564 < baseStart_7586564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586601 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 5, 3, 2]
def baseStart_7586601 : Nat := 118140960795 + 7586601 * 2 ^ 59
def prefixEnd_7586601 : Nat := 4983230072969 + 3 ^ 40 * 7586601 * 2
def baseEnd_7586601 : Nat := 3895572846880777122397363

theorem tailTrace_7586601 : CollatzResearch.WordTrace tailWord_7586601 prefixEnd_7586601 3895572846880777122397363 := by
  unfold tailWord_7586601
  simp only [CollatzResearch.WordTrace]
  refine ⟨276706070788047740140895657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184470713858698493427263771 276706070788047740140895657)
  ·
    refine ⟨207529553091035805105671743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276706070788047740140895657 207529553091035805105671743)
    ·
      refine ⟨311294329636553707658507615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207529553091035805105671743 311294329636553707658507615)
      ·
        refine ⟨466941494454830561487761423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311294329636553707658507615 466941494454830561487761423)
        ·
          refine ⟨700412241682245842231642135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466941494454830561487761423 700412241682245842231642135)
          ·
            refine ⟨1050618362523368763347463203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700412241682245842231642135 1050618362523368763347463203)
            ·
              refine ⟨1575927543785053145021194805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050618362523368763347463203 1575927543785053145021194805)
              ·
                refine ⟨147743207229848732345737013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1575927543785053145021194805 147743207229848732345737013)
                ·
                  refine ⟨13850925677798318657412845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147743207229848732345737013 13850925677798318657412845)
                  ·
                    refine ⟨5194097129174369496529817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13850925677798318657412845 5194097129174369496529817)
                    ·
                      refine ⟨3895572846880777122397363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194097129174369496529817 3895572846880777122397363)
                      ·
                        rfl

theorem cell23_7586601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 3, 2].length) (baseStart_7586601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586601 prefixEnd_7586601 := by exact prefixLift 7586601
  have htrace : WordTrace (prefixWord ++ tailWord_7586601) baseStart_7586601 baseEnd_7586601 := by
    simpa [prefixWord, tailWord_7586601, baseEnd_7586601] using wordTrace_append hprefix tailTrace_7586601
  have hstable : (prefixWord ++ tailWord_7586601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586601).length < 2 ^ (prefixWord ++ tailWord_7586601).sum := by decide
  have hdescent : baseEnd_7586601 < baseStart_7586601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586612 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_7586612 : Nat := 118140960795 + 7586612 * 2 ^ 59
def prefixEnd_7586612 : Nat := 4983230072969 + 3 ^ 40 * 7586612 * 2
def baseEnd_7586612 : Nat := 3895578495167976579359813

theorem tailTrace_7586612 : CollatzResearch.WordTrace tailWord_7586612 prefixEnd_7586612 3895578495167976579359813 := by
  unfold tailWord_7586612
  simp only [CollatzResearch.WordTrace]
  refine ⟨138353235995503944509773045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184470981327338592679697393 138353235995503944509773045)
  ·
    refine ⟨12970615874578494797791223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138353235995503944509773045 12970615874578494797791223)
    ·
      refine ⟨19455923811867742196686835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12970615874578494797791223 19455923811867742196686835)
      ·
        refine ⟨29183885717801613295030253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19455923811867742196686835 29183885717801613295030253)
        ·
          refine ⟨10943957144175604985636345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29183885717801613295030253 10943957144175604985636345)
          ·
            refine ⟨8207967858131703739227259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10943957144175604985636345 8207967858131703739227259)
            ·
              refine ⟨12311951787197555608840889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207967858131703739227259 12311951787197555608840889)
              ·
                refine ⟨9233963840398166706630667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12311951787197555608840889 9233963840398166706630667)
                ·
                  refine ⟨13850945760597250059946001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9233963840398166706630667 13850945760597250059946001)
                  ·
                    refine ⟨10388209320447937544959501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13850945760597250059946001 10388209320447937544959501)
                    ·
                      refine ⟨3895578495167976579359813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10388209320447937544959501 3895578495167976579359813)
                      ·
                        rfl

theorem cell23_7586612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_7586612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586612 prefixEnd_7586612 := by exact prefixLift 7586612
  have htrace : WordTrace (prefixWord ++ tailWord_7586612) baseStart_7586612 baseEnd_7586612 := by
    simpa [prefixWord, tailWord_7586612, baseEnd_7586612] using wordTrace_append hprefix tailTrace_7586612
  have hstable : (prefixWord ++ tailWord_7586612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586612).length < 2 ^ (prefixWord ++ tailWord_7586612).sum := by decide
  have hdescent : baseEnd_7586612 < baseStart_7586612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586625 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7586625 : Nat := 118140960795 + 7586625 * 2 ^ 59
def prefixEnd_7586625 : Nat := 4983230072969 + 3 ^ 40 * 7586625 * 2
def baseEnd_7586625 : Nat := 3895585170416485028497253

theorem tailTrace_7586625 : CollatzResearch.WordTrace tailWord_7586625 prefixEnd_7586625 3895585170416485028497253 := by
  unfold tailWord_7586625
  simp only [CollatzResearch.WordTrace]
  refine ⟨276706946139960792239769329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184471297426640528159846219 276706946139960792239769329)
  ·
    refine ⟨207530209604970594179826997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276706946139960792239769329 207530209604970594179826997)
    ·
      refine ⟨19455957150465993204358781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207530209604970594179826997 19455957150465993204358781)
      ·
        refine ⟨7295983931424747451634543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19455957150465993204358781 7295983931424747451634543)
        ·
          refine ⟨10943975897137121177451815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7295983931424747451634543 10943975897137121177451815)
          ·
            refine ⟨16415963845705681766177723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10943975897137121177451815 16415963845705681766177723)
            ·
              refine ⟨24623945768558522649266585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16415963845705681766177723 24623945768558522649266585)
              ·
                refine ⟨18467959326418891986949939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24623945768558522649266585 18467959326418891986949939)
                ·
                  refine ⟨27701938989628337980424909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18467959326418891986949939 27701938989628337980424909)
                  ·
                    refine ⟨10388227121110626742659341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27701938989628337980424909 10388227121110626742659341)
                    ·
                      refine ⟨3895585170416485028497253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10388227121110626742659341 3895585170416485028497253)
                      ·
                        rfl

theorem cell23_7586625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7586625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586625 prefixEnd_7586625 := by exact prefixLift 7586625
  have htrace : WordTrace (prefixWord ++ tailWord_7586625) baseStart_7586625 baseEnd_7586625 := by
    simpa [prefixWord, tailWord_7586625, baseEnd_7586625] using wordTrace_append hprefix tailTrace_7586625
  have hstable : (prefixWord ++ tailWord_7586625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586625).length < 2 ^ (prefixWord ++ tailWord_7586625).sum := by decide
  have hdescent : baseEnd_7586625 < baseStart_7586625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586634 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_7586634 : Nat := 118140960795 + 7586634 * 2 ^ 59
def prefixEnd_7586634 : Nat := 4983230072969 + 3 ^ 40 * 7586634 * 2
def baseEnd_7586634 : Nat := 3895589791742375493284711

theorem tailTrace_7586634 : CollatzResearch.WordTrace tailWord_7586634 prefixEnd_7586634 3895589791742375493284711 := by
  unfold tailWord_7586634
  simp only [CollatzResearch.WordTrace]
  refine ⟨69176818599232046694211739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184471516264618791184564637 69176818599232046694211739)
  ·
    refine ⟨103765227898848070041317609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69176818599232046694211739 103765227898848070041317609)
    ·
      refine ⟨77823920924136052530988207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103765227898848070041317609 77823920924136052530988207)
      ·
        refine ⟨116735881386204078796482311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77823920924136052530988207 116735881386204078796482311)
        ·
          refine ⟨175103822079306118194723467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116735881386204078796482311 175103822079306118194723467)
          ·
            refine ⟨262655733118959177292085201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175103822079306118194723467 262655733118959177292085201)
            ·
              refine ⟨196991799839219382969063901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262655733118959177292085201 196991799839219382969063901)
              ·
                refine ⟨73871924939707268613398963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196991799839219382969063901 73871924939707268613398963)
                ·
                  refine ⟨110807887409560902920098445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73871924939707268613398963 110807887409560902920098445)
                  ·
                    refine ⟨41552957778585338595036917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110807887409560902920098445 41552957778585338595036917)
                    ·
                      refine ⟨3895589791742375493284711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41552957778585338595036917 3895589791742375493284711)
                      ·
                        rfl

theorem cell23_7586634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_7586634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586634 prefixEnd_7586634 := by exact prefixLift 7586634
  have htrace : WordTrace (prefixWord ++ tailWord_7586634) baseStart_7586634 baseEnd_7586634 := by
    simpa [prefixWord, tailWord_7586634, baseEnd_7586634] using wordTrace_append hprefix tailTrace_7586634
  have hstable : (prefixWord ++ tailWord_7586634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586634).length < 2 ^ (prefixWord ++ tailWord_7586634).sum := by decide
  have hdescent : baseEnd_7586634 < baseStart_7586634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586648 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 4, 2, 2]
def baseStart_7586648 : Nat := 118140960795 + 7586648 * 2 ^ 59
def prefixEnd_7586648 : Nat := 4983230072969 + 3 ^ 40 * 7586648 * 2
def baseEnd_7586648 : Nat := 3895596980471538438509647

theorem tailTrace_7586648 : CollatzResearch.WordTrace tailWord_7586648 prefixEnd_7586648 3895596980471538438509647 := by
  unfold tailWord_7586648
  simp only [CollatzResearch.WordTrace]
  refine ⟨138353892509438733583928299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184471856679251644778571065 138353892509438733583928299)
  ·
    refine ⟨207530838764158100375892449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138353892509438733583928299 207530838764158100375892449)
    ·
      refine ⟨155648129073118575281919337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207530838764158100375892449 155648129073118575281919337)
      ·
        refine ⟨116736096804838931461439503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155648129073118575281919337 116736096804838931461439503)
        ·
          refine ⟨175104145207258397192159255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116736096804838931461439503 175104145207258397192159255)
          ·
            refine ⟨262656217810887595788238883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175104145207258397192159255 262656217810887595788238883)
            ·
              refine ⟨393984326716331393682358325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262656217810887595788238883 393984326716331393682358325)
              ·
                refine ⟨36936030629656068157721093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 393984326716331393682358325 36936030629656068157721093)
                ·
                  refine ⟨6925505743060512779572705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36936030629656068157721093 6925505743060512779572705)
                  ·
                    refine ⟨5194129307295384584679529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6925505743060512779572705 5194129307295384584679529)
                    ·
                      refine ⟨3895596980471538438509647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194129307295384584679529 3895596980471538438509647)
                      ·
                        rfl

theorem cell23_7586648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_7586648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586648 prefixEnd_7586648 := by exact prefixLift 7586648
  have htrace : WordTrace (prefixWord ++ tailWord_7586648) baseStart_7586648 baseEnd_7586648 := by
    simpa [prefixWord, tailWord_7586648, baseEnd_7586648] using wordTrace_append hprefix tailTrace_7586648
  have hstable : (prefixWord ++ tailWord_7586648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586648).length < 2 ^ (prefixWord ++ tailWord_7586648).sum := by decide
  have hdescent : baseEnd_7586648 < baseStart_7586648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586658 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_7586658 : Nat := 118140960795 + 7586658 * 2 ^ 59
def prefixEnd_7586658 : Nat := 4983230072969 + 3 ^ 40 * 7586658 * 2
def baseEnd_7586658 : Nat := 1298534038426027799794867

theorem tailTrace_7586658 : CollatzResearch.WordTrace tailWord_7586658 prefixEnd_7586658 1298534038426027799794867 := by
  unfold tailWord_7586658
  simp only [CollatzResearch.WordTrace]
  refine ⟨69177037437210309718930157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184472099832560825917147085 69177037437210309718930157)
  ·
    refine ⟨25941389038953866144598809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69177037437210309718930157 25941389038953866144598809)
    ·
      refine ⟨19456041779215399608449107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25941389038953866144598809 19456041779215399608449107)
      ·
        refine ⟨29184062668823099412673661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19456041779215399608449107 29184062668823099412673661)
        ·
          refine ⟨10944023500808662279752623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29184062668823099412673661 10944023500808662279752623)
          ·
            refine ⟨16416035251212993419628935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10944023500808662279752623 16416035251212993419628935)
            ·
              refine ⟨24624052876819490129443403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16416035251212993419628935 24624052876819490129443403)
              ·
                refine ⟨36936079315229235194165105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24624052876819490129443403 36936079315229235194165105)
                ·
                  refine ⟨27702059486421926395623829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36936079315229235194165105 27702059486421926395623829)
                  ·
                    refine ⟨1298534038426027799794867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27702059486421926395623829 1298534038426027799794867)
                    ·
                      rfl

theorem cell23_7586658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_7586658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586658 prefixEnd_7586658 := by exact prefixLift 7586658
  have htrace : WordTrace (prefixWord ++ tailWord_7586658) baseStart_7586658 baseEnd_7586658 := by
    simpa [prefixWord, tailWord_7586658, baseEnd_7586658] using wordTrace_append hprefix tailTrace_7586658
  have hstable : (prefixWord ++ tailWord_7586658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586658).length < 2 ^ (prefixWord ++ tailWord_7586658).sum := by decide
  have hdescent : baseEnd_7586658 < baseStart_7586658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586686 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7586686 : Nat := 118140960795 + 7586686 * 2 ^ 59
def prefixEnd_7586686 : Nat := 4983230072969 + 3 ^ 40 * 7586686 * 2
def baseEnd_7586686 : Nat := 3895616492736409289834473

theorem tailTrace_7586686 : CollatzResearch.WordTrace tailWord_7586686 prefixEnd_7586686 3895616492736409289834473 := by
  unfold tailWord_7586686
  simp only [CollatzResearch.WordTrace]
  refine ⟨34588646374092474957217489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184472780661826533105159941 34588646374092474957217489)
  ·
    refine ⟨25941484780569356217913117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34588646374092474957217489 25941484780569356217913117)
    ·
      refine ⟨9728056792713508581717419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25941484780569356217913117 9728056792713508581717419)
      ·
        refine ⟨14592085189070262872576129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9728056792713508581717419 14592085189070262872576129)
        ·
          refine ⟨10944063891802697154432097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14592085189070262872576129 10944063891802697154432097)
          ·
            refine ⟨8208047918852022865824073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10944063891802697154432097 8208047918852022865824073)
            ·
              refine ⟨6156035939139017149368055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8208047918852022865824073 6156035939139017149368055)
              ·
                refine ⟨9234053908708525724052083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156035939139017149368055 9234053908708525724052083)
                ·
                  refine ⟨13851080863062788586078125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9234053908708525724052083 13851080863062788586078125)
                  ·
                    refine ⟨5194155323648545719779297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13851080863062788586078125 5194155323648545719779297)
                    ·
                      refine ⟨3895616492736409289834473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194155323648545719779297 3895616492736409289834473)
                      ·
                        rfl

theorem cell23_7586686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7586686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586686 prefixEnd_7586686 := by exact prefixLift 7586686
  have htrace : WordTrace (prefixWord ++ tailWord_7586686) baseStart_7586686 baseEnd_7586686 := by
    simpa [prefixWord, tailWord_7586686, baseEnd_7586686] using wordTrace_append hprefix tailTrace_7586686
  have hstable : (prefixWord ++ tailWord_7586686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586686).length < 2 ^ (prefixWord ++ tailWord_7586686).sum := by decide
  have hdescent : baseEnd_7586686 < baseStart_7586686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586698 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_7586698 : Nat := 118140960795 + 7586698 * 2 ^ 59
def prefixEnd_7586698 : Nat := 4983230072969 + 3 ^ 40 * 7586698 * 2
def baseEnd_7586698 : Nat := 3895622654504263242884417

theorem tailTrace_7586698 : CollatzResearch.WordTrace tailWord_7586698 prefixEnd_7586698 3895622654504263242884417 := by
  unfold tailWord_7586698
  simp only [CollatzResearch.WordTrace]
  refine ⟨69177402167174081426794187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184473072445797550471451165 69177402167174081426794187)
  ·
    refine ⟨103766103250761122140191281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69177402167174081426794187 103766103250761122140191281)
    ·
      refine ⟨77824577438070841605143461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103766103250761122140191281 77824577438070841605143461)
      ·
        refine ⟨14592108269638282800964399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77824577438070841605143461 14592108269638282800964399)
        ·
          refine ⟨21888162404457424201446599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14592108269638282800964399 21888162404457424201446599)
          ·
            refine ⟨32832243606686136302169899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21888162404457424201446599 32832243606686136302169899)
            ·
              refine ⟨49248365410029204453254849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32832243606686136302169899 49248365410029204453254849)
              ·
                refine ⟨36936274057521903339941137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49248365410029204453254849 36936274057521903339941137)
                ·
                  refine ⟨27702205543141427504955853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36936274057521903339941137 27702205543141427504955853)
                  ·
                    refine ⟨10388327078678035314358445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27702205543141427504955853 10388327078678035314358445)
                    ·
                      refine ⟨3895622654504263242884417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10388327078678035314358445 3895622654504263242884417)
                      ·
                        rfl

theorem cell23_7586698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_7586698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586698 prefixEnd_7586698 := by exact prefixLift 7586698
  have htrace : WordTrace (prefixWord ++ tailWord_7586698) baseStart_7586698 baseEnd_7586698 := by
    simpa [prefixWord, tailWord_7586698, baseEnd_7586698] using wordTrace_append hprefix tailTrace_7586698
  have hstable : (prefixWord ++ tailWord_7586698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586698).length < 2 ^ (prefixWord ++ tailWord_7586698).sum := by decide
  have hdescent : baseEnd_7586698 < baseStart_7586698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586778 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 6]
def baseStart_7586778 : Nat := 118140960795 + 7586778 * 2 ^ 59
def prefixEnd_7586778 : Nat := 4983230072969 + 3 ^ 40 * 7586778 * 2
def baseEnd_7586778 : Nat := 432851525884069214431561

theorem tailTrace_7586778 : CollatzResearch.WordTrace tailWord_7586778 prefixEnd_7586778 432851525884069214431561 := by
  unfold tailWord_7586778
  simp only [CollatzResearch.WordTrace]
  refine ⟨69178131627101624842522247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184475017672270999580059325 69178131627101624842522247)
  ·
    refine ⟨103767197440652437263783371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69178131627101624842522247 103767197440652437263783371)
    ·
      refine ⟨155650796160978655895675057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103767197440652437263783371 155650796160978655895675057)
      ·
        refine ⟨116738097120733991921756293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155650796160978655895675057 116738097120733991921756293)
        ·
          refine ⟨21888393210137623485329305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116738097120733991921756293 21888393210137623485329305)
          ·
            refine ⟨16416294907603217613996979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21888393210137623485329305 16416294907603217613996979)
            ·
              refine ⟨24624442361404826420995469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16416294907603217613996979 24624442361404826420995469)
              ·
                refine ⟨9234165885526809907873301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24624442361404826420995469 9234165885526809907873301)
                ·
                  refine ⟨432851525884069214431561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9234165885526809907873301 432851525884069214431561)
                  ·
                    rfl

theorem cell23_7586778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_7586778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586778 prefixEnd_7586778 := by exact prefixLift 7586778
  have htrace : WordTrace (prefixWord ++ tailWord_7586778) baseStart_7586778 baseEnd_7586778 := by
    simpa [prefixWord, tailWord_7586778, baseEnd_7586778] using wordTrace_append hprefix tailTrace_7586778
  have hstable : (prefixWord ++ tailWord_7586778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586778).length < 2 ^ (prefixWord ++ tailWord_7586778).sum := by decide
  have hdescent : baseEnd_7586778 < baseStart_7586778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586821 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_7586821 : Nat := 118140960795 + 7586821 * 2 ^ 59
def prefixEnd_7586821 : Nat := 4983230072969 + 3 ^ 40 * 7586821 * 2
def baseEnd_7586821 : Nat := 1298561937541588753882117

theorem tailTrace_7586821 : CollatzResearch.WordTrace tailWord_7586821 prefixEnd_7586821 1298561937541588753882117 := by
  unfold tailWord_7586821
  simp only [CollatzResearch.WordTrace]
  refine ⟨276714094847250717713904317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184476063231500478475936211 276714094847250717713904317)
  ·
    refine ⟨103767785567719019142714119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276714094847250717713904317 103767785567719019142714119)
    ·
      refine ⟨155651678351578528714071179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103767785567719019142714119 155651678351578528714071179)
      ·
        refine ⟨233477517527367793071106769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155651678351578528714071179 233477517527367793071106769)
        ·
          refine ⟨175108138145525844803330077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233477517527367793071106769 175108138145525844803330077)
          ·
            refine ⟨65665551804572191801248779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175108138145525844803330077 65665551804572191801248779)
            ·
              refine ⟨98498327706858287701873169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65665551804572191801248779 98498327706858287701873169)
              ·
                refine ⟨73873745780143715776404877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98498327706858287701873169 73873745780143715776404877)
                ·
                  refine ⟨27702654667553893416151829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73873745780143715776404877 27702654667553893416151829)
                  ·
                    refine ⟨1298561937541588753882117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27702654667553893416151829 1298561937541588753882117)
                    ·
                      rfl

theorem cell23_7586821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_7586821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586821 prefixEnd_7586821 := by exact prefixLift 7586821
  have htrace : WordTrace (prefixWord ++ tailWord_7586821) baseStart_7586821 baseEnd_7586821 := by
    simpa [prefixWord, tailWord_7586821, baseEnd_7586821] using wordTrace_append hprefix tailTrace_7586821
  have hstable : (prefixWord ++ tailWord_7586821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586821).length < 2 ^ (prefixWord ++ tailWord_7586821).sum := by decide
  have hdescent : baseEnd_7586821 < baseStart_7586821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586828 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_7586828 : Nat := 118140960795 + 7586828 * 2 ^ 59
def prefixEnd_7586828 : Nat := 4983230072969 + 3 ^ 40 * 7586828 * 2
def baseEnd_7586828 : Nat := 3895689406989347734258819

theorem tailTrace_7586828 : CollatzResearch.WordTrace tailWord_7586828 prefixEnd_7586828 3895689406989347734258819 := by
  unfold tailWord_7586828
  simp only [CollatzResearch.WordTrace]
  refine ⟨138357175079112678954704569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184476233438816905272939425 138357175079112678954704569)
  ·
    refine ⟨103767881309334509216028427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138357175079112678954704569 103767881309334509216028427)
    ·
      refine ⟨155651821964001763824042641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103767881309334509216028427 155651821964001763824042641)
      ·
        refine ⟨116738866473001322868031981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155651821964001763824042641 116738866473001322868031981)
        ·
          refine ⟨43777074927375496075511993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116738866473001322868031981 43777074927375496075511993)
          ·
            refine ⟨32832806195531622056633995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43777074927375496075511993 32832806195531622056633995)
            ·
              refine ⟨49249209293297433084950993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32832806195531622056633995 49249209293297433084950993)
              ·
                refine ⟨36936906969973074813713245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49249209293297433084950993 36936906969973074813713245)
                ·
                  refine ⟨13851340113739903055142467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36936906969973074813713245 13851340113739903055142467)
                  ·
                    refine ⟨20777010170609854582713701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13851340113739903055142467 20777010170609854582713701)
                    ·
                      refine ⟨3895689406989347734258819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20777010170609854582713701 3895689406989347734258819)
                      ·
                        rfl

theorem cell23_7586828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_7586828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586828 prefixEnd_7586828 := by exact prefixLift 7586828
  have htrace : WordTrace (prefixWord ++ tailWord_7586828) baseStart_7586828 baseEnd_7586828 := by
    simpa [prefixWord, tailWord_7586828, baseEnd_7586828] using wordTrace_append hprefix tailTrace_7586828
  have hstable : (prefixWord ++ tailWord_7586828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586828).length < 2 ^ (prefixWord ++ tailWord_7586828).sum := by decide
  have hdescent : baseEnd_7586828 < baseStart_7586828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586841 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_7586841 : Nat := 118140960795 + 7586841 * 2 ^ 59
def prefixEnd_7586841 : Nat := 4983230072969 + 3 ^ 40 * 7586841 * 2
def baseEnd_7586841 : Nat := 3895696082237856183396259

theorem tailTrace_7586841 : CollatzResearch.WordTrace tailWord_7586841 prefixEnd_7586841 3895696082237856183396259 := by
  unfold tailWord_7586841
  simp only [CollatzResearch.WordTrace]
  refine ⟨276714824307178261129632377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184476549538118840753088251 276714824307178261129632377)
  ·
    refine ⟨207536118230383695847224283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276714824307178261129632377 207536118230383695847224283)
    ·
      refine ⟨311304177345575543770836425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207536118230383695847224283 311304177345575543770836425)
      ·
        refine ⟨233478133009181657828127319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311304177345575543770836425 233478133009181657828127319)
        ·
          refine ⟨350217199513772486742190979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233478133009181657828127319 350217199513772486742190979)
          ·
            refine ⟨525325799270658730113286469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350217199513772486742190979 525325799270658730113286469)
            ·
              refine ⟨98498587363248511896241213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 525325799270658730113286469 98498587363248511896241213)
              ·
                refine ⟨36936970261218191961090455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98498587363248511896241213 36936970261218191961090455)
                ·
                  refine ⟨55405455391827287941635683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36936970261218191961090455 55405455391827287941635683)
                  ·
                    refine ⟨83108183087740931912453525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55405455391827287941635683 83108183087740931912453525)
                    ·
                      refine ⟨3895696082237856183396259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83108183087740931912453525 3895696082237856183396259)
                      ·
                        rfl

theorem cell23_7586841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_7586841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586841 prefixEnd_7586841 := by exact prefixLift 7586841
  have htrace : WordTrace (prefixWord ++ tailWord_7586841) baseStart_7586841 baseEnd_7586841 := by
    simpa [prefixWord, tailWord_7586841, baseEnd_7586841] using wordTrace_append hprefix tailTrace_7586841
  have hstable : (prefixWord ++ tailWord_7586841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586841).length < 2 ^ (prefixWord ++ tailWord_7586841).sum := by decide
  have hdescent : baseEnd_7586841 < baseStart_7586841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586855 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 1, 6]
def baseStart_7586855 : Nat := 118140960795 + 7586855 * 2 ^ 59
def prefixEnd_7586855 : Nat := 4983230072969 + 3 ^ 40 * 7586855 * 2
def baseEnd_7586855 : Nat := 1298567756989006376207065

theorem tailTrace_7586855 : CollatzResearch.WordTrace tailWord_7586855 prefixEnd_7586855 1298567756989006376207065 := by
  unfold tailWord_7586855
  simp only [CollatzResearch.WordTrace]
  refine ⟨276715334929127541520642019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184476889952751694347094679 276715334929127541520642019)
  ·
    refine ⟨415073002393691312280963029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276715334929127541520642019 415073002393691312280963029)
    ·
      refine ⟨9728273493602140131585071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 415073002393691312280963029 9728273493602140131585071)
      ·
        refine ⟨14592410240403210197377607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9728273493602140131585071 14592410240403210197377607)
        ·
          refine ⟨21888615360604815296066411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14592410240403210197377607 21888615360604815296066411)
          ·
            refine ⟨32832923040907222944099617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21888615360604815296066411 32832923040907222944099617)
            ·
              refine ⟨24624692280680417208074713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32832923040907222944099617 24624692280680417208074713)
              ·
                refine ⟨18468519210510312906056035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24624692280680417208074713 18468519210510312906056035)
                ·
                  refine ⟨27702778815765469359084053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18468519210510312906056035 27702778815765469359084053)
                  ·
                    refine ⟨1298567756989006376207065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27702778815765469359084053 1298567756989006376207065)
                    ·
                      rfl

theorem cell23_7586855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_7586855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586855 prefixEnd_7586855 := by exact prefixLift 7586855
  have htrace : WordTrace (prefixWord ++ tailWord_7586855) baseStart_7586855 baseEnd_7586855 := by
    simpa [prefixWord, tailWord_7586855, baseEnd_7586855] using wordTrace_append hprefix tailTrace_7586855
  have hstable : (prefixWord ++ tailWord_7586855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586855).length < 2 ^ (prefixWord ++ tailWord_7586855).sum := by decide
  have hdescent : baseEnd_7586855 < baseStart_7586855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586862 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_7586862 : Nat := 118140960795 + 7586862 * 2 ^ 59
def prefixEnd_7586862 : Nat := 4983230072969 + 3 ^ 40 * 7586862 * 2
def baseEnd_7586862 : Nat := 3895706865331600601233663

theorem tailTrace_7586862 : CollatzResearch.WordTrace tailWord_7586862 prefixEnd_7586862 3895706865331600601233663 := by
  unfold tailWord_7586862
  simp only [CollatzResearch.WordTrace]
  refine ⟨34589448780012772714518355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184477060160068121144097893 34589448780012772714518355)
  ·
    refine ⟨51884173170019159071777533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34589448780012772714518355 51884173170019159071777533)
    ·
      refine ⟨19456564938757184651916575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51884173170019159071777533 19456564938757184651916575)
      ·
        refine ⟨29184847408135776977874863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19456564938757184651916575 29184847408135776977874863)
        ·
          refine ⟨43777271112203665466812295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29184847408135776977874863 43777271112203665466812295)
          ·
            refine ⟨65665906668305498200218443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43777271112203665466812295 65665906668305498200218443)
            ·
              refine ⟨98498860002458247300327665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65665906668305498200218443 98498860002458247300327665)
              ·
                refine ⟨73874145001843685475245749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98498860002458247300327665 73874145001843685475245749)
                ·
                  refine ⟨6925701093922845513304289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73874145001843685475245749 6925701093922845513304289)
                  ·
                    refine ⟨5194275820442134134978217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6925701093922845513304289 5194275820442134134978217)
                    ·
                      refine ⟨3895706865331600601233663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194275820442134134978217 3895706865331600601233663)
                      ·
                        rfl

theorem cell23_7586862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_7586862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586862 prefixEnd_7586862 := by exact prefixLift 7586862
  have htrace : WordTrace (prefixWord ++ tailWord_7586862) baseStart_7586862 baseEnd_7586862 := by
    simpa [prefixWord, tailWord_7586862, baseEnd_7586862] using wordTrace_append hprefix tailTrace_7586862
  have hstable : (prefixWord ++ tailWord_7586862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586862).length < 2 ^ (prefixWord ++ tailWord_7586862).sum := by decide
  have hdescent : baseEnd_7586862 < baseStart_7586862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586865 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 3]
def baseStart_7586865 : Nat := 118140960795 + 7586865 * 2 ^ 59
def prefixEnd_7586865 : Nat := 4983230072969 + 3 ^ 40 * 7586865 * 2
def baseEnd_7586865 : Nat := 3895708405773564089496149

theorem tailTrace_7586865 : CollatzResearch.WordTrace tailWord_7586865 prefixEnd_7586865 3895708405773564089496149 := by
  unfold tailWord_7586865
  simp only [CollatzResearch.WordTrace]
  refine ⟨276715699659091313228506049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184477133106060875485670699 276715699659091313228506049)
  ·
    refine ⟨207536774744318484921379537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276715699659091313228506049 207536774744318484921379537)
    ·
      refine ⟨155652581058238863691034653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207536774744318484921379537 155652581058238863691034653)
      ·
        refine ⟨58369717896839573884137995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155652581058238863691034653 58369717896839573884137995)
        ·
          refine ⟨87554576845259360826206993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58369717896839573884137995 87554576845259360826206993)
          ·
            refine ⟨65665932633944520619655245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87554576845259360826206993 65665932633944520619655245)
            ·
              refine ⟨24624724737729195232370717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65665932633944520619655245 24624724737729195232370717)
              ·
                refine ⟨9234271776648448212139019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24624724737729195232370717 9234271776648448212139019)
                ·
                  refine ⟨13851407664972672318208529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9234271776648448212139019 13851407664972672318208529)
                  ·
                    refine ⟨10388555748729504238656397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13851407664972672318208529 10388555748729504238656397)
                    ·
                      refine ⟨3895708405773564089496149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10388555748729504238656397 3895708405773564089496149)
                      ·
                        rfl

theorem cell23_7586865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_7586865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586865 prefixEnd_7586865 := by exact prefixLift 7586865
  have htrace : WordTrace (prefixWord ++ tailWord_7586865) baseStart_7586865 baseEnd_7586865 := by
    simpa [prefixWord, tailWord_7586865, baseEnd_7586865] using wordTrace_append hprefix tailTrace_7586865
  have hstable : (prefixWord ++ tailWord_7586865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586865).length < 2 ^ (prefixWord ++ tailWord_7586865).sum := by decide
  have hdescent : baseEnd_7586865 < baseStart_7586865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586871 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_7586871 : Nat := 118140960795 + 7586871 * 2 ^ 59
def prefixEnd_7586871 : Nat := 4983230072969 + 3 ^ 40 * 7586871 * 2
def baseEnd_7586871 : Nat := 3895711486657491066021121

theorem tailTrace_7586871 : CollatzResearch.WordTrace tailWord_7586871 prefixEnd_7586871 3895711486657491066021121 := by
  unfold tailWord_7586871
  simp only [CollatzResearch.WordTrace]
  refine ⟨276715918497069576253224467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184477278998046384168816311 276715918497069576253224467)
  ·
    refine ⟨415073877745604364379836701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276715918497069576253224467 415073877745604364379836701)
    ·
      refine ⟨155652704154601636642438763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415073877745604364379836701 155652704154601636642438763)
      ·
        refine ⟨233479056231902454963658145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155652704154601636642438763 233479056231902454963658145)
        ·
          refine ⟨175109292173926841222743609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233479056231902454963658145 175109292173926841222743609)
          ·
            refine ⟨131331969130445130917057707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175109292173926841222743609 131331969130445130917057707)
            ·
              refine ⟨196997953695667696375586561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131331969130445130917057707 196997953695667696375586561)
              ·
                refine ⟨147748465271750772281689921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196997953695667696375586561 147748465271750772281689921)
                ·
                  refine ⟨110811348953813079211267441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147748465271750772281689921 110811348953813079211267441)
                  ·
                    refine ⟨83108511715359809408450581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110811348953813079211267441 83108511715359809408450581)
                    ·
                      refine ⟨3895711486657491066021121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83108511715359809408450581 3895711486657491066021121)
                      ·
                        rfl

theorem cell23_7586871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_7586871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586871 prefixEnd_7586871 := by exact prefixLift 7586871
  have htrace : WordTrace (prefixWord ++ tailWord_7586871) baseStart_7586871 baseEnd_7586871 := by
    simpa [prefixWord, tailWord_7586871, baseEnd_7586871] using wordTrace_append hprefix tailTrace_7586871
  have hstable : (prefixWord ++ tailWord_7586871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586871).length < 2 ^ (prefixWord ++ tailWord_7586871).sum := by decide
  have hdescent : baseEnd_7586871 < baseStart_7586871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586872 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 2, 4]
def baseStart_7586872 : Nat := 118140960795 + 7586872 * 2 ^ 59
def prefixEnd_7586872 : Nat := 4983230072969 + 3 ^ 40 * 7586872 * 2
def baseEnd_7586872 : Nat := 1298570666712715187369539

theorem tailTrace_7586872 : CollatzResearch.WordTrace tailWord_7586872 prefixEnd_7586872 1298570666712715187369539 := by
  unfold tailWord_7586872
  simp only [CollatzResearch.WordTrace]
  refine ⟨138357977485032976712005435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184477303313377302282673913 138357977485032976712005435)
  ·
    refine ⟨207536966227549465068008153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138357977485032976712005435 207536966227549465068008153)
    ·
      refine ⟨155652724670662098801006115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207536966227549465068008153 155652724670662098801006115)
      ·
        refine ⟨233479087005993148201509173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155652724670662098801006115 233479087005993148201509173)
        ·
          refine ⟨21888664406811857643891485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233479087005993148201509173 21888664406811857643891485)
          ·
            refine ⟨8208249152554446616459307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21888664406811857643891485 8208249152554446616459307)
            ·
              refine ⟨12312373728831669924688961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208249152554446616459307 12312373728831669924688961)
              ·
                refine ⟨9234280296623752443516721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12312373728831669924688961 9234280296623752443516721)
                ·
                  refine ⟨6925710222467814332637541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9234280296623752443516721 6925710222467814332637541)
                  ·
                    refine ⟨1298570666712715187369539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6925710222467814332637541 1298570666712715187369539)
                    ·
                      rfl

theorem cell23_7586872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_7586872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586872 prefixEnd_7586872 := by exact prefixLift 7586872
  have htrace : WordTrace (prefixWord ++ tailWord_7586872) baseStart_7586872 baseEnd_7586872 := by
    simpa [prefixWord, tailWord_7586872, baseEnd_7586872] using wordTrace_append hprefix tailTrace_7586872
  have hstable : (prefixWord ++ tailWord_7586872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586872).length < 2 ^ (prefixWord ++ tailWord_7586872).sum := by decide
  have hdescent : baseEnd_7586872 < baseStart_7586872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586891 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 5]
def baseStart_7586891 : Nat := 118140960795 + 7586891 * 2 ^ 59
def prefixEnd_7586891 : Nat := 4983230072969 + 3 ^ 40 * 7586891 * 2
def baseEnd_7586891 : Nat := 3895721756270580987771029

theorem tailTrace_7586891 : CollatzResearch.WordTrace tailWord_7586891 prefixEnd_7586891 3895721756270580987771029 := by
  unfold tailWord_7586891
  simp only [CollatzResearch.WordTrace]
  refine ⟨276716647956997119668952527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184477765304664746445968351 276716647956997119668952527)
  ·
    refine ⟨415074971935495679503428791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276716647956997119668952527 415074971935495679503428791)
    ·
      refine ⟨622612457903243519255143187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415074971935495679503428791 622612457903243519255143187)
      ·
        refine ⟨933918686854865278882714781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622612457903243519255143187 933918686854865278882714781)
        ·
          refine ⟨350219507570574479581018043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 933918686854865278882714781 350219507570574479581018043)
          ·
            refine ⟨525329261355861719371527065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350219507570574479581018043 525329261355861719371527065)
            ·
              refine ⟨393996946016896289528645299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525329261355861719371527065 393996946016896289528645299)
              ·
                refine ⟨590995419025344434292967949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393996946016896289528645299 590995419025344434292967949)
                ·
                  refine ⟨221623282134504162859862981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590995419025344434292967949 221623282134504162859862981)
                  ·
                    refine ⟨41554365400219530536224309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221623282134504162859862981 41554365400219530536224309)
                    ·
                      refine ⟨3895721756270580987771029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41554365400219530536224309 3895721756270580987771029)
                      ·
                        rfl

theorem cell23_7586891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_7586891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586891 prefixEnd_7586891 := by exact prefixLift 7586891
  have htrace : WordTrace (prefixWord ++ tailWord_7586891) baseStart_7586891 baseEnd_7586891 := by
    simpa [prefixWord, tailWord_7586891, baseEnd_7586891] using wordTrace_append hprefix tailTrace_7586891
  have hstable : (prefixWord ++ tailWord_7586891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586891).length < 2 ^ (prefixWord ++ tailWord_7586891).sum := by decide
  have hdescent : baseEnd_7586891 < baseStart_7586891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586902 : List Nat := [5, 2, 2, 1, 2, 1, 1, 9]
def baseStart_7586902 : Nat := 118140960795 + 7586902 * 2 ^ 59
def prefixEnd_7586902 : Nat := 4983230072969 + 3 ^ 40 * 7586902 * 2
def baseEnd_7586902 : Nat := 144286200168806683138277

theorem tailTrace_7586902 : CollatzResearch.WordTrace tailWord_7586902 prefixEnd_7586902 144286200168806683138277 := by
  unfold tailWord_7586902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294815572497329284225185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184478032773304845698401973 17294815572497329284225185)
  ·
    refine ⟨12971111679372996963168889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17294815572497329284225185 12971111679372996963168889)
    ·
      refine ⟨9728333759529747722376667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12971111679372996963168889 9728333759529747722376667)
      ·
        refine ⟨14592500639294621583565001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9728333759529747722376667 14592500639294621583565001)
        ·
          refine ⟨10944375479470966187673751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14592500639294621583565001 10944375479470966187673751)
          ·
            refine ⟨16416563219206449281510627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10944375479470966187673751 16416563219206449281510627)
            ·
              refine ⟨24624844828809673922265941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16416563219206449281510627 24624844828809673922265941)
              ·
                refine ⟨144286200168806683138277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24624844828809673922265941 144286200168806683138277)
                ·
                  rfl

theorem cell23_7586902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_7586902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586902 prefixEnd_7586902 := by exact prefixLift 7586902
  have htrace : WordTrace (prefixWord ++ tailWord_7586902) baseStart_7586902 baseEnd_7586902 := by
    simpa [prefixWord, tailWord_7586902, baseEnd_7586902] using wordTrace_append hprefix tailTrace_7586902
  have hstable : (prefixWord ++ tailWord_7586902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586902).length < 2 ^ (prefixWord ++ tailWord_7586902).sum := by decide
  have hdescent : baseEnd_7586902 < baseStart_7586902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586908 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_7586908 : Nat := 118140960795 + 7586908 * 2 ^ 59
def prefixEnd_7586908 : Nat := 4983230072969 + 3 ^ 40 * 7586908 * 2
def baseEnd_7586908 : Nat := 3895730485441707421258451

theorem tailTrace_7586908 : CollatzResearch.WordTrace tailWord_7586908 prefixEnd_7586908 3895730485441707421258451 := by
  unfold tailWord_7586908
  simp only [CollatzResearch.WordTrace]
  refine ⟨138358633998967765786160689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184478178665290354381547585 138358633998967765786160689)
  ·
    refine ⟨103768975499225824339620517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138358633998967765786160689 103768975499225824339620517)
    ·
      refine ⟨19456682906104842063678847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103768975499225824339620517 19456682906104842063678847)
      ·
        refine ⟨29185024359157263095518271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19456682906104842063678847 29185024359157263095518271)
        ·
          refine ⟨43777536538735894643277407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29185024359157263095518271 43777536538735894643277407)
          ·
            refine ⟨65666304808103841964916111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43777536538735894643277407 65666304808103841964916111)
            ·
              refine ⟨98499457212155762947374167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65666304808103841964916111 98499457212155762947374167)
              ·
                refine ⟨147749185818233644421061251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98499457212155762947374167 147749185818233644421061251)
                ·
                  refine ⟨221623778727350466631591877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147749185818233644421061251 221623778727350466631591877)
                  ·
                    refine ⟨41554458511378212493423477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221623778727350466631591877 41554458511378212493423477)
                    ·
                      refine ⟨3895730485441707421258451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41554458511378212493423477 3895730485441707421258451)
                      ·
                        rfl

theorem cell23_7586908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_7586908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586908 prefixEnd_7586908 := by exact prefixLift 7586908
  have htrace : WordTrace (prefixWord ++ tailWord_7586908) baseStart_7586908 baseEnd_7586908 := by
    simpa [prefixWord, tailWord_7586908, baseEnd_7586908] using wordTrace_append hprefix tailTrace_7586908
  have hstable : (prefixWord ++ tailWord_7586908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586908).length < 2 ^ (prefixWord ++ tailWord_7586908).sum := by decide
  have hdescent : baseEnd_7586908 < baseStart_7586908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586986 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7586986 : Nat := 118140960795 + 7586986 * 2 ^ 59
def prefixEnd_7586986 : Nat := 4983230072969 + 3 ^ 40 * 7586986 * 2
def baseEnd_7586986 : Nat := 3895770536932758116083093

theorem tailTrace_7586986 : CollatzResearch.WordTrace tailWord_7586986 prefixEnd_7586986 3895770536932758116083093 := by
  unfold tailWord_7586986
  simp only [CollatzResearch.WordTrace]
  refine ⟨69180028222913237723415203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184480075261101967262440541 69180028222913237723415203)
  ·
    refine ⟨103770042334369856585122805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69180028222913237723415203 103770042334369856585122805)
    ·
      refine ⟨9728441468847174054855263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103770042334369856585122805 9728441468847174054855263)
      ·
        refine ⟨14592662203270761082282895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9728441468847174054855263 14592662203270761082282895)
        ·
          refine ⟨21888993304906141623424343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14592662203270761082282895 21888993304906141623424343)
          ·
            refine ⟨32833489957359212435136515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21888993304906141623424343 32833489957359212435136515)
            ·
              refine ⟨49250234936038818652704773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32833489957359212435136515 49250234936038818652704773)
              ·
                refine ⟨9234419050507278497382145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49250234936038818652704773 9234419050507278497382145)
                ·
                  refine ⟨6925814287880458873036609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9234419050507278497382145 6925814287880458873036609)
                  ·
                    refine ⟨5194360715910344154777457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6925814287880458873036609 5194360715910344154777457)
                    ·
                      refine ⟨3895770536932758116083093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194360715910344154777457 3895770536932758116083093)
                      ·
                        rfl

theorem cell23_7586986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7586986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586986 prefixEnd_7586986 := by exact prefixLift 7586986
  have htrace : WordTrace (prefixWord ++ tailWord_7586986) baseStart_7586986 baseEnd_7586986 := by
    simpa [prefixWord, tailWord_7586986, baseEnd_7586986] using wordTrace_append hprefix tailTrace_7586986
  have hstable : (prefixWord ++ tailWord_7586986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586986).length < 2 ^ (prefixWord ++ tailWord_7586986).sum := by decide
  have hdescent : baseEnd_7586986 < baseStart_7586986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586988 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_7586988 : Nat := 118140960795 + 7586988 * 2 ^ 59
def prefixEnd_7586988 : Nat := 4983230072969 + 3 ^ 40 * 7586988 * 2
def baseEnd_7586988 : Nat := 1298590521298022369419361

theorem tailTrace_7586988 : CollatzResearch.WordTrace tailWord_7586988 prefixEnd_7586988 1298590521298022369419361 := by
  unfold tailWord_7586988
  simp only [CollatzResearch.WordTrace]
  refine ⟨138360092918822852617616809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184480123891763803490155745 138360092918822852617616809)
  ·
    refine ⟨103770069689117139463212607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138360092918822852617616809 103770069689117139463212607)
    ·
      refine ⟨155655104533675709194818911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103770069689117139463212607 155655104533675709194818911)
      ·
        refine ⟨233482656800513563792228367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155655104533675709194818911 233482656800513563792228367)
        ·
          refine ⟨350223985200770345688342551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233482656800513563792228367 350223985200770345688342551)
          ·
            refine ⟨525335977801155518532513827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350223985200770345688342551 525335977801155518532513827)
            ·
              refine ⟨788003966701733277798770741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525335977801155518532513827 788003966701733277798770741)
              ·
                refine ⟨73875371878287494793634757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 788003966701733277798770741 73875371878287494793634757)
                ·
                  refine ⟨13851632227178905273806517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73875371878287494793634757 13851632227178905273806517)
                  ·
                    refine ⟨1298590521298022369419361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13851632227178905273806517 1298590521298022369419361)
                    ·
                      rfl

theorem cell23_7586988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_7586988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586988 prefixEnd_7586988 := by exact prefixLift 7586988
  have htrace : WordTrace (prefixWord ++ tailWord_7586988) baseStart_7586988 baseEnd_7586988 := by
    simpa [prefixWord, tailWord_7586988, baseEnd_7586988] using wordTrace_append hprefix tailTrace_7586988
  have hstable : (prefixWord ++ tailWord_7586988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586988).length < 2 ^ (prefixWord ++ tailWord_7586988).sum := by decide
  have hdescent : baseEnd_7586988 < baseStart_7586988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7586995 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 2, 5, 2]
def baseStart_7586995 : Nat := 118140960795 + 7586995 * 2 ^ 59
def prefixEnd_7586995 : Nat := 4983230072969 + 3 ^ 40 * 7586995 * 2
def baseEnd_7586995 : Nat := 3895775158258648580870551

theorem tailTrace_7586995 : CollatzResearch.WordTrace tailWord_7586995 prefixEnd_7586995 3895775158258648580870551 := by
  unfold tailWord_7586995
  simp only [CollatzResearch.WordTrace]
  refine ⟨276720441148620345430738439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184480294099080230287158959 276720441148620345430738439)
  ·
    refine ⟨415080661722930518146107659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276720441148620345430738439 415080661722930518146107659)
    ·
      refine ⟨622620992584395777219161489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415080661722930518146107659 622620992584395777219161489)
      ·
        refine ⟨466965744438296832914371117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622620992584395777219161489 466965744438296832914371117)
        ·
          refine ⟨175112154164361312342889169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466965744438296832914371117 175112154164361312342889169)
          ·
            refine ⟨131334115623270984257166877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175112154164361312342889169 131334115623270984257166877)
            ·
              refine ⟨49250293358726619096437579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131334115623270984257166877 49250293358726619096437579)
              ·
                refine ⟨73875440038089928644656369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49250293358726619096437579 73875440038089928644656369)
                ·
                  refine ⟨55406580028567446483492277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73875440038089928644656369 55406580028567446483492277)
                  ·
                    refine ⟨5194366877678198107827401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55406580028567446483492277 5194366877678198107827401)
                    ·
                      refine ⟨3895775158258648580870551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194366877678198107827401 3895775158258648580870551)
                      ·
                        rfl

theorem cell23_7586995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 5, 2].length) (baseStart_7586995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7586995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7586995 prefixEnd_7586995 := by exact prefixLift 7586995
  have htrace : WordTrace (prefixWord ++ tailWord_7586995) baseStart_7586995 baseEnd_7586995 := by
    simpa [prefixWord, tailWord_7586995, baseEnd_7586995] using wordTrace_append hprefix tailTrace_7586995
  have hstable : (prefixWord ++ tailWord_7586995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7586995).length < 2 ^ (prefixWord ++ tailWord_7586995).sum := by decide
  have hdescent : baseEnd_7586995 < baseStart_7586995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7586995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587025 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 3, 6, 2]
def baseStart_7587025 : Nat := 118140960795 + 7587025 * 2 ^ 59
def prefixEnd_7587025 : Nat := 4983230072969 + 3 ^ 40 * 7587025 * 2
def baseEnd_7587025 : Nat := 3895790562678283463495413

theorem tailTrace_7587025 : CollatzResearch.WordTrace tailWord_7587025 prefixEnd_7587025 3895790562678283463495413 := by
  unfold tailWord_7587025
  simp only [CollatzResearch.WordTrace]
  refine ⟨276721535338511660554330529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184481023559007773702887019 276721535338511660554330529)
  ·
    refine ⟨207541151503883745415747897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276721535338511660554330529 207541151503883745415747897)
    ·
      refine ⟨155655863627912809061810923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207541151503883745415747897 155655863627912809061810923)
      ·
        refine ⟨233483795441869213592716385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155655863627912809061810923 233483795441869213592716385)
        ·
          refine ⟨175112846581401910194537289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233483795441869213592716385 175112846581401910194537289)
          ·
            refine ⟨131334634936051432645902967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175112846581401910194537289 131334634936051432645902967)
            ·
              refine ⟨197001952404077148968854451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131334634936051432645902967 197001952404077148968854451)
              ·
                refine ⟨295502928606115723453281677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197001952404077148968854451 295502928606115723453281677)
                ·
                  refine ⟨110813598227293396294980629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295502928606115723453281677 110813598227293396294980629)
                  ·
                    refine ⟨5194387416904377951327217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110813598227293396294980629 5194387416904377951327217)
                    ·
                      refine ⟨3895790562678283463495413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194387416904377951327217 3895790562678283463495413)
                      ·
                        rfl

theorem cell23_7587025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_7587025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587025 prefixEnd_7587025 := by exact prefixLift 7587025
  have htrace : WordTrace (prefixWord ++ tailWord_7587025) baseStart_7587025 baseEnd_7587025 := by
    simpa [prefixWord, tailWord_7587025, baseEnd_7587025] using wordTrace_append hprefix tailTrace_7587025
  have hstable : (prefixWord ++ tailWord_7587025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587025).length < 2 ^ (prefixWord ++ tailWord_7587025).sum := by decide
  have hdescent : baseEnd_7587025 < baseStart_7587025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587052 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_7587052 : Nat := 118140960795 + 7587052 * 2 ^ 59
def prefixEnd_7587052 : Nat := 4983230072969 + 3 ^ 40 * 7587052 * 2
def baseEnd_7587052 : Nat := 1298601475551984952619263

theorem tailTrace_7587052 : CollatzResearch.WordTrace tailWord_7587052 prefixEnd_7587052 1298601475551984952619263 := by
  unfold tailWord_7587052
  simp only [CollatzResearch.WordTrace]
  refine ⟨138361260054706922082781705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184481680072942562777042273 138361260054706922082781705)
  ·
    refine ⟨103770945041030191562086279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138361260054706922082781705 103770945041030191562086279)
    ·
      refine ⟨155656417561545287343129419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103770945041030191562086279 155656417561545287343129419)
      ·
        refine ⟨233484626342317931014694129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155656417561545287343129419 233484626342317931014694129)
        ·
          refine ⟨175113469756738448261020597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233484626342317931014694129 175113469756738448261020597)
          ·
            refine ⟨16416887789694229524470681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175113469756738448261020597 16416887789694229524470681)
            ·
              refine ⟨12312665842270672143353011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16416887789694229524470681 12312665842270672143353011)
              ·
                refine ⟨18468998763406008215029517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12312665842270672143353011 18468998763406008215029517)
                ·
                  refine ⟨6925874536277253080636069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18468998763406008215029517 6925874536277253080636069)
                  ·
                    refine ⟨1298601475551984952619263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6925874536277253080636069 1298601475551984952619263)
                    ·
                      rfl

theorem cell23_7587052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_7587052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587052 prefixEnd_7587052 := by exact prefixLift 7587052
  have htrace : WordTrace (prefixWord ++ tailWord_7587052) baseStart_7587052 baseEnd_7587052 := by
    simpa [prefixWord, tailWord_7587052, baseEnd_7587052] using wordTrace_append hprefix tailTrace_7587052
  have hstable : (prefixWord ++ tailWord_7587052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587052).length < 2 ^ (prefixWord ++ tailWord_7587052).sum := by decide
  have hdescent : baseEnd_7587052 < baseStart_7587052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587086 : List Nat := [4, 1, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_7587086 : Nat := 118140960795 + 7587086 * 2 ^ 59
def prefixEnd_7587086 : Nat := 4983230072969 + 3 ^ 40 * 7587086 * 2
def baseEnd_7587086 : Nat := 1298607294999402574944211

theorem tailTrace_7587086 : CollatzResearch.WordTrace tailWord_7587086 prefixEnd_7587086 1298607294999402574944211 := by
  unfold tailWord_7587086
  simp only [CollatzResearch.WordTrace]
  refine ⟨34590470023911333496537639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184482506794193778648200741 34590470023911333496537639)
  ·
    refine ⟨51885705035867000244806459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34590470023911333496537639 51885705035867000244806459)
    ·
      refine ⟨77828557553800500367209689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51885705035867000244806459 77828557553800500367209689)
      ·
        refine ⟨58371418165350375275407267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77828557553800500367209689 58371418165350375275407267)
        ·
          refine ⟨87557127248025562913110901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58371418165350375275407267 87557127248025562913110901)
          ·
            refine ⟨8208480679502396523104147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87557127248025562913110901 8208480679502396523104147)
            ·
              refine ⟨12312721019253594784656221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208480679502396523104147 12312721019253594784656221)
              ·
                refine ⟨4617270382220098044246083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12312721019253594784656221 4617270382220098044246083)
                ·
                  refine ⟨6925905573330147066369125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4617270382220098044246083 6925905573330147066369125)
                  ·
                    refine ⟨1298607294999402574944211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6925905573330147066369125 1298607294999402574944211)
                    ·
                      rfl

theorem cell23_7587086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_7587086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587086 prefixEnd_7587086 := by exact prefixLift 7587086
  have htrace : WordTrace (prefixWord ++ tailWord_7587086) baseStart_7587086 baseEnd_7587086 := by
    simpa [prefixWord, tailWord_7587086, baseEnd_7587086] using wordTrace_append hprefix tailTrace_7587086
  have hstable : (prefixWord ++ tailWord_7587086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587086).length < 2 ^ (prefixWord ++ tailWord_7587086).sum := by decide
  have hdescent : baseEnd_7587086 < baseStart_7587086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587088 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_7587088 : Nat := 118140960795 + 7587088 * 2 ^ 59
def prefixEnd_7587088 : Nat := 4983230072969 + 3 ^ 40 * 7587088 * 2
def baseEnd_7587088 : Nat := 3895822911959516717007623

theorem tailTrace_7587088 : CollatzResearch.WordTrace tailWord_7587088 prefixEnd_7587088 3895822911959516717007623 := by
  unfold tailWord_7587088
  simp only [CollatzResearch.WordTrace]
  refine ⟨138361916568641711156936959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184482555424855614875915945 138361916568641711156936959)
  ·
    refine ⟨207542874852962566735405439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138361916568641711156936959 207542874852962566735405439)
    ·
      refine ⟨311314312279443850103108159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207542874852962566735405439 311314312279443850103108159)
      ·
        refine ⟨466971468419165775154662239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311314312279443850103108159 466971468419165775154662239)
        ·
          refine ⟨700457202628748662731993359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466971468419165775154662239 700457202628748662731993359)
          ·
            refine ⟨1050685803943122994097990039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700457202628748662731993359 1050685803943122994097990039)
            ·
              refine ⟨1576028705914684491146985059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050685803943122994097990039 1576028705914684491146985059)
              ·
                refine ⟨2364043058872026736720477589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576028705914684491146985059 2364043058872026736720477589)
                ·
                  refine ⟨110814518384626253283772387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2364043058872026736720477589 110814518384626253283772387)
                  ·
                    refine ⟨166221777576939379925658581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110814518384626253283772387 166221777576939379925658581)
                    ·
                      refine ⟨3895822911959516717007623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166221777576939379925658581 3895822911959516717007623)
                      ·
                        rfl

theorem cell23_7587088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_7587088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587088 prefixEnd_7587088 := by exact prefixLift 7587088
  have htrace : WordTrace (prefixWord ++ tailWord_7587088) baseStart_7587088 baseEnd_7587088 := by
    simpa [prefixWord, tailWord_7587088, baseEnd_7587088] using wordTrace_append hprefix tailTrace_7587088
  have hstable : (prefixWord ++ tailWord_7587088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587088).length < 2 ^ (prefixWord ++ tailWord_7587088).sum := by decide
  have hdescent : baseEnd_7587088 < baseStart_7587088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587109 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 3]
def baseStart_7587109 : Nat := 118140960795 + 7587109 * 2 ^ 59
def prefixEnd_7587109 : Nat := 4983230072969 + 3 ^ 40 * 7587109 * 2
def baseEnd_7587109 : Nat := 3895833695053261134845027

theorem tailTrace_7587109 : CollatzResearch.WordTrace tailWord_7587109 prefixEnd_7587109 3895833695053261134845027 := by
  unfold tailWord_7587109
  simp only [CollatzResearch.WordTrace]
  refine ⟨276724599070207342900388381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184483066046804895266925587 276724599070207342900388381)
  ·
    refine ⟨103771724651327753587645643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276724599070207342900388381 103771724651327753587645643)
    ·
      refine ⟨155657586976991630381468465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103771724651327753587645643 155657586976991630381468465)
      ·
        refine ⟨116743190232743722786101349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155657586976991630381468465 116743190232743722786101349)
        ·
          refine ⟨21889348168639448022394003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116743190232743722786101349 21889348168639448022394003)
          ·
            refine ⟨32834022252959172033591005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21889348168639448022394003 32834022252959172033591005)
            ·
              refine ⟨12312758344859689512596627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32834022252959172033591005 12312758344859689512596627)
              ·
                refine ⟨18469137517289534268894941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12312758344859689512596627 18469137517289534268894941)
                ·
                  refine ⟨6925926568983575350835603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18469137517289534268894941 6925926568983575350835603)
                  ·
                    refine ⟨10388889853475363026253405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6925926568983575350835603 10388889853475363026253405)
                    ·
                      refine ⟨3895833695053261134845027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10388889853475363026253405 3895833695053261134845027)
                      ·
                        rfl

theorem cell23_7587109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_7587109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587109 prefixEnd_7587109 := by exact prefixLift 7587109
  have htrace : WordTrace (prefixWord ++ tailWord_7587109) baseStart_7587109 baseEnd_7587109 := by
    simpa [prefixWord, tailWord_7587109, baseEnd_7587109] using wordTrace_append hprefix tailTrace_7587109
  have hstable : (prefixWord ++ tailWord_7587109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587109).length < 2 ^ (prefixWord ++ tailWord_7587109).sum := by decide
  have hdescent : baseEnd_7587109 < baseStart_7587109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587132 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_7587132 : Nat := 118140960795 + 7587132 * 2 ^ 59
def prefixEnd_7587132 : Nat := 4983230072969 + 3 ^ 40 * 7587132 * 2
def baseEnd_7587132 : Nat := 3895845505108314544857421

theorem tailTrace_7587132 : CollatzResearch.WordTrace tailWord_7587132 prefixEnd_7587132 3895845505108314544857421 := by
  unfold tailWord_7587132
  simp only [CollatzResearch.WordTrace]
  refine ⟨138362718974562008914237825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184483625299416011885650433 138362718974562008914237825)
  ·
    refine ⟨103772039230921506685678369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138362718974562008914237825 103772039230921506685678369)
    ·
      refine ⟨77829029423191130014258777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103772039230921506685678369 77829029423191130014258777)
      ·
        refine ⟨58371772067393347510694083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77829029423191130014258777 58371772067393347510694083)
        ·
          refine ⟨87557658101090021266041125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58371772067393347510694083 87557658101090021266041125)
          ·
            refine ⟨16417060893954378987382711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87557658101090021266041125 16417060893954378987382711)
            ·
              refine ⟨24625591340931568481074067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16417060893954378987382711 24625591340931568481074067)
              ·
                refine ⟨36938387011397352721611101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24625591340931568481074067 36938387011397352721611101)
                ·
                  refine ⟨13851895129274007270604163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36938387011397352721611101 13851895129274007270604163)
                  ·
                    refine ⟨20777842693911010905906245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13851895129274007270604163 20777842693911010905906245)
                    ·
                      refine ⟨3895845505108314544857421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20777842693911010905906245 3895845505108314544857421)
                      ·
                        rfl

theorem cell23_7587132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_7587132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587132 prefixEnd_7587132 := by exact prefixLift 7587132
  have htrace : WordTrace (prefixWord ++ tailWord_7587132) baseStart_7587132 baseEnd_7587132 := by
    simpa [prefixWord, tailWord_7587132, baseEnd_7587132] using wordTrace_append hprefix tailTrace_7587132
  have hstable : (prefixWord ++ tailWord_7587132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587132).length < 2 ^ (prefixWord ++ tailWord_7587132).sum := by decide
  have hdescent : baseEnd_7587132 < baseStart_7587132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587145 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_7587145 : Nat := 118140960795 + 7587145 * 2 ^ 59
def prefixEnd_7587145 : Nat := 4983230072969 + 3 ^ 40 * 7587145 * 2
def baseEnd_7587145 : Nat := 3895852180356822993994861

theorem tailTrace_7587145 : CollatzResearch.WordTrace tailWord_7587145 prefixEnd_7587145 3895852180356822993994861 := by
  unfold tailWord_7587145
  simp only [CollatzResearch.WordTrace]
  refine ⟨276725912098076921048698889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184483941398717947365799259 276725912098076921048698889)
  ·
    refine ⟨207544434073557690786524167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276725912098076921048698889 207544434073557690786524167)
    ·
      refine ⟨311316651110336536179786251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207544434073557690786524167 311316651110336536179786251)
      ·
        refine ⟨466974976665504804269679377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311316651110336536179786251 466974976665504804269679377)
        ·
          refine ⟨350231232499128603202259533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466974976665504804269679377 350231232499128603202259533)
          ·
            refine ⟨131336712187173226200847325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350231232499128603202259533 131336712187173226200847325)
            ·
              refine ⟨49251267070189959825317747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131336712187173226200847325 49251267070189959825317747)
              ·
                refine ⟨73876900605284939737976621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49251267070189959825317747 73876900605284939737976621)
                ·
                  refine ⟨27703837726981852401741233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73876900605284939737976621 27703837726981852401741233)
                  ·
                    refine ⟨20777878295236389301305925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27703837726981852401741233 20777878295236389301305925)
                    ·
                      refine ⟨3895852180356822993994861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20777878295236389301305925 3895852180356822993994861)
                      ·
                        rfl

theorem cell23_7587145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_7587145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587145 prefixEnd_7587145 := by exact prefixLift 7587145
  have htrace : WordTrace (prefixWord ++ tailWord_7587145) baseStart_7587145 baseEnd_7587145 := by
    simpa [prefixWord, tailWord_7587145, baseEnd_7587145] using wordTrace_append hprefix tailTrace_7587145
  have hstable : (prefixWord ++ tailWord_7587145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587145).length < 2 ^ (prefixWord ++ tailWord_7587145).sum := by decide
  have hdescent : baseEnd_7587145 < baseStart_7587145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587159 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 2, 4]
def baseStart_7587159 : Nat := 118140960795 + 7587159 * 2 ^ 59
def prefixEnd_7587159 : Nat := 4983230072969 + 3 ^ 40 * 7587159 * 2
def baseEnd_7587159 : Nat := 1298619789695328646406599

theorem tailTrace_7587159 : CollatzResearch.WordTrace tailWord_7587159 prefixEnd_7587159 1298619789695328646406599 := by
  unfold tailWord_7587159
  simp only [CollatzResearch.WordTrace]
  refine ⟨276726422720026201439708531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184484281813350800959805687 276726422720026201439708531)
  ·
    refine ⟨415089634080039302159562797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276726422720026201439708531 415089634080039302159562797)
    ·
      refine ⟨155658612780014738309836049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415089634080039302159562797 155658612780014738309836049)
      ·
        refine ⟨116743959585011053732377037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155658612780014738309836049 116743959585011053732377037)
        ·
          refine ⟨43778984844379145149641389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116743959585011053732377037 43778984844379145149641389)
          ·
            refine ⟨16417119316642179431115521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43778984844379145149641389 16417119316642179431115521)
            ·
              refine ⟨12312839487481634573336641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16417119316642179431115521 12312839487481634573336641)
              ·
                refine ⟨9234629615611225930002481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12312839487481634573336641 9234629615611225930002481)
                ·
                  refine ⟨6925972211708419447501861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9234629615611225930002481 6925972211708419447501861)
                  ·
                    refine ⟨1298619789695328646406599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6925972211708419447501861 1298619789695328646406599)
                    ·
                      rfl

theorem cell23_7587159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_7587159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587159 prefixEnd_7587159 := by exact prefixLift 7587159
  have htrace : WordTrace (prefixWord ++ tailWord_7587159) baseStart_7587159 baseEnd_7587159 := by
    simpa [prefixWord, tailWord_7587159, baseEnd_7587159] using wordTrace_append hprefix tailTrace_7587159
  have hstable : (prefixWord ++ tailWord_7587159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587159).length < 2 ^ (prefixWord ++ tailWord_7587159).sum := by decide
  have hdescent : baseEnd_7587159 < baseStart_7587159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587172 : List Nat := [2, 3, 1, 1, 3, 4, 1, 8]
def baseStart_7587172 : Nat := 118140960795 + 7587172 * 2 ^ 59
def prefixEnd_7587172 : Nat := 4983230072969 + 3 ^ 40 * 7587172 * 2
def baseEnd_7587172 : Nat := 144291334975351644013231

theorem tailTrace_7587172 : CollatzResearch.WordTrace tailWord_7587172 prefixEnd_7587172 144291334975351644013231 := by
  unfold tailWord_7587172
  simp only [CollatzResearch.WordTrace]
  refine ⟨138363448434489552329965885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184484597912652736439954513 138363448434489552329965885)
  ·
    refine ⟨51886293162933582123737207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138363448434489552329965885 51886293162933582123737207)
    ·
      refine ⟨77829439744400373185605811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51886293162933582123737207 77829439744400373185605811)
      ·
        refine ⟨116744159616600559778408717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77829439744400373185605811 116744159616600559778408717)
        ·
          refine ⟨43779059856225209916903269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116744159616600559778408717 43779059856225209916903269)
          ·
            refine ⟨8208573723042226859419363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43779059856225209916903269 8208573723042226859419363)
            ·
              refine ⟨12312860584563340289129045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208573723042226859419363 12312860584563340289129045)
              ·
                refine ⟨144291334975351644013231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12312860584563340289129045 144291334975351644013231)
                ·
                  rfl

theorem cell23_7587172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 8].length) (baseStart_7587172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587172 prefixEnd_7587172 := by exact prefixLift 7587172
  have htrace : WordTrace (prefixWord ++ tailWord_7587172) baseStart_7587172 baseEnd_7587172 := by
    simpa [prefixWord, tailWord_7587172, baseEnd_7587172] using wordTrace_append hprefix tailTrace_7587172
  have hstable : (prefixWord ++ tailWord_7587172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587172).length < 2 ^ (prefixWord ++ tailWord_7587172).sum := by decide
  have hdescent : baseEnd_7587172 < baseStart_7587172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587189 : List Nat := [1, 3, 4, 1, 3, 1, 3, 7]
def baseStart_7587189 : Nat := 118140960795 + 7587189 * 2 ^ 59
def prefixEnd_7587189 : Nat := 4983230072969 + 3 ^ 40 * 7587189 * 2
def baseEnd_7587189 : Nat := 144291658277985956364617

theorem tailTrace_7587189 : CollatzResearch.WordTrace tailWord_7587189 prefixEnd_7587189 144291658277985956364617 := by
  unfold tailWord_7587189
  simp only [CollatzResearch.WordTrace]
  refine ⟨276727516909917516563300621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184485011273278344375533747 276727516909917516563300621)
  ·
    refine ⟨103772818841219068711237733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276727516909917516563300621 103772818841219068711237733)
    ·
      refine ⟨19457403532728575383357075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103772818841219068711237733 19457403532728575383357075)
      ·
        refine ⟨29186105299092863075035613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19457403532728575383357075 29186105299092863075035613)
        ·
          refine ⟨10944789487159823653138355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29186105299092863075035613 10944789487159823653138355)
          ·
            refine ⟨16417184230739735479707533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10944789487159823653138355 16417184230739735479707533)
            ·
              refine ⟨6156444086527400804890325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16417184230739735479707533 6156444086527400804890325)
              ·
                refine ⟨144291658277985956364617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6156444086527400804890325 144291658277985956364617)
                ·
                  rfl

theorem cell23_7587189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 7].length) (baseStart_7587189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587189 prefixEnd_7587189 := by exact prefixLift 7587189
  have htrace : WordTrace (prefixWord ++ tailWord_7587189) baseStart_7587189 baseEnd_7587189 := by
    simpa [prefixWord, tailWord_7587189, baseEnd_7587189] using wordTrace_append hprefix tailTrace_7587189
  have hstable : (prefixWord ++ tailWord_7587189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587189).length < 2 ^ (prefixWord ++ tailWord_7587189).sum := by decide
  have hdescent : baseEnd_7587189 < baseStart_7587189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587195 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 5]
def baseStart_7587195 : Nat := 118140960795 + 7587195 * 2 ^ 59
def prefixEnd_7587195 : Nat := 4983230072969 + 3 ^ 40 * 7587195 * 2
def baseEnd_7587195 : Nat := 3895877854389547798369631

theorem tailTrace_7587195 : CollatzResearch.WordTrace tailWord_7587195 prefixEnd_7587195 3895877854389547798369631 := by
  unfold tailWord_7587195
  simp only [CollatzResearch.WordTrace]
  refine ⟨276727735747895779588019039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184485157165263853058679359 276727735747895779588019039)
  ·
    refine ⟨415091603621843669382028559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276727735747895779588019039 415091603621843669382028559)
    ·
      refine ⟨622637405432765504073042839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415091603621843669382028559 622637405432765504073042839)
      ·
        refine ⟨933956108149148256109564259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622637405432765504073042839 933956108149148256109564259)
        ·
          refine ⟨1400934162223722384164346389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933956108149148256109564259 1400934162223722384164346389)
          ·
            refine ⟨65668788854236986757703737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1400934162223722384164346389 65668788854236986757703737)
            ·
              refine ⟨49251591640677740068277803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65668788854236986757703737 49251591640677740068277803)
              ·
                refine ⟨73877387461016610102416705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49251591640677740068277803 73877387461016610102416705)
                ·
                  refine ⟨55408040595762457576812529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73877387461016610102416705 55408040595762457576812529)
                  ·
                    refine ⟨41556030446821843182609397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55408040595762457576812529 41556030446821843182609397)
                    ·
                      refine ⟨3895877854389547798369631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41556030446821843182609397 3895877854389547798369631)
                      ·
                        rfl

theorem cell23_7587195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_7587195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587195 prefixEnd_7587195 := by exact prefixLift 7587195
  have htrace : WordTrace (prefixWord ++ tailWord_7587195) baseStart_7587195 baseEnd_7587195 := by
    simpa [prefixWord, tailWord_7587195, baseEnd_7587195] using wordTrace_append hprefix tailTrace_7587195
  have hstable : (prefixWord ++ tailWord_7587195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587195).length < 2 ^ (prefixWord ++ tailWord_7587195).sum := by decide
  have hdescent : baseEnd_7587195 < baseStart_7587195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587290 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2]
def baseStart_7587290 : Nat := 118140960795 + 7587290 * 2 ^ 59
def prefixEnd_7587290 : Nat := 4983230072969 + 3 ^ 40 * 7587290 * 2
def baseEnd_7587290 : Nat := 3895926635051724926681695

theorem tailTrace_7587290 : CollatzResearch.WordTrace tailWord_7587290 prefixEnd_7587290 3895926635051724926681695 := by
  unfold tailWord_7587290
  simp only [CollatzResearch.WordTrace]
  refine ⟨69182800170637902703181831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184487467121701073875151549 69182800170637902703181831)
  ·
    refine ⟨103774200255956854054772747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69182800170637902703181831 103774200255956854054772747)
    ·
      refine ⟨155661300383935281082159121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103774200255956854054772747 155661300383935281082159121)
      ·
        refine ⟨116745975287951460811619341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155661300383935281082159121 116745975287951460811619341)
        ·
          refine ⟨43779740732981797804357253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116745975287951460811619341 43779740732981797804357253)
          ·
            refine ⟨8208701387434087088316985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43779740732981797804357253 8208701387434087088316985)
            ·
              refine ⟨6156526040575565316237739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8208701387434087088316985 6156526040575565316237739)
              ·
                refine ⟨9234789060863347974356609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156526040575565316237739 9234789060863347974356609)
                ·
                  refine ⟨6926091795647510980767457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9234789060863347974356609 6926091795647510980767457)
                  ·
                    refine ⟨5194568846735633235575593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6926091795647510980767457 5194568846735633235575593)
                    ·
                      refine ⟨3895926635051724926681695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194568846735633235575593 3895926635051724926681695)
                      ·
                        rfl

theorem cell23_7587290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_7587290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587290 prefixEnd_7587290 := by exact prefixLift 7587290
  have htrace : WordTrace (prefixWord ++ tailWord_7587290) baseStart_7587290 baseEnd_7587290 := by
    simpa [prefixWord, tailWord_7587290, baseEnd_7587290] using wordTrace_append hprefix tailTrace_7587290
  have hstable : (prefixWord ++ tailWord_7587290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587290).length < 2 ^ (prefixWord ++ tailWord_7587290).sum := by decide
  have hdescent : baseEnd_7587290 < baseStart_7587290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587330 : List Nat := [3, 4, 1, 2, 1, 3, 2, 2, 5]
def baseStart_7587330 : Nat := 118140960795 + 7587330 * 2 ^ 59
def prefixEnd_7587330 : Nat := 4983230072969 + 3 ^ 40 * 7587330 * 2
def baseEnd_7587330 : Nat := 432883019364211641131279

theorem tailTrace_7587330 : CollatzResearch.WordTrace tailWord_7587330 prefixEnd_7587330 432883019364211641131279 := by
  unfold tailWord_7587330
  simp only [CollatzResearch.WordTrace]
  refine ⟨69183164900601674411045861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184488439734937798429455629 69183164900601674411045861)
  ·
    refine ⟨12971843418862813952071099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69183164900601674411045861 12971843418862813952071099)
    ·
      refine ⟨19457765128294220928106649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12971843418862813952071099 19457765128294220928106649)
      ·
        refine ⟨14593323846220665696079987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19457765128294220928106649 14593323846220665696079987)
        ·
          refine ⟨21889985769330998544119981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14593323846220665696079987 21889985769330998544119981)
          ·
            refine ⟨8208744663499124454044993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21889985769330998544119981 8208744663499124454044993)
            ·
              refine ⟨6156558497624343340533745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8208744663499124454044993 6156558497624343340533745)
              ·
                refine ⟨4617418873218257505400309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156558497624343340533745 4617418873218257505400309)
                ·
                  refine ⟨432883019364211641131279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4617418873218257505400309 432883019364211641131279)
                  ·
                    rfl

theorem cell23_7587330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_7587330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587330 prefixEnd_7587330 := by exact prefixLift 7587330
  have htrace : WordTrace (prefixWord ++ tailWord_7587330) baseStart_7587330 baseEnd_7587330 := by
    simpa [prefixWord, tailWord_7587330, baseEnd_7587330] using wordTrace_append hprefix tailTrace_7587330
  have hstable : (prefixWord ++ tailWord_7587330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587330).length < 2 ^ (prefixWord ++ tailWord_7587330).sum := by decide
  have hdescent : baseEnd_7587330 < baseStart_7587330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587363 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 2, 1, 4]
def baseStart_7587363 : Nat := 118140960795 + 7587363 * 2 ^ 59
def prefixEnd_7587363 : Nat := 4983230072969 + 3 ^ 40 * 7587363 * 2
def baseEnd_7587363 : Nat := 3895964119139503141068859

theorem tailTrace_7587363 : CollatzResearch.WordTrace tailWord_7587363 prefixEnd_7587363 3895964119139503141068859 := by
  unfold tailWord_7587363
  simp only [CollatzResearch.WordTrace]
  refine ⟨276733863211287144280134743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184489242140858096186756495 276733863211287144280134743)
  ·
    refine ⟨415100794816930716420202115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276733863211287144280134743 415100794816930716420202115)
    ·
      refine ⟨622651192225396074630303173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415100794816930716420202115 622651192225396074630303173)
      ·
        refine ⟨116747098542261763993181845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 622651192225396074630303173 116747098542261763993181845)
        ·
          refine ⟨5472520244168520187180399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116747098542261763993181845 5472520244168520187180399)
          ·
            refine ⟨8208780366252780280770599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472520244168520187180399 8208780366252780280770599)
            ·
              refine ⟨12313170549379170421155899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208780366252780280770599 12313170549379170421155899)
              ·
                refine ⟨18469755824068755631733849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12313170549379170421155899 18469755824068755631733849)
                ·
                  refine ⟨13852316868051566723800387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18469755824068755631733849 13852316868051566723800387)
                  ·
                    refine ⟨20778475302077350085700581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13852316868051566723800387 20778475302077350085700581)
                    ·
                      refine ⟨3895964119139503141068859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20778475302077350085700581 3895964119139503141068859)
                      ·
                        rfl

theorem cell23_7587363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_7587363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587363 prefixEnd_7587363 := by exact prefixLift 7587363
  have htrace : WordTrace (prefixWord ++ tailWord_7587363) baseStart_7587363 baseEnd_7587363 := by
    simpa [prefixWord, tailWord_7587363, baseEnd_7587363] using wordTrace_append hprefix tailTrace_7587363
  have hstable : (prefixWord ++ tailWord_7587363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587363).length < 2 ^ (prefixWord ++ tailWord_7587363).sum := by decide
  have hdescent : baseEnd_7587363 < baseStart_7587363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587439 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 3]
def baseStart_7587439 : Nat := 118140960795 + 7587439 * 2 ^ 59
def prefixEnd_7587439 : Nat := 4983230072969 + 3 ^ 40 * 7587439 * 2
def baseEnd_7587439 : Nat := 3896003143669244843718509

theorem tailTrace_7587439 : CollatzResearch.WordTrace tailWord_7587439 prefixEnd_7587439 3896003143669244843718509 := by
  unfold tailWord_7587439
  simp only [CollatzResearch.WordTrace]
  refine ⟨276736635159011809259901371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184491090106007872839934247 276736635159011809259901371)
  ·
    refine ⟨415104952738517713889852057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276736635159011809259901371 415104952738517713889852057)
    ·
      refine ⟨311328714553888285417389043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415104952738517713889852057 311328714553888285417389043)
      ·
        refine ⟨466993071830832428126083565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311328714553888285417389043 466993071830832428126083565)
        ·
          refine ⟨175122401936562160547281337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466993071830832428126083565 175122401936562160547281337)
          ·
            refine ⟨131341801452421620410461003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175122401936562160547281337 131341801452421620410461003)
            ·
              refine ⟨197012702178632430615691505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131341801452421620410461003 197012702178632430615691505)
              ·
                refine ⟨147759526633974322961768629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197012702178632430615691505 147759526633974322961768629)
                ·
                  refine ⟨13852455621935092777665809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147759526633974322961768629 13852455621935092777665809)
                  ·
                    refine ⟨10389341716451319583249357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13852455621935092777665809 10389341716451319583249357)
                    ·
                      refine ⟨3896003143669244843718509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10389341716451319583249357 3896003143669244843718509)
                      ·
                        rfl

theorem cell23_7587439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_7587439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587439 prefixEnd_7587439 := by exact prefixLift 7587439
  have htrace : WordTrace (prefixWord ++ tailWord_7587439) baseStart_7587439 baseEnd_7587439 := by
    simpa [prefixWord, tailWord_7587439, baseEnd_7587439] using wordTrace_append hprefix tailTrace_7587439
  have hstable : (prefixWord ++ tailWord_7587439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587439).length < 2 ^ (prefixWord ++ tailWord_7587439).sum := by decide
  have hdescent : baseEnd_7587439 < baseStart_7587439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587463 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 2, 4]
def baseStart_7587463 : Nat := 118140960795 + 7587463 * 2 ^ 59
def prefixEnd_7587463 : Nat := 4983230072969 + 3 ^ 40 * 7587463 * 2
def baseEnd_7587463 : Nat := 1298671822401650916606133

theorem tailTrace_7587463 : CollatzResearch.WordTrace tailWord_7587463 prefixEnd_7587463 1298671822401650916606133 := by
  unfold tailWord_7587463
  simp only [CollatzResearch.WordTrace]
  refine ⟨276737510510924861358775043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184491673673949907572516695 276737510510924861358775043)
  ·
    refine ⟨415106265766387292038162565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276737510510924861358775043 415106265766387292038162565)
    ·
      refine ⟨77832424831197617257155481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415106265766387292038162565 77832424831197617257155481)
      ·
        refine ⟨58374318623398212942866611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77832424831197617257155481 58374318623398212942866611)
        ·
          refine ⟨87561477935097319414299917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58374318623398212942866611 87561477935097319414299917)
          ·
            refine ⟨32835554225661494780362469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87561477935097319414299917 32835554225661494780362469)
            ·
              refine ⟨6156666417311530271317963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32835554225661494780362469 6156666417311530271317963)
              ·
                refine ⟨9234999625967295406976945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156666417311530271317963 9234999625967295406976945)
                ·
                  refine ⟨6926249719475471555232709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9234999625967295406976945 6926249719475471555232709)
                  ·
                    refine ⟨1298671822401650916606133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6926249719475471555232709 1298671822401650916606133)
                    ·
                      rfl

theorem cell23_7587463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_7587463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587463 prefixEnd_7587463 := by exact prefixLift 7587463
  have htrace : WordTrace (prefixWord ++ tailWord_7587463) baseStart_7587463 baseEnd_7587463 := by
    simpa [prefixWord, tailWord_7587463, baseEnd_7587463] using wordTrace_append hprefix tailTrace_7587463
  have hstable : (prefixWord ++ tailWord_7587463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587463).length < 2 ^ (prefixWord ++ tailWord_7587463).sum := by decide
  have hdescent : baseEnd_7587463 < baseStart_7587463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587490 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_7587490 : Nat := 118140960795 + 7587490 * 2 ^ 59
def prefixEnd_7587490 : Nat := 4983230072969 + 3 ^ 40 * 7587490 * 2
def baseEnd_7587490 : Nat := 3896029331182624144180775

theorem tailTrace_7587490 : CollatzResearch.WordTrace tailWord_7587490 prefixEnd_7587490 3896029331182624144180775 := by
  unfold tailWord_7587490
  simp only [CollatzResearch.WordTrace]
  refine ⟨69184623820456761242501981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184492330187884696646671949 69184623820456761242501981)
  ·
    refine ⟨25944233932671285465938243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69184623820456761242501981 25944233932671285465938243)
    ·
      refine ⟨38916350899006928198907365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25944233932671285465938243 38916350899006928198907365)
      ·
        refine ⟨7296815793563799037295131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38916350899006928198907365 7296815793563799037295131)
        ·
          refine ⟨10945223690345698555942697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296815793563799037295131 10945223690345698555942697)
          ·
            refine ⟨8208917767759273916957023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10945223690345698555942697 8208917767759273916957023)
            ·
              refine ⟨12313376651638910875435535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208917767759273916957023 12313376651638910875435535)
              ·
                refine ⟨18470064977458366313153303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12313376651638910875435535 18470064977458366313153303)
                ·
                  refine ⟨27705097466187549469729955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18470064977458366313153303 27705097466187549469729955)
                  ·
                    refine ⟨41557646199281324204594933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27705097466187549469729955 41557646199281324204594933)
                    ·
                      refine ⟨3896029331182624144180775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41557646199281324204594933 3896029331182624144180775)
                      ·
                        rfl

theorem cell23_7587490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_7587490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587490 prefixEnd_7587490 := by exact prefixLift 7587490
  have htrace : WordTrace (prefixWord ++ tailWord_7587490) baseStart_7587490 baseEnd_7587490 := by
    simpa [prefixWord, tailWord_7587490, baseEnd_7587490] using wordTrace_append hprefix tailTrace_7587490
  have hstable : (prefixWord ++ tailWord_7587490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587490).length < 2 ^ (prefixWord ++ tailWord_7587490).sum := by decide
  have hdescent : baseEnd_7587490 < baseStart_7587490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587503 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 3]
def baseStart_7587503 : Nat := 118140960795 + 7587503 * 2 ^ 59
def prefixEnd_7587503 : Nat := 4983230072969 + 3 ^ 40 * 7587503 * 2
def baseEnd_7587503 : Nat := 3896036006431132593318215

theorem tailTrace_7587503 : CollatzResearch.WordTrace tailWord_7587503 prefixEnd_7587503 3896036006431132593318215 := by
  unfold tailWord_7587503
  simp only [CollatzResearch.WordTrace]
  refine ⟨276738969430779948190231163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184492646287186632126820775 276738969430779948190231163)
  ·
    refine ⟨415108454146169922285346745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276738969430779948190231163 415108454146169922285346745)
    ·
      refine ⟨311331340609627441714010059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415108454146169922285346745 311331340609627441714010059)
      ·
        refine ⟨466997010914441162571015089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311331340609627441714010059 466997010914441162571015089)
        ·
          refine ⟨350247758185830871928261317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466997010914441162571015089 350247758185830871928261317)
          ·
            refine ⟨65671454659843288486548997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350247758185830871928261317 65671454659843288486548997)
            ·
              refine ⟨12313397748720616591227937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65671454659843288486548997 12313397748720616591227937)
              ·
                refine ⟨9235048311540462443420953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12313397748720616591227937 9235048311540462443420953)
                ·
                  refine ⟨6926286233655346832565715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9235048311540462443420953 6926286233655346832565715)
                  ·
                    refine ⟨10389429350483020248848573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6926286233655346832565715 10389429350483020248848573)
                    ·
                      refine ⟨3896036006431132593318215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10389429350483020248848573 3896036006431132593318215)
                      ·
                        rfl

theorem cell23_7587503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 3].length) (baseStart_7587503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587503 prefixEnd_7587503 := by exact prefixLift 7587503
  have htrace : WordTrace (prefixWord ++ tailWord_7587503) baseStart_7587503 baseEnd_7587503 := by
    simpa [prefixWord, tailWord_7587503, baseEnd_7587503] using wordTrace_append hprefix tailTrace_7587503
  have hstable : (prefixWord ++ tailWord_7587503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587503).length < 2 ^ (prefixWord ++ tailWord_7587503).sum := by decide
  have hdescent : baseEnd_7587503 < baseStart_7587503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587519 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 2, 6]
def baseStart_7587519 : Nat := 118140960795 + 7587519 * 2 ^ 59
def prefixEnd_7587519 : Nat := 4983230072969 + 3 ^ 40 * 7587519 * 2
def baseEnd_7587519 : Nat := 1298681407373868176906047

theorem tailTrace_7587519 : CollatzResearch.WordTrace tailWord_7587519 prefixEnd_7587519 1298681407373868176906047 := by
  unfold tailWord_7587519
  simp only [CollatzResearch.WordTrace]
  refine ⟨276739552998721982922813611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184493035332481321948542407 276739552998721982922813611)
  ·
    refine ⟨415109329498082974384220417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276739552998721982922813611 415109329498082974384220417)
    ·
      refine ⟨311331997123562230788165313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415109329498082974384220417 311331997123562230788165313)
      ·
        refine ⟨233498997842671673091123985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311331997123562230788165313 233498997842671673091123985)
        ·
          refine ⟨175124248382003754818342989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233498997842671673091123985 175124248382003754818342989)
          ·
            refine ⟨65671593143251408056878621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175124248382003754818342989 65671593143251408056878621)
            ·
              refine ⟨24626847428719278021329483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65671593143251408056878621 24626847428719278021329483)
              ·
                refine ⟨36940271143078917031994225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24626847428719278021329483 36940271143078917031994225)
                ·
                  refine ⟨27705203357309187773995669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36940271143078917031994225 27705203357309187773995669)
                  ·
                    refine ⟨1298681407373868176906047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27705203357309187773995669 1298681407373868176906047)
                    ·
                      rfl

theorem cell23_7587519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_7587519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587519 prefixEnd_7587519 := by exact prefixLift 7587519
  have htrace : WordTrace (prefixWord ++ tailWord_7587519) baseStart_7587519 baseEnd_7587519 := by
    simpa [prefixWord, tailWord_7587519, baseEnd_7587519] using wordTrace_append hprefix tailTrace_7587519
  have hstable : (prefixWord ++ tailWord_7587519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587519).length < 2 ^ (prefixWord ++ tailWord_7587519).sum := by decide
  have hdescent : baseEnd_7587519 < baseStart_7587519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587543 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 4, 2, 2]
def baseStart_7587543 : Nat := 118140960795 + 7587543 * 2 ^ 59
def prefixEnd_7587543 : Nat := 4983230072969 + 3 ^ 40 * 7587543 * 2
def baseEnd_7587543 : Nat := 3896056545657312436818031

theorem tailTrace_7587543 : CollatzResearch.WordTrace tailWord_7587543 prefixEnd_7587543 3896056545657312436818031 := by
  unfold tailWord_7587543
  simp only [CollatzResearch.WordTrace]
  refine ⟨276740428350635035021687283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184493618900423356681124855 276740428350635035021687283)
  ·
    refine ⟨415110642525952552532530925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276740428350635035021687283 415110642525952552532530925)
    ·
      refine ⟨155666490947232207199699097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415110642525952552532530925 155666490947232207199699097)
      ·
        refine ⟨116749868210424155399774323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155666490947232207199699097 116749868210424155399774323)
        ·
          refine ⟨175124802315636233099661485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116749868210424155399774323 175124802315636233099661485)
          ·
            refine ⟨65671800868363587412373057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175124802315636233099661485 65671800868363587412373057)
            ·
              refine ⟨49253850651272690559279793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65671800868363587412373057 49253850651272690559279793)
              ·
                refine ⟨36940387988454517919459845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49253850651272690559279793 36940387988454517919459845)
                ·
                  refine ⟨6926322747835222109898721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36940387988454517919459845 6926322747835222109898721)
                  ·
                    refine ⟨5194742060876416582424041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6926322747835222109898721 5194742060876416582424041)
                    ·
                      refine ⟨3896056545657312436818031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194742060876416582424041 3896056545657312436818031)
                      ·
                        rfl

theorem cell23_7587543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_7587543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587543 prefixEnd_7587543 := by exact prefixLift 7587543
  have htrace : WordTrace (prefixWord ++ tailWord_7587543) baseStart_7587543 baseEnd_7587543 := by
    simpa [prefixWord, tailWord_7587543, baseEnd_7587543] using wordTrace_append hprefix tailTrace_7587543
  have hstable : (prefixWord ++ tailWord_7587543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587543).length < 2 ^ (prefixWord ++ tailWord_7587543).sum := by decide
  have hdescent : baseEnd_7587543 < baseStart_7587543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587560 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_7587560 : Nat := 118140960795 + 7587560 * 2 ^ 59
def prefixEnd_7587560 : Nat := 4983230072969 + 3 ^ 40 * 7587560 * 2
def baseEnd_7587560 : Nat := 3896065274828438870305453

theorem tailTrace_7587560 : CollatzResearch.WordTrace tailWord_7587560 prefixEnd_7587560 3896065274828438870305453 := by
  unfold tailWord_7587560
  simp only [CollatzResearch.WordTrace]
  refine ⟨138370524195786723462528067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184494032261048964616704089 138370524195786723462528067)
  ·
    refine ⟨207555786293680085193792101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138370524195786723462528067 207555786293680085193792101)
    ·
      refine ⟨38916709930065015973836019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207555786293680085193792101 38916709930065015973836019)
      ·
        refine ⟨58375064895097523960754029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38916709930065015973836019 58375064895097523960754029)
        ·
          refine ⟨21890649335661571485282761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58375064895097523960754029 21890649335661571485282761)
          ·
            refine ⟨16417987001746178613962071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21890649335661571485282761 16417987001746178613962071)
            ·
              refine ⟨24626980502619267920943107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16417987001746178613962071 24626980502619267920943107)
              ·
                refine ⟨36940470753928901881414661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24626980502619267920943107 36940470753928901881414661)
                ·
                  refine ⟨6926338266361669102765249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36940470753928901881414661 6926338266361669102765249)
                  ·
                    refine ⟨5194753699771251827073937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6926338266361669102765249 5194753699771251827073937)
                    ·
                      refine ⟨3896065274828438870305453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194753699771251827073937 3896065274828438870305453)
                      ·
                        rfl

theorem cell23_7587560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_7587560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587560 prefixEnd_7587560 := by exact prefixLift 7587560
  have htrace : WordTrace (prefixWord ++ tailWord_7587560) baseStart_7587560 baseEnd_7587560 := by
    simpa [prefixWord, tailWord_7587560, baseEnd_7587560] using wordTrace_append hprefix tailTrace_7587560
  have hstable : (prefixWord ++ tailWord_7587560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587560).length < 2 ^ (prefixWord ++ tailWord_7587560).sum := by decide
  have hdescent : baseEnd_7587560 < baseStart_7587560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587566 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_7587566 : Nat := 118140960795 + 7587566 * 2 ^ 59
def prefixEnd_7587566 : Nat := 4983230072969 + 3 ^ 40 * 7587566 * 2
def baseEnd_7587566 : Nat := 432896483968040649647825

theorem tailTrace_7587566 : CollatzResearch.WordTrace tailWord_7587566 prefixEnd_7587566 432896483968040649647825 := by
  unfold tailWord_7587566
  simp only [CollatzResearch.WordTrace]
  refine ⟨34592658403693963743721819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184494178153034473299849701 34592658403693963743721819)
  ·
    refine ⟨51888987605540945615582729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34592658403693963743721819 51888987605540945615582729)
    ·
      refine ⟨38916740704155709211687047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51888987605540945615582729 38916740704155709211687047)
      ·
        refine ⟨58375111056233563817530571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38916740704155709211687047 58375111056233563817530571)
        ·
          refine ⟨87562666584350345726295857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58375111056233563817530571 87562666584350345726295857)
          ·
            refine ⟨65671999938262759294721893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87562666584350345726295857 65671999938262759294721893)
            ·
              refine ⟨12313499988424267367760355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65671999938262759294721893 12313499988424267367760355)
              ·
                refine ⟨18470249982636401051640533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12313499988424267367760355 18470249982636401051640533)
                ·
                  refine ⟨432896483968040649647825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18470249982636401051640533 432896483968040649647825)
                  ·
                    rfl

theorem cell23_7587566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_7587566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587566 prefixEnd_7587566 := by exact prefixLift 7587566
  have htrace : WordTrace (prefixWord ++ tailWord_7587566) baseStart_7587566 baseEnd_7587566 := by
    simpa [prefixWord, tailWord_7587566, baseEnd_7587566] using wordTrace_append hprefix tailTrace_7587566
  have hstable : (prefixWord ++ tailWord_7587566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587566).length < 2 ^ (prefixWord ++ tailWord_7587566).sum := by decide
  have hdescent : baseEnd_7587566 < baseStart_7587566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587579 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 6, 5]
def baseStart_7587579 : Nat := 118140960795 + 7587579 * 2 ^ 59
def prefixEnd_7587579 : Nat := 4983230072969 + 3 ^ 40 * 7587579 * 2
def baseEnd_7587579 : Nat := 1298691676986958098655955

theorem tailTrace_7587579 : CollatzResearch.WordTrace tailWord_7587579 prefixEnd_7587579 1298691676986958098655955 := by
  unfold tailWord_7587579
  simp only [CollatzResearch.WordTrace]
  refine ⟨276741741378504613169997791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184494494252336408779998527 276741741378504613169997791)
  ·
    refine ⟨415112612067756919754996687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276741741378504613169997791 415112612067756919754996687)
    ·
      refine ⟨622668918101635379632495031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415112612067756919754996687 622668918101635379632495031)
      ·
        refine ⟨934003377152453069448742547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622668918101635379632495031 934003377152453069448742547)
        ·
          refine ⟨1401005065728679604173113821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934003377152453069448742547 1401005065728679604173113821)
          ·
            refine ⟨525376899648254851564917683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1401005065728679604173113821 525376899648254851564917683)
            ·
              refine ⟨788065349472382277347376525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525376899648254851564917683 788065349472382277347376525)
              ·
                refine ⟨295524506052143354005266197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 788065349472382277347376525 295524506052143354005266197)
                ·
                  refine ⟨13852711221194219718996853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 295524506052143354005266197 13852711221194219718996853)
                  ·
                    refine ⟨1298691676986958098655955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13852711221194219718996853 1298691676986958098655955)
                    ·
                      rfl

theorem cell23_7587579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 5].length) (baseStart_7587579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587579 prefixEnd_7587579 := by exact prefixLift 7587579
  have htrace : WordTrace (prefixWord ++ tailWord_7587579) baseStart_7587579 baseEnd_7587579 := by
    simpa [prefixWord, tailWord_7587579, baseEnd_7587579] using wordTrace_append hprefix tailTrace_7587579
  have hstable : (prefixWord ++ tailWord_7587579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587579).length < 2 ^ (prefixWord ++ tailWord_7587579).sum := by decide
  have hdescent : baseEnd_7587579 < baseStart_7587579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587589 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_7587589 : Nat := 118140960795 + 7587589 * 2 ^ 59
def prefixEnd_7587589 : Nat := 4983230072969 + 3 ^ 40 * 7587589 * 2
def baseEnd_7587589 : Nat := 3896080165767419256842819

theorem tailTrace_7587589 : CollatzResearch.WordTrace tailWord_7587589 prefixEnd_7587589 3896080165767419256842819 := by
  unfold tailWord_7587589
  simp only [CollatzResearch.WordTrace]
  refine ⟨276742106108468384877861821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184494737405645589918574547 276742106108468384877861821)
  ·
    refine ⟨103778289790675644329198183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276742106108468384877861821 103778289790675644329198183)
    ·
      refine ⟨155667434686013466493797275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103778289790675644329198183 155667434686013466493797275)
      ·
        refine ⟨233501152029020199740695913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155667434686013466493797275 233501152029020199740695913)
        ·
          refine ⟨175125864021765149805521935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233501152029020199740695913 175125864021765149805521935)
          ·
            refine ⟨262688796032647724708282903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175125864021765149805521935 262688796032647724708282903)
            ·
              refine ⟨394033194048971587062424355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262688796032647724708282903 394033194048971587062424355)
              ·
                refine ⟨591049791073457380593636533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394033194048971587062424355 591049791073457380593636533)
                ·
                  refine ⟨55410917913136629430653425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 591049791073457380593636533 55410917913136629430653425)
                  ·
                    refine ⟨41558188434852472072990069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55410917913136629430653425 41558188434852472072990069)
                    ·
                      refine ⟨3896080165767419256842819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41558188434852472072990069 3896080165767419256842819)
                      ·
                        rfl

theorem cell23_7587589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_7587589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587589 prefixEnd_7587589 := by exact prefixLift 7587589
  have htrace : WordTrace (prefixWord ++ tailWord_7587589) baseStart_7587589 baseEnd_7587589 := by
    simpa [prefixWord, tailWord_7587589, baseEnd_7587589] using wordTrace_append hprefix tailTrace_7587589
  have hstable : (prefixWord ++ tailWord_7587589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587589).length < 2 ^ (prefixWord ++ tailWord_7587589).sum := by decide
  have hdescent : baseEnd_7587589 < baseStart_7587589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587639 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 10]
def baseStart_7587639 : Nat := 118140960795 + 7587639 * 2 ^ 59
def prefixEnd_7587639 : Nat := 4983230072969 + 3 ^ 40 * 7587639 * 2
def baseEnd_7587639 : Nat := 432900648866682673468621

theorem tailTrace_7587639 : CollatzResearch.WordTrace tailWord_7587639 prefixEnd_7587639 432900648866682673468621 := by
  unfold tailWord_7587639
  simp only [CollatzResearch.WordTrace]
  refine ⟨276743929758287243417181971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184495953172191495611454647 276743929758287243417181971)
  ·
    refine ⟨415115894637430865125772957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276743929758287243417181971 415115894637430865125772957)
    ·
      refine ⟨155668460489036574422164859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415115894637430865125772957 155668460489036574422164859)
      ·
        refine ⟨233502690733554861633247289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155668460489036574422164859 233502690733554861633247289)
        ·
          refine ⟨175127018050166146224935467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233502690733554861633247289 175127018050166146224935467)
          ·
            refine ⟨262690527075249219337403201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175127018050166146224935467 262690527075249219337403201)
            ·
              refine ⟨197017895306436914503052401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262690527075249219337403201 197017895306436914503052401)
              ·
                refine ⟨147763421479827685877289301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197017895306436914503052401 147763421479827685877289301)
                ·
                  refine ⟨432900648866682673468621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 147763421479827685877289301 432900648866682673468621)
                  ·
                    rfl

theorem cell23_7587639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 10].length) (baseStart_7587639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587639 prefixEnd_7587639 := by exact prefixLift 7587639
  have htrace : WordTrace (prefixWord ++ tailWord_7587639) baseStart_7587639 baseEnd_7587639 := by
    simpa [prefixWord, tailWord_7587639, baseEnd_7587639] using wordTrace_append hprefix tailTrace_7587639
  have hstable : (prefixWord ++ tailWord_7587639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587639).length < 2 ^ (prefixWord ++ tailWord_7587639).sum := by decide
  have hdescent : baseEnd_7587639 < baseStart_7587639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587653 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_7587653 : Nat := 118140960795 + 7587653 * 2 ^ 59
def prefixEnd_7587653 : Nat := 4983230072969 + 3 ^ 40 * 7587653 * 2
def baseEnd_7587653 : Nat := 3896113028529307006442525

theorem tailTrace_7587653 : CollatzResearch.WordTrace tailWord_7587653 prefixEnd_7587653 3896113028529307006442525 := by
  unfold tailWord_7587653
  simp only [CollatzResearch.WordTrace]
  refine ⟨276744440380236523808191613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184496293586824349205461075 276744440380236523808191613)
  ·
    refine ⟨103779165142588696428071855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276744440380236523808191613 103779165142588696428071855)
    ·
      refine ⟨155668747713883044642107783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103779165142588696428071855 155668747713883044642107783)
      ·
        refine ⟨233503121570824566963161675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155668747713883044642107783 233503121570824566963161675)
        ·
          refine ⟨350254682356236850444742513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233503121570824566963161675 350254682356236850444742513)
          ·
            refine ⟨262691011767177637833556885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350254682356236850444742513 262691011767177637833556885)
            ·
              refine ⟨12313641176586451773447979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 262691011767177637833556885 12313641176586451773447979)
              ·
                refine ⟨18470461764879677660171969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12313641176586451773447979 18470461764879677660171969)
                ·
                  refine ⟨13852846323659758245128977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18470461764879677660171969 13852846323659758245128977)
                  ·
                    refine ⟨10389634742744818683846733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13852846323659758245128977 10389634742744818683846733)
                    ·
                      refine ⟨3896113028529307006442525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10389634742744818683846733 3896113028529307006442525)
                      ·
                        rfl

theorem cell23_7587653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_7587653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587653 prefixEnd_7587653 := by exact prefixLift 7587653
  have htrace : WordTrace (prefixWord ++ tailWord_7587653) baseStart_7587653 baseEnd_7587653 := by
    simpa [prefixWord, tailWord_7587653, baseEnd_7587653] using wordTrace_append hprefix tailTrace_7587653
  have hstable : (prefixWord ++ tailWord_7587653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587653).length < 2 ^ (prefixWord ++ tailWord_7587653).sum := by decide
  have hdescent : baseEnd_7587653 < baseStart_7587653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587717 : List Nat := [1, 3, 1, 1, 3, 2, 4, 3, 1, 1, 3]
def baseStart_7587717 : Nat := 118140960795 + 7587717 * 2 ^ 59
def prefixEnd_7587717 : Nat := 4983230072969 + 3 ^ 40 * 7587717 * 2
def baseEnd_7587717 : Nat := 3896145891291194756042231

theorem tailTrace_7587717 : CollatzResearch.WordTrace tailWord_7587717 prefixEnd_7587717 3896145891291194756042231 := by
  unfold tailWord_7587717
  simp only [CollatzResearch.WordTrace]
  refine ⟨276746774652004662738521405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184497849768003108492347603 276746774652004662738521405)
  ·
    refine ⟨103780040494501748526945527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276746774652004662738521405 103780040494501748526945527)
    ·
      refine ⟨155670060741752622790418291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103780040494501748526945527 155670060741752622790418291)
      ·
        refine ⟨233505091112628934185627437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155670060741752622790418291 233505091112628934185627437)
        ·
          refine ⟨87564409167235850319610289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233505091112628934185627437 87564409167235850319610289)
          ·
            refine ⟨65673306875426887739707717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87564409167235850319610289 65673306875426887739707717)
            ·
              refine ⟨12313745039142541451195197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65673306875426887739707717 12313745039142541451195197)
              ·
                refine ⟨4617654389678453044198199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12313745039142541451195197 4617654389678453044198199)
                ·
                  refine ⟨6926481584517679566297299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4617654389678453044198199 6926481584517679566297299)
                  ·
                    refine ⟨10389722376776519349445949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6926481584517679566297299 10389722376776519349445949)
                    ·
                      refine ⟨3896145891291194756042231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10389722376776519349445949 3896145891291194756042231)
                      ·
                        rfl

theorem cell23_7587717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 1, 3].length) (baseStart_7587717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587717 prefixEnd_7587717 := by exact prefixLift 7587717
  have htrace : WordTrace (prefixWord ++ tailWord_7587717) baseStart_7587717 baseEnd_7587717 := by
    simpa [prefixWord, tailWord_7587717, baseEnd_7587717] using wordTrace_append hprefix tailTrace_7587717
  have hstable : (prefixWord ++ tailWord_7587717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587717).length < 2 ^ (prefixWord ++ tailWord_7587717).sum := by decide
  have hdescent : baseEnd_7587717 < baseStart_7587717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587720 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 1, 5]
def baseStart_7587720 : Nat := 118140960795 + 7587720 * 2 ^ 59
def prefixEnd_7587720 : Nat := 4983230072969 + 3 ^ 40 * 7587720 * 2
def baseEnd_7587720 : Nat := 1298715810577719414768239

theorem tailTrace_7587720 : CollatzResearch.WordTrace tailWord_7587720 prefixEnd_7587720 1298715810577719414768239 := by
  unfold tailWord_7587720
  simp only [CollatzResearch.WordTrace]
  refine ⟨138373442035496897125440307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184497922713995862833920409 138373442035496897125440307)
  ·
    refine ⟨207560163053245345688160461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138373442035496897125440307 207560163053245345688160461)
    ·
      refine ⟨77835061144967004633060173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207560163053245345688160461 77835061144967004633060173)
      ·
        refine ⟨29188147929362626737397565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77835061144967004633060173 29188147929362626737397565)
        ·
          refine ⟨10945555473510985026524087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29188147929362626737397565 10945555473510985026524087)
          ·
            refine ⟨16418333210266477539786131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10945555473510985026524087 16418333210266477539786131)
            ·
              refine ⟨24627499815399716309679197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16418333210266477539786131 24627499815399716309679197)
              ·
                refine ⟨9235312430774893616129699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24627499815399716309679197 9235312430774893616129699)
                ·
                  refine ⟨13852968646162340424194549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9235312430774893616129699 13852968646162340424194549)
                  ·
                    refine ⟨1298715810577719414768239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13852968646162340424194549 1298715810577719414768239)
                    ·
                      rfl

theorem cell23_7587720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_7587720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587720 prefixEnd_7587720 := by exact prefixLift 7587720
  have htrace : WordTrace (prefixWord ++ tailWord_7587720) baseStart_7587720 baseEnd_7587720 := by
    simpa [prefixWord, tailWord_7587720, baseEnd_7587720] using wordTrace_append hprefix tailTrace_7587720
  have hstable : (prefixWord ++ tailWord_7587720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587720).length < 2 ^ (prefixWord ++ tailWord_7587720).sum := by decide
  have hdescent : baseEnd_7587720 < baseStart_7587720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587733 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_7587733 : Nat := 118140960795 + 7587733 * 2 ^ 59
def prefixEnd_7587733 : Nat := 4983230072969 + 3 ^ 40 * 7587733 * 2
def baseEnd_7587733 : Nat := 1298718035660555564480719

theorem tailTrace_7587733 : CollatzResearch.WordTrace tailWord_7587733 prefixEnd_7587733 1298718035660555564480719 := by
  unfold tailWord_7587733
  simp only [CollatzResearch.WordTrace]
  refine ⟨276747358219946697471103853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184498238813297798314069235 276747358219946697471103853)
  ·
    refine ⟨103780259332480011551663945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276747358219946697471103853 103780259332480011551663945)
    ·
      refine ⟨77835194499360008663747959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103780259332480011551663945 77835194499360008663747959)
      ·
        refine ⟨116752791749040012995621939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77835194499360008663747959 116752791749040012995621939)
        ·
          refine ⟨175129187623560019493432909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116752791749040012995621939 175129187623560019493432909)
          ·
            refine ⟨65673445358835007310037341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175129187623560019493432909 65673445358835007310037341)
            ·
              refine ⟨24627542009563127741264003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65673445358835007310037341 24627542009563127741264003)
              ·
                refine ⟨36941313014344691611896005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24627542009563127741264003 36941313014344691611896005)
                ·
                  refine ⟨6926496190189629677230501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36941313014344691611896005 6926496190189629677230501)
                  ·
                    refine ⟨1298718035660555564480719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6926496190189629677230501 1298718035660555564480719)
                    ·
                      rfl

theorem cell23_7587733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_7587733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587733 prefixEnd_7587733 := by exact prefixLift 7587733
  have htrace : WordTrace (prefixWord ++ tailWord_7587733) baseStart_7587733 baseEnd_7587733 := by
    simpa [prefixWord, tailWord_7587733, baseEnd_7587733] using wordTrace_append hprefix tailTrace_7587733
  have hstable : (prefixWord ++ tailWord_7587733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587733).length < 2 ^ (prefixWord ++ tailWord_7587733).sum := by decide
  have hdescent : baseEnd_7587733 < baseStart_7587733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587790 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_7587790 : Nat := 118140960795 + 7587790 * 2 ^ 59
def prefixEnd_7587790 : Nat := 4983230072969 + 3 ^ 40 * 7587790 * 2
def baseEnd_7587790 : Nat := 3896183375378972970429395

theorem tailTrace_7587790 : CollatzResearch.WordTrace tailWord_7587790 prefixEnd_7587790 3896183375378972970429395 := by
  unfold tailWord_7587790
  simp only [CollatzResearch.WordTrace]
  refine ⟨34593679647592524525741103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184499624787160130803952549 34593679647592524525741103)
  ·
    refine ⟨51890519471388786788611655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34593679647592524525741103 51890519471388786788611655)
    ·
      refine ⟨77835779207083180182917483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51890519471388786788611655 77835779207083180182917483)
      ·
        refine ⟨116753668810624770274376225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77835779207083180182917483 116753668810624770274376225)
        ·
          refine ⟨87565251607968577705782169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116753668810624770274376225 87565251607968577705782169)
          ·
            refine ⟨65673938705976433279336627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87565251607968577705782169 65673938705976433279336627)
            ·
              refine ⟨98510908058964649919004941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65673938705976433279336627 98510908058964649919004941)
              ·
                refine ⟨36941590522111743719626853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98510908058964649919004941 36941590522111743719626853)
                ·
                  refine ⟨6926548222895951947430035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36941590522111743719626853 6926548222895951947430035)
                  ·
                    refine ⟨10389822334343927921145053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6926548222895951947430035 10389822334343927921145053)
                    ·
                      refine ⟨3896183375378972970429395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10389822334343927921145053 3896183375378972970429395)
                      ·
                        rfl

theorem cell23_7587790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_7587790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587790 prefixEnd_7587790 := by exact prefixLift 7587790
  have htrace : WordTrace (prefixWord ++ tailWord_7587790) baseStart_7587790 baseEnd_7587790 := by
    simpa [prefixWord, tailWord_7587790, baseEnd_7587790] using wordTrace_append hprefix tailTrace_7587790
  have hstable : (prefixWord ++ tailWord_7587790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587790).length < 2 ^ (prefixWord ++ tailWord_7587790).sum := by decide
  have hdescent : baseEnd_7587790 < baseStart_7587790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587800 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 3, 3, 2]
def baseStart_7587800 : Nat := 118140960795 + 7587800 * 2 ^ 59
def prefixEnd_7587800 : Nat := 4983230072969 + 3 ^ 40 * 7587800 * 2
def baseEnd_7587800 : Nat := 3896188510185517931304349

theorem tailTrace_7587800 : CollatzResearch.WordTrace tailWord_7587800 prefixEnd_7587800 3896188510185517931304349 := by
  unfold tailWord_7587800
  simp only [CollatzResearch.WordTrace]
  refine ⟨138374900955351983956896427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184499867940469311942528569 138374900955351983956896427)
  ·
    refine ⟨207562351433027975935344641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138374900955351983956896427 207562351433027975935344641)
    ·
      refine ⟨155671763574770981951508481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207562351433027975935344641 155671763574770981951508481)
      ·
        refine ⟨116753822681078236463631361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155671763574770981951508481 116753822681078236463631361)
        ·
          refine ⟨87565367010808677347723521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116753822681078236463631361 87565367010808677347723521)
          ·
            refine ⟨65674025258106508010792641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87565367010808677347723521 65674025258106508010792641)
            ·
              refine ⟨49255518943579881008094481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65674025258106508010792641 49255518943579881008094481)
              ·
                refine ⟨36941639207684910756070861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49255518943579881008094481 36941639207684910756070861)
                ·
                  refine ⟨13853114702881841533526573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36941639207684910756070861 13853114702881841533526573)
                  ·
                    refine ⟨5194918013580690575072465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13853114702881841533526573 5194918013580690575072465)
                    ·
                      refine ⟨3896188510185517931304349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5194918013580690575072465 3896188510185517931304349)
                      ·
                        rfl

theorem cell23_7587800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_7587800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587800 prefixEnd_7587800 := by exact prefixLift 7587800
  have htrace : WordTrace (prefixWord ++ tailWord_7587800) baseStart_7587800 baseEnd_7587800 := by
    simpa [prefixWord, tailWord_7587800, baseEnd_7587800] using wordTrace_append hprefix tailTrace_7587800
  have hstable : (prefixWord ++ tailWord_7587800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587800).length < 2 ^ (prefixWord ++ tailWord_7587800).sum := by decide
  have hdescent : baseEnd_7587800 < baseStart_7587800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587807 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 3]
def baseStart_7587807 : Nat := 118140960795 + 7587807 * 2 ^ 59
def prefixEnd_7587807 : Nat := 4983230072969 + 3 ^ 40 * 7587807 * 2
def baseEnd_7587807 : Nat := 3896192104550099403916817

theorem tailTrace_7587807 : CollatzResearch.WordTrace tailWord_7587807 prefixEnd_7587807 3896192104550099403916817 := by
  unfold tailWord_7587807
  simp only [CollatzResearch.WordTrace]
  refine ⟨276750057221678608109297675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184500038147785738739531783 276750057221678608109297675)
  ·
    refine ⟨415125085832517912163946513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276750057221678608109297675 415125085832517912163946513)
    ·
      refine ⟨311343814374388434122959885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415125085832517912163946513 311343814374388434122959885)
      ·
        refine ⟨116753930390395662796109957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311343814374388434122959885 116753930390395662796109957)
        ·
          refine ⟨21891361948199186774270617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116753930390395662796109957 21891361948199186774270617)
          ·
            refine ⟨16418521461149390080702963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21891361948199186774270617 16418521461149390080702963)
            ·
              refine ⟨24627782191724085121054445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16418521461149390080702963 24627782191724085121054445)
              ·
                refine ⟨9235418321896531920395417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24627782191724085121054445 9235418321896531920395417)
                ·
                  refine ⟨6926563741422398940296563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9235418321896531920395417 6926563741422398940296563)
                  ·
                    refine ⟨10389845612133598410444845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6926563741422398940296563 10389845612133598410444845)
                    ·
                      refine ⟨3896192104550099403916817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10389845612133598410444845 3896192104550099403916817)
                      ·
                        rfl

theorem cell23_7587807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_7587807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587807 prefixEnd_7587807 := by exact prefixLift 7587807
  have htrace : WordTrace (prefixWord ++ tailWord_7587807) baseStart_7587807 baseEnd_7587807 := by
    simpa [prefixWord, tailWord_7587807, baseEnd_7587807] using wordTrace_append hprefix tailTrace_7587807
  have hstable : (prefixWord ++ tailWord_7587807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587807).length < 2 ^ (prefixWord ++ tailWord_7587807).sum := by decide
  have hdescent : baseEnd_7587807 < baseStart_7587807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587833 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_7587833 : Nat := 118140960795 + 7587833 * 2 ^ 59
def prefixEnd_7587833 : Nat := 4983230072969 + 3 ^ 40 * 7587833 * 2
def baseEnd_7587833 : Nat := 3896205455047116302191697

theorem tailTrace_7587833 : CollatzResearch.WordTrace tailWord_7587833 prefixEnd_7587833 3896205455047116302191697 := by
  unfold tailWord_7587833
  simp only [CollatzResearch.WordTrace]
  refine ⟨276751005519584414549744153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184500670346389609699829435 276751005519584414549744153)
  ·
    refine ⟨207563254139688310912308115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276751005519584414549744153 207563254139688310912308115)
    ·
      refine ⟨311344881209532466368462173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207563254139688310912308115 311344881209532466368462173)
      ·
        refine ⟨116754330453574674888173315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311344881209532466368462173 116754330453574674888173315)
        ·
          refine ⟨175131495680362012332259973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116754330453574674888173315 175131495680362012332259973)
          ·
            refine ⟨32837155440067877312298745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175131495680362012332259973 32837155440067877312298745)
            ·
              refine ⟨24627866580050907984224059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32837155440067877312298745 24627866580050907984224059)
              ·
                refine ⟨36941799870076361976336089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24627866580050907984224059 36941799870076361976336089)
                ·
                  refine ⟨27706349902557271482252067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36941799870076361976336089 27706349902557271482252067)
                  ·
                    refine ⟨41559524853835907223378101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27706349902557271482252067 41559524853835907223378101)
                    ·
                      refine ⟨3896205455047116302191697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41559524853835907223378101 3896205455047116302191697)
                      ·
                        rfl

theorem cell23_7587833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_7587833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587833 prefixEnd_7587833 := by exact prefixLift 7587833
  have htrace : WordTrace (prefixWord ++ tailWord_7587833) baseStart_7587833 baseEnd_7587833 := by
    simpa [prefixWord, tailWord_7587833, baseEnd_7587833] using wordTrace_append hprefix tailTrace_7587833
  have hstable : (prefixWord ++ tailWord_7587833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587833).length < 2 ^ (prefixWord ++ tailWord_7587833).sum := by decide
  have hdescent : baseEnd_7587833 < baseStart_7587833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587883 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 2, 5]
def baseStart_7587883 : Nat := 118140960795 + 7587883 * 2 ^ 59
def prefixEnd_7587883 : Nat := 4983230072969 + 3 ^ 40 * 7587883 * 2
def baseEnd_7587883 : Nat := 1298743709693280368855489

theorem tailTrace_7587883 : CollatzResearch.WordTrace tailWord_7587883 prefixEnd_7587883 1298743709693280368855489 := by
  unfold tailWord_7587883
  simp only [CollatzResearch.WordTrace]
  refine ⟨276752829169403273089064303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184501886112935515392709535 276752829169403273089064303)
  ·
    refine ⟨415129243754104909633596455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276752829169403273089064303 415129243754104909633596455)
    ·
      refine ⟨622693865631157364450394683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415129243754104909633596455 622693865631157364450394683)
      ·
        refine ⟨934040798446736046675592025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622693865631157364450394683 934040798446736046675592025)
        ·
          refine ⟨700530598835052035006694019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934040798446736046675592025 700530598835052035006694019)
          ·
            refine ⟨1050795898252578052510041029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700530598835052035006694019 1050795898252578052510041029)
            ·
              refine ⟨197024230922358384845632693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1050795898252578052510041029 197024230922358384845632693)
              ·
                refine ⟨18471021648971098579278065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197024230922358384845632693 18471021648971098579278065)
                ·
                  refine ⟨13853266236728323934458549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18471021648971098579278065 13853266236728323934458549)
                  ·
                    refine ⟨1298743709693280368855489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13853266236728323934458549 1298743709693280368855489)
                    ·
                      rfl

theorem cell23_7587883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 5].length) (baseStart_7587883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587883 prefixEnd_7587883 := by exact prefixLift 7587883
  have htrace : WordTrace (prefixWord ++ tailWord_7587883) baseStart_7587883 baseEnd_7587883 := by
    simpa [prefixWord, tailWord_7587883, baseEnd_7587883] using wordTrace_append hprefix tailTrace_7587883
  have hstable : (prefixWord ++ tailWord_7587883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587883).length < 2 ^ (prefixWord ++ tailWord_7587883).sum := by decide
  have hdescent : baseEnd_7587883 < baseStart_7587883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587893 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_7587893 : Nat := 118140960795 + 7587893 * 2 ^ 59
def prefixEnd_7587893 : Nat := 4983230072969 + 3 ^ 40 * 7587893 * 2
def baseEnd_7587893 : Nat := 3896236263886386067441421

theorem tailTrace_7587893 : CollatzResearch.WordTrace tailWord_7587893 prefixEnd_7587893 3896236263886386067441421 := by
  unfold tailWord_7587893
  simp only [CollatzResearch.WordTrace]
  refine ⟨276753193899367044796928333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184502129266244696531285555 276753193899367044796928333)
  ·
    refine ⟨103782447712262641798848125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276753193899367044796928333 103782447712262641798848125)
    ·
      refine ⟨38918417892098490674568047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103782447712262641798848125 38918417892098490674568047)
      ·
        refine ⟨58377626838147736011852071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38918417892098490674568047 58377626838147736011852071)
        ·
          refine ⟨87566440257221604017778107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58377626838147736011852071 87566440257221604017778107)
          ·
            refine ⟨131349660385832406026667161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87566440257221604017778107 131349660385832406026667161)
            ·
              refine ⟨98512245289374304520000371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131349660385832406026667161 98512245289374304520000371)
              ·
                refine ⟨147768367934061456780000557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98512245289374304520000371 147768367934061456780000557)
                ·
                  refine ⟨55413137975273046292500209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147768367934061456780000557 55413137975273046292500209)
                  ·
                    refine ⟨41559853481454784719375157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55413137975273046292500209 41559853481454784719375157)
                    ·
                      refine ⟨3896236263886386067441421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41559853481454784719375157 3896236263886386067441421)
                      ·
                        rfl

theorem cell23_7587893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_7587893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587893 prefixEnd_7587893 := by exact prefixLift 7587893
  have htrace : WordTrace (prefixWord ++ tailWord_7587893) baseStart_7587893 baseEnd_7587893 := by
    simpa [prefixWord, tailWord_7587893, baseEnd_7587893] using wordTrace_append hprefix tailTrace_7587893
  have hstable : (prefixWord ++ tailWord_7587893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587893).length < 2 ^ (prefixWord ++ tailWord_7587893).sum := by decide
  have hdescent : baseEnd_7587893 < baseStart_7587893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587930 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_7587930 : Nat := 118140960795 + 7587930 * 2 ^ 59
def prefixEnd_7587930 : Nat := 4983230072969 + 3 ^ 40 * 7587930 * 2
def baseEnd_7587930 : Nat := 1298751754223534140892917

theorem tailTrace_7587930 : CollatzResearch.WordTrace tailWord_7587930 prefixEnd_7587930 1298751754223534140892917 := by
  unfold tailWord_7587930
  simp only [CollatzResearch.WordTrace]
  refine ⟨69188635850058250029006311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184503028933488666744016829 69188635850058250029006311)
  ·
    refine ⟨103782953775087375043509467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69188635850058250029006311 103782953775087375043509467)
    ·
      refine ⟨155674430662631062565264201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103782953775087375043509467 155674430662631062565264201)
      ·
        refine ⟨116755822996973296923948151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155674430662631062565264201 116755822996973296923948151)
        ·
          refine ⟨175133734495459945385922227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116755822996973296923948151 175133734495459945385922227)
          ·
            refine ⟨262700601743189918078883341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175133734495459945385922227 262700601743189918078883341)
            ·
              refine ⟨98512725653696219279581253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262700601743189918078883341 98512725653696219279581253)
              ·
                refine ⟨18471136060068041114921485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98512725653696219279581253 18471136060068041114921485)
                ·
                  refine ⟨6926676022525515418095557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18471136060068041114921485 6926676022525515418095557)
                  ·
                    refine ⟨1298751754223534140892917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6926676022525515418095557 1298751754223534140892917)
                    ·
                      rfl

theorem cell23_7587930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_7587930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587930 prefixEnd_7587930 := by exact prefixLift 7587930
  have htrace : WordTrace (prefixWord ++ tailWord_7587930) baseStart_7587930 baseEnd_7587930 := by
    simpa [prefixWord, tailWord_7587930, baseEnd_7587930] using wordTrace_append hprefix tailTrace_7587930
  have hstable : (prefixWord ++ tailWord_7587930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587930).length < 2 ^ (prefixWord ++ tailWord_7587930).sum := by decide
  have hdescent : baseEnd_7587930 < baseStart_7587930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587940 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_7587940 : Nat := 118140960795 + 7587940 * 2 ^ 59
def prefixEnd_7587940 : Nat := 4983230072969 + 3 ^ 40 * 7587940 * 2
def baseEnd_7587940 : Nat := 3896260397477147383553705

theorem tailTrace_7587940 : CollatzResearch.WordTrace tailWord_7587940 prefixEnd_7587940 3896260397477147383553705 := by
  unfold tailWord_7587940
  simp only [CollatzResearch.WordTrace]
  refine ⟨138377454065098385911944637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184503272086797847882592849 138377454065098385911944637)
  ·
    refine ⟨51891545274411894716979239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138377454065098385911944637 51891545274411894716979239)
    ·
      refine ⟨77837317911617842075468859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51891545274411894716979239 77837317911617842075468859)
      ·
        refine ⟨116755976867426763113203289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77837317911617842075468859 116755976867426763113203289)
        ·
          refine ⟨87566982650570072334902467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116755976867426763113203289 87566982650570072334902467)
          ·
            refine ⟨131350473975855108502353701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87566982650570072334902467 131350473975855108502353701)
            ·
              refine ⟨24628213870472832844191319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131350473975855108502353701 24628213870472832844191319)
              ·
                refine ⟨36942320805709249266286979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24628213870472832844191319 36942320805709249266286979)
                ·
                  refine ⟨55413481208563873899430469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36942320805709249266286979 55413481208563873899430469)
                  ·
                    refine ⟨10390027726605726356143213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55413481208563873899430469 10390027726605726356143213)
                    ·
                      refine ⟨3896260397477147383553705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10390027726605726356143213 3896260397477147383553705)
                      ·
                        rfl

theorem cell23_7587940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_7587940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587940 prefixEnd_7587940 := by exact prefixLift 7587940
  have htrace : WordTrace (prefixWord ++ tailWord_7587940) baseStart_7587940 baseEnd_7587940 := by
    simpa [prefixWord, tailWord_7587940, baseEnd_7587940] using wordTrace_append hprefix tailTrace_7587940
  have hstable : (prefixWord ++ tailWord_7587940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587940).length < 2 ^ (prefixWord ++ tailWord_7587940).sum := by decide
  have hdescent : baseEnd_7587940 < baseStart_7587940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7587943 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 10]
def baseStart_7587943 : Nat := 118140960795 + 7587943 * 2 ^ 59
def prefixEnd_7587943 : Nat := 4983230072969 + 3 ^ 40 * 7587943 * 2
def baseEnd_7587943 : Nat := 432917993102123430201799

theorem tailTrace_7587943 : CollatzResearch.WordTrace tailWord_7587943 prefixEnd_7587943 432917993102123430201799 := by
  unfold tailWord_7587943
  simp only [CollatzResearch.WordTrace]
  refine ⟨276755017549185903336248483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184503345032790602224165655 276755017549185903336248483)
  ·
    refine ⟨415132526323778855004372725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276755017549185903336248483 415132526323778855004372725)
    ·
      refine ⟨38918674342854267656659943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 415132526323778855004372725 38918674342854267656659943)
      ·
        refine ⟨58378011514281401484989915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38918674342854267656659943 58378011514281401484989915)
        ·
          refine ⟨87567017271422102227484873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58378011514281401484989915 87567017271422102227484873)
          ·
            refine ⟨65675262953566576670613655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87567017271422102227484873 65675262953566576670613655)
            ·
              refine ⟨98512894430349865005920483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65675262953566576670613655 98512894430349865005920483)
              ·
                refine ⟨147769341645524797508880725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98512894430349865005920483 147769341645524797508880725)
                ·
                  refine ⟨432917993102123430201799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 147769341645524797508880725 432917993102123430201799)
                  ·
                    rfl

theorem cell23_7587943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 10].length) (baseStart_7587943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7587943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7587943 prefixEnd_7587943 := by exact prefixLift 7587943
  have htrace : WordTrace (prefixWord ++ tailWord_7587943) baseStart_7587943 baseEnd_7587943 := by
    simpa [prefixWord, tailWord_7587943, baseEnd_7587943] using wordTrace_append hprefix tailTrace_7587943
  have hstable : (prefixWord ++ tailWord_7587943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7587943).length < 2 ^ (prefixWord ++ tailWord_7587943).sum := by decide
  have hdescent : baseEnd_7587943 < baseStart_7587943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7587943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588037 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_7588037 : Nat := 118140960795 + 7588037 * 2 ^ 59
def prefixEnd_7588037 : Nat := 4983230072969 + 3 ^ 40 * 7588037 * 2
def baseEnd_7588037 : Nat := 1298770068366877834680253

theorem tailTrace_7588037 : CollatzResearch.WordTrace tailWord_7588037 prefixEnd_7588037 1298770068366877834680253 := by
  unfold tailWord_7588037
  simp only [CollatzResearch.WordTrace]
  refine ⟨276758446010845357390170365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184505630673896904926780243 276758446010845357390170365)
  ·
    refine ⟨103784417254067009021313887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276758446010845357390170365 103784417254067009021313887)
    ·
      refine ⟨155676625881100513531970831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103784417254067009021313887 155676625881100513531970831)
      ·
        refine ⟨233514938821650770297956247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155676625881100513531970831 233514938821650770297956247)
        ·
          refine ⟨350272408232476155446934371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233514938821650770297956247 350272408232476155446934371)
          ·
            refine ⟨525408612348714233170401557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350272408232476155446934371 525408612348714233170401557)
            ·
              refine ⟨24628528703845979679862573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 525408612348714233170401557 24628528703845979679862573)
              ·
                refine ⟨9235698263942242379948465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24628528703845979679862573 9235698263942242379948465)
                ·
                  refine ⟨6926773697956681784961349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9235698263942242379948465 6926773697956681784961349)
                  ·
                    refine ⟨1298770068366877834680253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6926773697956681784961349 1298770068366877834680253)
                    ·
                      rfl

theorem cell23_7588037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_7588037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588037 prefixEnd_7588037 := by exact prefixLift 7588037
  have htrace : WordTrace (prefixWord ++ tailWord_7588037) baseStart_7588037 baseEnd_7588037 := by
    simpa [prefixWord, tailWord_7588037, baseEnd_7588037] using wordTrace_append hprefix tailTrace_7588037
  have hstable : (prefixWord ++ tailWord_7588037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588037).length < 2 ^ (prefixWord ++ tailWord_7588037).sum := by decide
  have hdescent : baseEnd_7588037 < baseStart_7588037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588047 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 3]
def baseStart_7588047 : Nat := 118140960795 + 7588047 * 2 ^ 59
def prefixEnd_7588047 : Nat := 4983230072969 + 3 ^ 40 * 7588047 * 2
def baseEnd_7588047 : Nat := 3896315339907178464915713

theorem tailTrace_7588047 : CollatzResearch.WordTrace tailWord_7588047 prefixEnd_7588047 3896315339907178464915713 := by
  unfold tailWord_7588047
  simp only [CollatzResearch.WordTrace]
  refine ⟨276758810740809129098034395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184505873827206086065356263 276758810740809129098034395)
  ·
    refine ⟨415138216111213693647051593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276758810740809129098034395 415138216111213693647051593)
    ·
      refine ⟨311353662083410270235288695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415138216111213693647051593 311353662083410270235288695)
      ·
        refine ⟨467030493125115405352933043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311353662083410270235288695 467030493125115405352933043)
        ·
          refine ⟨700545739687673108029399565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467030493125115405352933043 700545739687673108029399565)
          ·
            refine ⟨262704652382877415511024837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 700545739687673108029399565 262704652382877415511024837)
            ·
              refine ⟨49257122321789515408317157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262704652382877415511024837 49257122321789515408317157)
              ·
                refine ⟨9235710435335534139059467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49257122321789515408317157 9235710435335534139059467)
                ·
                  refine ⟨13853565653003301208589201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9235710435335534139059467 13853565653003301208589201)
                  ·
                    refine ⟨10390174239752475906441901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13853565653003301208589201 10390174239752475906441901)
                    ·
                      refine ⟨3896315339907178464915713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10390174239752475906441901 3896315339907178464915713)
                      ·
                        rfl

theorem cell23_7588047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 3].length) (baseStart_7588047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588047 prefixEnd_7588047 := by exact prefixLift 7588047
  have htrace : WordTrace (prefixWord ++ tailWord_7588047) baseStart_7588047 baseEnd_7588047 := by
    simpa [prefixWord, tailWord_7588047, baseEnd_7588047] using wordTrace_append hprefix tailTrace_7588047
  have hstable : (prefixWord ++ tailWord_7588047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588047).length < 2 ^ (prefixWord ++ tailWord_7588047).sum := by decide
  have hdescent : baseEnd_7588047 < baseStart_7588047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588054 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_7588054 : Nat := 118140960795 + 7588054 * 2 ^ 59
def prefixEnd_7588054 : Nat := 4983230072969 + 3 ^ 40 * 7588054 * 2
def baseEnd_7588054 : Nat := 1298772978090586645842727

theorem tailTrace_7588054 : CollatzResearch.WordTrace tailWord_7588054 prefixEnd_7588054 1298772978090586645842727 := by
  unfold tailWord_7588054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17297441628236485580846201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184506044034522512862359477 17297441628236485580846201)
  ·
    refine ⟨12973081221177364185634651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17297441628236485580846201 12973081221177364185634651)
    ·
      refine ⟨19459621831766046278451977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12973081221177364185634651 19459621831766046278451977)
      ·
        refine ⟨14594716373824534708838983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19459621831766046278451977 14594716373824534708838983)
        ·
          refine ⟨21892074560736802063258475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14594716373824534708838983 21892074560736802063258475)
          ·
            refine ⟨32838111841105203094887713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21892074560736802063258475 32838111841105203094887713)
            ·
              refine ⟨24628583880828902321165785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32838111841105203094887713 24628583880828902321165785)
              ·
                refine ⟨18471437910621676740874339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24628583880828902321165785 18471437910621676740874339)
                ·
                  refine ⟨27707156865932515111311509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18471437910621676740874339 27707156865932515111311509)
                  ·
                    refine ⟨1298772978090586645842727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27707156865932515111311509 1298772978090586645842727)
                    ·
                      rfl

theorem cell23_7588054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_7588054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588054 prefixEnd_7588054 := by exact prefixLift 7588054
  have htrace : WordTrace (prefixWord ++ tailWord_7588054) baseStart_7588054 baseEnd_7588054 := by
    simpa [prefixWord, tailWord_7588054, baseEnd_7588054] using wordTrace_append hprefix tailTrace_7588054
  have hstable : (prefixWord ++ tailWord_7588054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588054).length < 2 ^ (prefixWord ++ tailWord_7588054).sum := by decide
  have hdescent : baseEnd_7588054 < baseStart_7588054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588061 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7588061 : Nat := 118140960795 + 7588061 * 2 ^ 59
def prefixEnd_7588061 : Nat := 4983230072969 + 3 ^ 40 * 7588061 * 2
def baseEnd_7588061 : Nat := 3896322528636341410140649

theorem tailTrace_7588061 : CollatzResearch.WordTrace tailWord_7588061 prefixEnd_7588061 3896322528636341410140649 := by
  unfold tailWord_7588061
  simp only [CollatzResearch.WordTrace]
  refine ⟨276759321362758409489044037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184506214241838939659362691 276759321362758409489044037)
  ·
    refine ⟨51892372755517201779195757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276759321362758409489044037 51892372755517201779195757)
    ·
      refine ⟨19459639783318950667198409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51892372755517201779195757 19459639783318950667198409)
      ·
        refine ⟨14594729837489213000398807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19459639783318950667198409 14594729837489213000398807)
        ·
          refine ⟨21892094756233819500598211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14594729837489213000398807 21892094756233819500598211)
          ·
            refine ⟨32838142134350729250897317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21892094756233819500598211 32838142134350729250897317)
            ·
              refine ⟨6157151650190761734543247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32838142134350729250897317 6157151650190761734543247)
              ·
                refine ⟨9235727475286142601814871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157151650190761734543247 9235727475286142601814871)
                ·
                  refine ⟨13853591212929213902722307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9235727475286142601814871 13853591212929213902722307)
                  ·
                    refine ⟨20780386819393820854083461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13853591212929213902722307 20780386819393820854083461)
                    ·
                      refine ⟨3896322528636341410140649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20780386819393820854083461 3896322528636341410140649)
                      ·
                        rfl

theorem cell23_7588061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7588061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588061 prefixEnd_7588061 := by exact prefixLift 7588061
  have htrace : WordTrace (prefixWord ++ tailWord_7588061) baseStart_7588061 baseEnd_7588061 := by
    simpa [prefixWord, tailWord_7588061, baseEnd_7588061] using wordTrace_append hprefix tailTrace_7588061
  have hstable : (prefixWord ++ tailWord_7588061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588061).length < 2 ^ (prefixWord ++ tailWord_7588061).sum := by decide
  have hdescent : baseEnd_7588061 < baseStart_7588061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588067 : List Nat := [1, 1, 1, 8, 1, 1, 10]
def baseStart_7588067 : Nat := 118140960795 + 7588067 * 2 ^ 59
def prefixEnd_7588067 : Nat := 4983230072969 + 3 ^ 40 * 7588067 * 2
def baseEnd_7588067 : Nat := 48102785302719362798341

theorem tailTrace_7588067 : CollatzResearch.WordTrace tailWord_7588067 prefixEnd_7588067 48102785302719362798341 := by
  unfold tailWord_7588067
  simp only [CollatzResearch.WordTrace]
  refine ⟨276759540200736672513762455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184506360133824448342508303 276759540200736672513762455)
  ·
    refine ⟨415139310301105008770643683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276759540200736672513762455 415139310301105008770643683)
    ·
      refine ⟨622708965451657513155965525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415139310301105008770643683 622708965451657513155965525)
      ·
        refine ⟨7297370688886611482296471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 622708965451657513155965525 7297370688886611482296471)
        ·
          refine ⟨10946056033329917223444707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297370688886611482296471 10946056033329917223444707)
          ·
            refine ⟨16419084049994875835167061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10946056033329917223444707 16419084049994875835167061)
            ·
              refine ⟨48102785302719362798341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16419084049994875835167061 48102785302719362798341)
              ·
                rfl

theorem cell23_7588067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 10].length) (baseStart_7588067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588067 prefixEnd_7588067 := by exact prefixLift 7588067
  have htrace : WordTrace (prefixWord ++ tailWord_7588067) baseStart_7588067 baseEnd_7588067 := by
    simpa [prefixWord, tailWord_7588067, baseEnd_7588067] using wordTrace_append hprefix tailTrace_7588067
  have hstable : (prefixWord ++ tailWord_7588067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588067).length < 2 ^ (prefixWord ++ tailWord_7588067).sum := by decide
  have hdescent : baseEnd_7588067 < baseStart_7588067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588071 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 2, 4]
def baseStart_7588071 : Nat := 118140960795 + 7588071 * 2 ^ 59
def prefixEnd_7588071 : Nat := 4983230072969 + 3 ^ 40 * 7588071 * 2
def baseEnd_7588071 : Nat := 1298775887814295457005201

theorem tailTrace_7588071 : CollatzResearch.WordTrace tailWord_7588071 prefixEnd_7588071 1298775887814295457005201 := by
  unfold tailWord_7588071
  simp only [CollatzResearch.WordTrace]
  refine ⟨276759686092722181196908067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184506457395148120797938711 276759686092722181196908067)
  ·
    refine ⟨415139529139083271795362101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276759686092722181196908067 415139529139083271795362101)
    ·
      refine ⟨38919330856789056730815197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 415139529139083271795362101 38919330856789056730815197)
      ·
        refine ⟨14594749071295896274055699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38919330856789056730815197 14594749071295896274055699)
        ·
          refine ⟨21892123606943844411083549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14594749071295896274055699 21892123606943844411083549)
          ·
            refine ⟨8209546352603941654156331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21892123606943844411083549 8209546352603941654156331)
            ·
              refine ⟨12314319528905912481234497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209546352603941654156331 12314319528905912481234497)
              ·
                refine ⟨9235739646679434360925873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12314319528905912481234497 9235739646679434360925873)
                ·
                  refine ⟨6926804735009575770694405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9235739646679434360925873 6926804735009575770694405)
                  ·
                    refine ⟨1298775887814295457005201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6926804735009575770694405 1298775887814295457005201)
                    ·
                      rfl

theorem cell23_7588071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_7588071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588071 prefixEnd_7588071 := by exact prefixLift 7588071
  have htrace : WordTrace (prefixWord ++ tailWord_7588071) baseStart_7588071 baseEnd_7588071 := by
    simpa [prefixWord, tailWord_7588071, baseEnd_7588071] using wordTrace_append hprefix tailTrace_7588071
  have hstable : (prefixWord ++ tailWord_7588071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588071).length < 2 ^ (prefixWord ++ tailWord_7588071).sum := by decide
  have hdescent : baseEnd_7588071 < baseStart_7588071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588145 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 2, 1, 3]
def baseStart_7588145 : Nat := 118140960795 + 7588145 * 2 ^ 59
def prefixEnd_7588145 : Nat := 4983230072969 + 3 ^ 40 * 7588145 * 2
def baseEnd_7588145 : Nat := 3896365661011319081490263

theorem tailTrace_7588145 : CollatzResearch.WordTrace tailWord_7588145 prefixEnd_7588145 3896365661011319081490263 := by
  unfold tailWord_7588145
  simp only [CollatzResearch.WordTrace]
  refine ⟨276762385094454091835101889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184508256729636061223401259 276762385094454091835101889)
  ·
    refine ⟨207571788820840568876326417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276762385094454091835101889 207571788820840568876326417)
    ·
      refine ⟨155678841615630426657244813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207571788820840568876326417 155678841615630426657244813)
      ·
        refine ⟨58379565605861409996466805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155678841615630426657244813 58379565605861409996466805)
        ·
          refine ⟨5473084275549507187168763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58379565605861409996466805 5473084275549507187168763)
          ·
            refine ⟨8209626413324260780753145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473084275549507187168763 8209626413324260780753145)
            ·
              refine ⟨6157219809993195585564859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8209626413324260780753145 6157219809993195585564859)
              ·
                refine ⟨9235829714989793378347289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157219809993195585564859 9235829714989793378347289)
                ·
                  refine ⟨6926872286242345033760467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9235829714989793378347289 6926872286242345033760467)
                  ·
                    refine ⟨10390308429363517550640701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6926872286242345033760467 10390308429363517550640701)
                    ·
                      refine ⟨3896365661011319081490263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10390308429363517550640701 3896365661011319081490263)
                      ·
                        rfl

theorem cell23_7588145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_7588145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588145 prefixEnd_7588145 := by exact prefixLift 7588145
  have htrace : WordTrace (prefixWord ++ tailWord_7588145) baseStart_7588145 baseEnd_7588145 := by
    simpa [prefixWord, tailWord_7588145, baseEnd_7588145] using wordTrace_append hprefix tailTrace_7588145
  have hstable : (prefixWord ++ tailWord_7588145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588145).length < 2 ^ (prefixWord ++ tailWord_7588145).sum := by decide
  have hdescent : baseEnd_7588145 < baseStart_7588145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588197 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_7588197 : Nat := 118140960795 + 7588197 * 2 ^ 59
def prefixEnd_7588197 : Nat := 4983230072969 + 3 ^ 40 * 7588197 * 2
def baseEnd_7588197 : Nat := 3896392362005352878040023

theorem tailTrace_7588197 : CollatzResearch.WordTrace tailWord_7588197 prefixEnd_7588197 3896392362005352878040023 := by
  unfold tailWord_7588197
  simp only [CollatzResearch.WordTrace]
  refine ⟨276764281690265704715994845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184509521126843803143996563 276764281690265704715994845)
  ·
    refine ⟨103786605633849639268498067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276764281690265704715994845 103786605633849639268498067)
    ·
      refine ⟨155679908450774458902747101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103786605633849639268498067 155679908450774458902747101)
      ·
        refine ⟨58379965669040422088530163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155679908450774458902747101 58379965669040422088530163)
        ·
          refine ⟨87569948503560633132795245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58379965669040422088530163 87569948503560633132795245)
          ·
            refine ⟨32838730688835237424798217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87569948503560633132795245 32838730688835237424798217)
            ·
              refine ⟨24629048016626428068598663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32838730688835237424798217 24629048016626428068598663)
              ·
                refine ⟨36943572024939642102897995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24629048016626428068598663 36943572024939642102897995)
                ·
                  refine ⟨55415358037409463154346993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36943572024939642102897995 55415358037409463154346993)
                  ·
                    refine ⟨41561518528057097365760245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55415358037409463154346993 41561518528057097365760245)
                    ·
                      refine ⟨3896392362005352878040023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41561518528057097365760245 3896392362005352878040023)
                      ·
                        rfl

theorem cell23_7588197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_7588197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588197 prefixEnd_7588197 := by exact prefixLift 7588197
  have htrace : WordTrace (prefixWord ++ tailWord_7588197) baseStart_7588197 baseEnd_7588197 := by
    simpa [prefixWord, tailWord_7588197, baseEnd_7588197] using wordTrace_append hprefix tailTrace_7588197
  have hstable : (prefixWord ++ tailWord_7588197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588197).length < 2 ^ (prefixWord ++ tailWord_7588197).sum := by decide
  have hdescent : baseEnd_7588197 < baseStart_7588197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588308 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_7588308 : Nat := 118140960795 + 7588308 * 2 ^ 59
def prefixEnd_7588308 : Nat := 4983230072969 + 3 ^ 40 * 7588308 * 2
def baseEnd_7588308 : Nat := 3896449358358001943752013

theorem tailTrace_7588308 : CollatzResearch.WordTrace tailWord_7588308 prefixEnd_7588308 3896449358358001943752013 := by
  unfold tailWord_7588308
  simp only [CollatzResearch.WordTrace]
  refine ⟨138384165096431785336642789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184512220128575713782190385 138384165096431785336642789)
  ·
    refine ⟨25947030955580959750620523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138384165096431785336642789 25947030955580959750620523)
    ·
      refine ⟨38920546433371439625930785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25947030955580959750620523 38920546433371439625930785)
      ·
        refine ⟨29190409825028579719448089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38920546433371439625930785 29190409825028579719448089)
        ·
          refine ⟨21892807368771434789586067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29190409825028579719448089 21892807368771434789586067)
          ·
            refine ⟨32839211053157152184379101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21892807368771434789586067 32839211053157152184379101)
            ·
              refine ⟨12314704144933932069142163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32839211053157152184379101 12314704144933932069142163)
              ·
                refine ⟨18472056217400898103713245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12314704144933932069142163 18472056217400898103713245)
                ·
                  refine ⟨6927021081525336788892467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18472056217400898103713245 6927021081525336788892467)
                  ·
                    refine ⟨10390531622288005183338701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6927021081525336788892467 10390531622288005183338701)
                    ·
                      refine ⟨3896449358358001943752013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10390531622288005183338701 3896449358358001943752013)
                      ·
                        rfl

theorem cell23_7588308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_7588308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588308 prefixEnd_7588308 := by exact prefixLift 7588308
  have htrace : WordTrace (prefixWord ++ tailWord_7588308) baseStart_7588308 baseEnd_7588308 := by
    simpa [prefixWord, tailWord_7588308, baseEnd_7588308] using wordTrace_append hprefix tailTrace_7588308
  have hstable : (prefixWord ++ tailWord_7588308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588308).length < 2 ^ (prefixWord ++ tailWord_7588308).sum := by decide
  have hdescent : baseEnd_7588308 < baseStart_7588308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588314 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_7588314 : Nat := 118140960795 + 7588314 * 2 ^ 59
def prefixEnd_7588314 : Nat := 4983230072969 + 3 ^ 40 * 7588314 * 2
def baseEnd_7588314 : Nat := 3896452439241928920276985

theorem tailTrace_7588314 : CollatzResearch.WordTrace tailWord_7588314 prefixEnd_7588314 3896452439241928920276985 := by
  unfold tailWord_7588314
  simp only [CollatzResearch.WordTrace]
  refine ⟨69192137257710458424500999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184512366020561222465335997 69192137257710458424500999)
  ·
    refine ⟨103788205886565687636751499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69192137257710458424500999 103788205886565687636751499)
    ·
      refine ⟨155682308829848531455127249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103788205886565687636751499 155682308829848531455127249)
      ·
        refine ⟨116761731622386398591345437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155682308829848531455127249 116761731622386398591345437)
        ·
          refine ⟨43785649358394899471754539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116761731622386398591345437 43785649358394899471754539)
          ·
            refine ⟨65678474037592349207631809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43785649358394899471754539 65678474037592349207631809)
            ·
              refine ⟨49258855528194261905723857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65678474037592349207631809 49258855528194261905723857)
              ·
                refine ⟨36944141646145696429292893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49258855528194261905723857 36944141646145696429292893)
                ·
                  refine ⟨13854053117304636160984835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36944141646145696429292893 13854053117304636160984835)
                  ·
                    refine ⟨20781079675956954241477253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13854053117304636160984835 20781079675956954241477253)
                    ·
                      refine ⟨3896452439241928920276985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20781079675956954241477253 3896452439241928920276985)
                      ·
                        rfl

theorem cell23_7588314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_7588314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588314 prefixEnd_7588314 := by exact prefixLift 7588314
  have htrace : WordTrace (prefixWord ++ tailWord_7588314) baseStart_7588314 baseEnd_7588314 := by
    simpa [prefixWord, tailWord_7588314, baseEnd_7588314] using wordTrace_append hprefix tailTrace_7588314
  have hstable : (prefixWord ++ tailWord_7588314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588314).length < 2 ^ (prefixWord ++ tailWord_7588314).sum := by decide
  have hdescent : baseEnd_7588314 < baseStart_7588314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588331 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 5, 2, 2]
def baseStart_7588331 : Nat := 118140960795 + 7588331 * 2 ^ 59
def prefixEnd_7588331 : Nat := 4983230072969 + 3 ^ 40 * 7588331 * 2
def baseEnd_7588331 : Nat := 3896461168413055353764407

theorem tailTrace_7588331 : CollatzResearch.WordTrace tailWord_7588331 prefixEnd_7588331 3896461168413055353764407 := by
  unfold tailWord_7588331
  simp only [CollatzResearch.WordTrace]
  refine ⟨276769169071780245601372847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184512779381186830400915231 276769169071780245601372847)
  ·
    refine ⟨415153753607670368402059271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276769169071780245601372847 415153753607670368402059271)
    ·
      refine ⟨622730630411505552603088907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415153753607670368402059271 622730630411505552603088907)
      ·
        refine ⟨934095945617258328904633361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622730630411505552603088907 934095945617258328904633361)
        ·
          refine ⟨700571959212943746678475021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934095945617258328904633361 700571959212943746678475021)
          ·
            refine ⟨262714484704853905004428133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 700571959212943746678475021 262714484704853905004428133)
            ·
              refine ⟨49258965882160107188330275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262714484704853905004428133 49258965882160107188330275)
              ·
                refine ⟨73888448823240160782495413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49258965882160107188330275 73888448823240160782495413)
                ·
                  refine ⟨6927042077178765073358945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73888448823240160782495413 6927042077178765073358945)
                  ·
                    refine ⟨5195281557884073805019209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6927042077178765073358945 5195281557884073805019209)
                    ·
                      refine ⟨3896461168413055353764407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195281557884073805019209 3896461168413055353764407)
                      ·
                        rfl

theorem cell23_7588331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 2, 2].length) (baseStart_7588331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588331 prefixEnd_7588331 := by exact prefixLift 7588331
  have htrace : WordTrace (prefixWord ++ tailWord_7588331) baseStart_7588331 baseEnd_7588331 := by
    simpa [prefixWord, tailWord_7588331, baseEnd_7588331] using wordTrace_append hprefix tailTrace_7588331
  have hstable : (prefixWord ++ tailWord_7588331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588331).length < 2 ^ (prefixWord ++ tailWord_7588331).sum := by decide
  have hdescent : baseEnd_7588331 < baseStart_7588331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588337 : List Nat := [1, 2, 2, 2, 3, 1, 1, 11]
def baseStart_7588337 : Nat := 118140960795 + 7588337 * 2 ^ 59
def prefixEnd_7588337 : Nat := 4983230072969 + 3 ^ 40 * 7588337 * 2
def baseEnd_7588337 : Nat := 144313490714703049269977

theorem tailTrace_7588337 : CollatzResearch.WordTrace tailWord_7588337 prefixEnd_7588337 144313490714703049269977 := by
  unfold tailWord_7588337
  simp only [CollatzResearch.WordTrace]
  refine ⟨276769387909758508626091265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184512925273172339084060843 276769387909758508626091265)
  ·
    refine ⟨207577040932318881469568449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276769387909758508626091265 207577040932318881469568449)
    ·
      refine ⟨155682780699239161102176337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207577040932318881469568449 155682780699239161102176337)
      ·
        refine ⟨116762085524429370826632253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155682780699239161102176337 116762085524429370826632253)
        ·
          refine ⟨43785782071661014059987095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116762085524429370826632253 43785782071661014059987095)
          ·
            refine ⟨65678673107491521089980643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43785782071661014059987095 65678673107491521089980643)
            ·
              refine ⟨98518009661237281634970965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65678673107491521089980643 98518009661237281634970965)
              ·
                refine ⟨144313490714703049269977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 98518009661237281634970965 144313490714703049269977)
                ·
                  rfl

theorem cell23_7588337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 11].length) (baseStart_7588337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588337 prefixEnd_7588337 := by exact prefixLift 7588337
  have htrace : WordTrace (prefixWord ++ tailWord_7588337) baseStart_7588337 baseEnd_7588337 := by
    simpa [prefixWord, tailWord_7588337, baseEnd_7588337] using wordTrace_append hprefix tailTrace_7588337
  have hstable : (prefixWord ++ tailWord_7588337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588337).length < 2 ^ (prefixWord ++ tailWord_7588337).sum := by decide
  have hdescent : baseEnd_7588337 < baseStart_7588337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588344 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_7588344 : Nat := 118140960795 + 7588344 * 2 ^ 59
def prefixEnd_7588344 : Nat := 4983230072969 + 3 ^ 40 * 7588344 * 2
def baseEnd_7588344 : Nat := 3896467843661563802901847

theorem tailTrace_7588344 : CollatzResearch.WordTrace tailWord_7588344 prefixEnd_7588344 3896467843661563802901847 := by
  unfold tailWord_7588344
  simp only [CollatzResearch.WordTrace]
  refine ⟨138384821610366574410798043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184513095480488765881064057 138384821610366574410798043)
  ·
    refine ⟨207577232415549861616197065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138384821610366574410798043 207577232415549861616197065)
    ·
      refine ⟨155682924311662396212147799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207577232415549861616197065 155682924311662396212147799)
      ·
        refine ⟨233524386467493594318221699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155682924311662396212147799 233524386467493594318221699)
        ·
          refine ⟨350286579701240391477332549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233524386467493594318221699 350286579701240391477332549)
          ·
            refine ⟨65678733693982573401999853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350286579701240391477332549 65678733693982573401999853)
            ·
              refine ⟨24629525135243465025749945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65678733693982573401999853 24629525135243465025749945)
              ·
                refine ⟨18472143851432598769312459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24629525135243465025749945 18472143851432598769312459)
                ·
                  refine ⟨27708215777148898153968689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18472143851432598769312459 27708215777148898153968689)
                  ·
                    refine ⟨20781161832861673615476517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27708215777148898153968689 20781161832861673615476517)
                    ·
                      refine ⟨3896467843661563802901847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20781161832861673615476517 3896467843661563802901847)
                      ·
                        rfl

theorem cell23_7588344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_7588344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588344 prefixEnd_7588344 := by exact prefixLift 7588344
  have htrace : WordTrace (prefixWord ++ tailWord_7588344) baseStart_7588344 baseEnd_7588344 := by
    simpa [prefixWord, tailWord_7588344, baseEnd_7588344] using wordTrace_append hprefix tailTrace_7588344
  have hstable : (prefixWord ++ tailWord_7588344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588344).length < 2 ^ (prefixWord ++ tailWord_7588344).sum := by decide
  have hdescent : baseEnd_7588344 < baseStart_7588344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588354 : List Nat := [3, 4, 1, 2, 13]
def baseStart_7588354 : Nat := 118140960795 + 7588354 * 2 ^ 59
def prefixEnd_7588354 : Nat := 4983230072969 + 3 ^ 40 * 7588354 * 2
def baseEnd_7588354 : Nat := 5344956074716198578569

theorem tailTrace_7588354 : CollatzResearch.WordTrace tailWord_7588354 prefixEnd_7588354 5344956074716198578569 := by
  unfold tailWord_7588354
  simp only [CollatzResearch.WordTrace]
  refine ⟨69192501987674230132365029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184513338633797947019640077 69192501987674230132365029)
  ·
    refine ⟨12973594122688918149818443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69192501987674230132365029 12973594122688918149818443)
    ·
      refine ⟨19460391184033377224727665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12973594122688918149818443 19460391184033377224727665)
      ·
        refine ⟨14595293388025032918545749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19460391184033377224727665 14595293388025032918545749)
        ·
          refine ⟨5344956074716198578569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 14595293388025032918545749 5344956074716198578569)
          ·
            rfl

theorem cell23_7588354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 13].length) (baseStart_7588354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588354 prefixEnd_7588354 := by exact prefixLift 7588354
  have htrace : WordTrace (prefixWord ++ tailWord_7588354) baseStart_7588354 baseEnd_7588354 := by
    simpa [prefixWord, tailWord_7588354, baseEnd_7588354] using wordTrace_append hprefix tailTrace_7588354
  have hstable : (prefixWord ++ tailWord_7588354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588354).length < 2 ^ (prefixWord ++ tailWord_7588354).sum := by decide
  have hdescent : baseEnd_7588354 < baseStart_7588354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588359 : List Nat := [1, 1, 4, 3, 4, 1, 2, 2, 1, 1, 3]
def baseStart_7588359 : Nat := 118140960795 + 7588359 * 2 ^ 59
def prefixEnd_7588359 : Nat := 4983230072969 + 3 ^ 40 * 7588359 * 2
def baseEnd_7588359 : Nat := 3896475545871381244214279

theorem tailTrace_7588359 : CollatzResearch.WordTrace tailWord_7588359 prefixEnd_7588359 3896475545871381244214279 := by
  unfold tailWord_7588359
  simp only [CollatzResearch.WordTrace]
  refine ⟨276770190315678806383392131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184513460210452537588928087 276770190315678806383392131)
  ·
    refine ⟨415155285473518209575088197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276770190315678806383392131 415155285473518209575088197)
    ·
      refine ⟨77841616026284664295329037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415155285473518209575088197 77841616026284664295329037)
      ·
        refine ⟨29190606009856749110748389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77841616026284664295329037 29190606009856749110748389)
        ·
          refine ⟨5473238626848140458265323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29190606009856749110748389 5473238626848140458265323)
          ·
            refine ⟨8209857940272210687397985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473238626848140458265323 8209857940272210687397985)
            ·
              refine ⟨6157393455204158015548489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8209857940272210687397985 6157393455204158015548489)
              ·
                refine ⟨4618045091403118511661367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6157393455204158015548489 4618045091403118511661367)
                ·
                  refine ⟨6927067637104677767492051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618045091403118511661367 6927067637104677767492051)
                  ·
                    refine ⟨10390601455657016651238077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6927067637104677767492051 10390601455657016651238077)
                    ·
                      refine ⟨3896475545871381244214279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10390601455657016651238077 3896475545871381244214279)
                      ·
                        rfl

theorem cell23_7588359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_7588359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588359 prefixEnd_7588359 := by exact prefixLift 7588359
  have htrace : WordTrace (prefixWord ++ tailWord_7588359) baseStart_7588359 baseEnd_7588359 := by
    simpa [prefixWord, tailWord_7588359, baseEnd_7588359] using wordTrace_append hprefix tailTrace_7588359
  have hstable : (prefixWord ++ tailWord_7588359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588359).length < 2 ^ (prefixWord ++ tailWord_7588359).sum := by decide
  have hdescent : baseEnd_7588359 < baseStart_7588359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588367 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 2, 7]
def baseStart_7588367 : Nat := 118140960795 + 7588367 * 2 ^ 59
def prefixEnd_7588367 : Nat := 4983230072969 + 3 ^ 40 * 7588367 * 2
def baseEnd_7588367 : Nat := 1298826551238872404304747

theorem tailTrace_7588367 : CollatzResearch.WordTrace tailWord_7588367 prefixEnd_7588367 1298826551238872404304747 := by
  unfold tailWord_7588367
  simp only [CollatzResearch.WordTrace]
  refine ⟨276770482099649823749683355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184513654733099882499788903 276770482099649823749683355)
  ·
    refine ⟨415155723149474735624525033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276770482099649823749683355 415155723149474735624525033)
    ·
      refine ⟨311366792362106051718393775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415155723149474735624525033 311366792362106051718393775)
      ·
        refine ⟨467050188543159077577590663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311366792362106051718393775 467050188543159077577590663)
        ·
          refine ⟨700575282814738616366385995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467050188543159077577590663 700575282814738616366385995)
          ·
            refine ⟨1050862924222107924549578993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700575282814738616366385995 1050862924222107924549578993)
            ·
              refine ⟨788147193166580943412184245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050862924222107924549578993 788147193166580943412184245)
              ·
                refine ⟨73888799359366963444892273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 788147193166580943412184245 73888799359366963444892273)
                ·
                  refine ⟨55416599519525222583669205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73888799359366963444892273 55416599519525222583669205)
                  ·
                    refine ⟨1298826551238872404304747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55416599519525222583669205 1298826551238872404304747)
                    ·
                      rfl

theorem cell23_7588367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_7588367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588367 prefixEnd_7588367 := by exact prefixLift 7588367
  have htrace : WordTrace (prefixWord ++ tailWord_7588367) baseStart_7588367 baseEnd_7588367 := by
    simpa [prefixWord, tailWord_7588367, baseEnd_7588367] using wordTrace_append hprefix tailTrace_7588367
  have hstable : (prefixWord ++ tailWord_7588367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588367).length < 2 ^ (prefixWord ++ tailWord_7588367).sum := by decide
  have hdescent : baseEnd_7588367 < baseStart_7588367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588381 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_7588381 : Nat := 118140960795 + 7588381 * 2 ^ 59
def prefixEnd_7588381 : Nat := 4983230072969 + 3 ^ 40 * 7588381 * 2
def baseEnd_7588381 : Nat := 3896486842445780158139177

theorem tailTrace_7588381 : CollatzResearch.WordTrace tailWord_7588381 prefixEnd_7588381 3896486842445780158139177 := by
  unfold tailWord_7588381
  simp only [CollatzResearch.WordTrace]
  refine ⟨276770992721599104140692997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184513995147732736093795331 276770992721599104140692997)
  ·
    refine ⟨51894561135299832026379937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276770992721599104140692997 51894561135299832026379937)
    ·
      refine ⟨38920920851474874019784953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51894561135299832026379937 38920920851474874019784953)
      ·
        refine ⟨29190690638606155514838715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38920920851474874019784953 29190690638606155514838715)
        ·
          refine ⟨43786035957909233272258073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29190690638606155514838715 43786035957909233272258073)
          ·
            refine ⟨32839526968431924954193555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43786035957909233272258073 32839526968431924954193555)
            ·
              refine ⟨49259290452647887431290333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32839526968431924954193555 49259290452647887431290333)
              ·
                refine ⟨18472233919742957786733875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49259290452647887431290333 18472233919742957786733875)
                ·
                  refine ⟨27708350879614436680100813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18472233919742957786733875 27708350879614436680100813)
                  ·
                    refine ⟨10390631579855413755037805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27708350879614436680100813 10390631579855413755037805)
                    ·
                      refine ⟨3896486842445780158139177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10390631579855413755037805 3896486842445780158139177)
                      ·
                        rfl

theorem cell23_7588381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_7588381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588381 prefixEnd_7588381 := by exact prefixLift 7588381
  have htrace : WordTrace (prefixWord ++ tailWord_7588381) baseStart_7588381 baseEnd_7588381 := by
    simpa [prefixWord, tailWord_7588381, baseEnd_7588381] using wordTrace_append hprefix tailTrace_7588381
  have hstable : (prefixWord ++ tailWord_7588381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588381).length < 2 ^ (prefixWord ++ tailWord_7588381).sum := by decide
  have hdescent : baseEnd_7588381 < baseStart_7588381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588388 : List Nat := [2, 3, 1, 5, 1, 1, 3, 7]
def baseStart_7588388 : Nat := 118140960795 + 7588388 * 2 ^ 59
def prefixEnd_7588388 : Nat := 4983230072969 + 3 ^ 40 * 7588388 * 2
def baseEnd_7588388 : Nat := 144314460622605986324135

theorem tailTrace_7588388 : CollatzResearch.WordTrace tailWord_7588388 prefixEnd_7588388 144314460622605986324135 := by
  unfold tailWord_7588388
  simp only [CollatzResearch.WordTrace]
  refine ⟨138385624016286872168098909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184514165355049162890798545 138385624016286872168098909)
  ·
    refine ⟨51894609006107577063037091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138385624016286872168098909 51894609006107577063037091)
    ·
      refine ⟨77841913509161365594555637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51894609006107577063037091 77841913509161365594555637)
      ·
        refine ⟨7297679391483878024489591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77841913509161365594555637 7297679391483878024489591)
        ·
          refine ⟨10946519087225817036734387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297679391483878024489591 10946519087225817036734387)
          ·
            refine ⟨16419778630838725555101581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10946519087225817036734387 16419778630838725555101581)
            ·
              refine ⟨6157416986564522083163093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16419778630838725555101581 6157416986564522083163093)
              ·
                refine ⟨144314460622605986324135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6157416986564522083163093 144314460622605986324135)
                ·
                  rfl

theorem cell23_7588388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 7].length) (baseStart_7588388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588388 prefixEnd_7588388 := by exact prefixLift 7588388
  have htrace : WordTrace (prefixWord ++ tailWord_7588388) baseStart_7588388 baseEnd_7588388 := by
    simpa [prefixWord, tailWord_7588388, baseEnd_7588388] using wordTrace_append hprefix tailTrace_7588388
  have hstable : (prefixWord ++ tailWord_7588388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588388).length < 2 ^ (prefixWord ++ tailWord_7588388).sum := by decide
  have hdescent : baseEnd_7588388 < baseStart_7588388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588408 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 1, 3, 2]
def baseStart_7588408 : Nat := 118140960795 + 7588408 * 2 ^ 59
def prefixEnd_7588408 : Nat := 4983230072969 + 3 ^ 40 * 7588408 * 2
def baseEnd_7588408 : Nat := 3896500706423451552501553

theorem tailTrace_7588408 : CollatzResearch.WordTrace tailWord_7588408 prefixEnd_7588408 3896500706423451552501553 := by
  unfold tailWord_7588408
  simp only [CollatzResearch.WordTrace]
  refine ⟨138385988746250643875962939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184514651661667525167950585 138385988746250643875962939)
  ·
    refine ⟨207578983119375965813944409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138385988746250643875962939 207578983119375965813944409)
    ·
      refine ⟨155684237339531974360458307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207578983119375965813944409 155684237339531974360458307)
      ·
        refine ⟨233526356009297961540687461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155684237339531974360458307 233526356009297961540687461)
        ·
          refine ⟨43786191751743367788878899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233526356009297961540687461 43786191751743367788878899)
          ·
            refine ⟨65679287627615051683318349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43786191751743367788878899 65679287627615051683318349)
            ·
              refine ⟨24629732860355644381244381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65679287627615051683318349 24629732860355644381244381)
              ·
                refine ⟨9236149822633366642966643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24629732860355644381244381 9236149822633366642966643)
                ·
                  refine ⟨13854224733950049964449965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236149822633366642966643 13854224733950049964449965)
                  ·
                    refine ⟨5195334275231268736668737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13854224733950049964449965 5195334275231268736668737)
                    ·
                      refine ⟨3896500706423451552501553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195334275231268736668737 3896500706423451552501553)
                      ·
                        rfl

theorem cell23_7588408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_7588408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588408 prefixEnd_7588408 := by exact prefixLift 7588408
  have htrace : WordTrace (prefixWord ++ tailWord_7588408) baseStart_7588408 baseEnd_7588408 := by
    simpa [prefixWord, tailWord_7588408, baseEnd_7588408] using wordTrace_append hprefix tailTrace_7588408
  have hstable : (prefixWord ++ tailWord_7588408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588408).length < 2 ^ (prefixWord ++ tailWord_7588408).sum := by decide
  have hdescent : baseEnd_7588408 < baseStart_7588408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588424 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_7588424 : Nat := 118140960795 + 7588424 * 2 ^ 59
def prefixEnd_7588424 : Nat := 4983230072969 + 3 ^ 40 * 7588424 * 2
def baseEnd_7588424 : Nat := 3896508922113923489901479

theorem tailTrace_7588424 : CollatzResearch.WordTrace tailWord_7588424 prefixEnd_7588424 3896508922113923489901479 := by
  unfold tailWord_7588424
  simp only [CollatzResearch.WordTrace]
  refine ⟨138386280530221661242254163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184515040706962214989672217 138386280530221661242254163)
  ·
    refine ⟨207579420795332491863381245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138386280530221661242254163 207579420795332491863381245)
    ·
      refine ⟨77842282798249684448767967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207579420795332491863381245 77842282798249684448767967)
      ·
        refine ⟨116763424197374526673151951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77842282798249684448767967 116763424197374526673151951)
        ·
          refine ⟨175145136296061790009727927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116763424197374526673151951 175145136296061790009727927)
          ·
            refine ⟨262717704444092685014591891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175145136296061790009727927 262717704444092685014591891)
            ·
              refine ⟨394076556666139027521887837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262717704444092685014591891 394076556666139027521887837)
              ·
                refine ⟨147778708749802135320707939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394076556666139027521887837 147778708749802135320707939)
                ·
                  refine ⟨221668063124703202981061909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147778708749802135320707939 221668063124703202981061909)
                  ·
                    refine ⟨10390690458970462639737277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 221668063124703202981061909 10390690458970462639737277)
                    ·
                      refine ⟨3896508922113923489901479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10390690458970462639737277 3896508922113923489901479)
                      ·
                        rfl

theorem cell23_7588424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_7588424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588424 prefixEnd_7588424 := by exact prefixLift 7588424
  have htrace : WordTrace (prefixWord ++ tailWord_7588424) baseStart_7588424 baseEnd_7588424 := by
    simpa [prefixWord, tailWord_7588424, baseEnd_7588424] using wordTrace_append hprefix tailTrace_7588424
  have hstable : (prefixWord ++ tailWord_7588424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588424).length < 2 ^ (prefixWord ++ tailWord_7588424).sum := by decide
  have hdescent : baseEnd_7588424 < baseStart_7588424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588508 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_7588508 : Nat := 118140960795 + 7588508 * 2 ^ 59
def prefixEnd_7588508 : Nat := 4983230072969 + 3 ^ 40 * 7588508 * 2
def baseEnd_7588508 : Nat := 1298850684829633720417031

theorem tailTrace_7588508 : CollatzResearch.WordTrace tailWord_7588508 prefixEnd_7588508 1298850684829633720417031 := by
  unfold tailWord_7588508
  simp only [CollatzResearch.WordTrace]
  refine ⟨138387812396069502415283089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184517083194759336553710785 138387812396069502415283089)
  ·
    refine ⟨103790859297052126811462317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138387812396069502415283089 103790859297052126811462317)
    ·
      refine ⟨38921572236394547554298369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103790859297052126811462317 38921572236394547554298369)
      ·
        refine ⟨29191179177295910665723777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38921572236394547554298369 29191179177295910665723777)
        ·
          refine ⟨21893384382971932999292833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29191179177295910665723777 21893384382971932999292833)
          ·
            refine ⟨16420038287228949749469625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21893384382971932999292833 16420038287228949749469625)
            ·
              refine ⟨12315028715421712312102219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16420038287228949749469625 12315028715421712312102219)
              ·
                refine ⟨18472543073132568468153329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12315028715421712312102219 18472543073132568468153329)
                ·
                  refine ⟨13854407304849426351114997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18472543073132568468153329 13854407304849426351114997)
                  ·
                    refine ⟨1298850684829633720417031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13854407304849426351114997 1298850684829633720417031)
                    ·
                      rfl

theorem cell23_7588508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_7588508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588508 prefixEnd_7588508 := by exact prefixLift 7588508
  have htrace : WordTrace (prefixWord ++ tailWord_7588508) baseStart_7588508 baseEnd_7588508 := by
    simpa [prefixWord, tailWord_7588508, baseEnd_7588508] using wordTrace_append hprefix tailTrace_7588508
  have hstable : (prefixWord ++ tailWord_7588508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588508).length < 2 ^ (prefixWord ++ tailWord_7588508).sum := by decide
  have hdescent : baseEnd_7588508 < baseStart_7588508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588529 : List Nat := [1, 2, 2, 6, 2, 1, 2, 2, 5]
def baseStart_7588529 : Nat := 118140960795 + 7588529 * 2 ^ 59
def prefixEnd_7588529 : Nat := 4983230072969 + 3 ^ 40 * 7588529 * 2
def baseEnd_7588529 : Nat := 432951426398071731009833

theorem tailTrace_7588529 : CollatzResearch.WordTrace tailWord_7588529 prefixEnd_7588529 432951426398071731009833 := by
  unfold tailWord_7588529
  simp only [CollatzResearch.WordTrace]
  refine ⟨276776390725062925417080641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184517593816708616944720427 276776390725062925417080641)
  ·
    refine ⟨207582293043797194062810481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276776390725062925417080641 207582293043797194062810481)
    ·
      refine ⟨155686719782847895547107861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207582293043797194062810481 155686719782847895547107861)
      ·
        refine ⟨7297814989820995103770681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155686719782847895547107861 7297814989820995103770681)
        ·
          refine ⟨5473361242365746327828011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7297814989820995103770681 5473361242365746327828011)
          ·
            refine ⟨8210041863548619491742017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473361242365746327828011 8210041863548619491742017)
            ·
              refine ⟨6157531397661464618806513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8210041863548619491742017 6157531397661464618806513)
              ·
                refine ⟨4618148548246098464104885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6157531397661464618806513 4618148548246098464104885)
                ·
                  refine ⟨432951426398071731009833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4618148548246098464104885 432951426398071731009833)
                  ·
                    rfl

theorem cell23_7588529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 5].length) (baseStart_7588529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588529 prefixEnd_7588529 := by exact prefixLift 7588529
  have htrace : WordTrace (prefixWord ++ tailWord_7588529) baseStart_7588529 baseEnd_7588529 := by
    simpa [prefixWord, tailWord_7588529, baseEnd_7588529] using wordTrace_append hprefix tailTrace_7588529
  have hstable : (prefixWord ++ tailWord_7588529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588529).length < 2 ^ (prefixWord ++ tailWord_7588529).sum := by decide
  have hdescent : baseEnd_7588529 < baseStart_7588529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588562 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_7588562 : Nat := 118140960795 + 7588562 * 2 ^ 59
def prefixEnd_7588562 : Nat := 4983230072969 + 3 ^ 40 * 7588562 * 2
def baseEnd_7588562 : Nat := 3896579782444243949975845

theorem tailTrace_7588562 : CollatzResearch.WordTrace tailWord_7588562 prefixEnd_7588562 3896579782444243949975845 := by
  unfold tailWord_7588562
  simp only [CollatzResearch.WordTrace]
  refine ⟨69194398583485843013257985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184518396222628914702021293 69194398583485843013257985)
  ·
    refine ⟨51895798937614382259943489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69194398583485843013257985 51895798937614382259943489)
    ·
      refine ⟨38921849203210786694957617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51895798937614382259943489 38921849203210786694957617)
      ·
        refine ⟨29191386902408090021218213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38921849203210786694957617 29191386902408090021218213)
        ·
          refine ⟨5473385044201516878978415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29191386902408090021218213 5473385044201516878978415)
          ·
            refine ⟨8210077566302275318467623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473385044201516878978415 8210077566302275318467623)
            ·
              refine ⟨12315116349453412977701435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8210077566302275318467623 12315116349453412977701435)
              ·
                refine ⟨18472674524180119466552153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12315116349453412977701435 18472674524180119466552153)
                ·
                  refine ⟨13854505893135089599914115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18472674524180119466552153 13854505893135089599914115)
                  ·
                    refine ⟨20781758839702634399871173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13854505893135089599914115 20781758839702634399871173)
                    ·
                      refine ⟨3896579782444243949975845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20781758839702634399871173 3896579782444243949975845)
                      ·
                        rfl

theorem cell23_7588562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_7588562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588562 prefixEnd_7588562 := by exact prefixLift 7588562
  have htrace : WordTrace (prefixWord ++ tailWord_7588562) baseStart_7588562 baseEnd_7588562 := by
    simpa [prefixWord, tailWord_7588562, baseEnd_7588562] using wordTrace_append hprefix tailTrace_7588562
  have hstable : (prefixWord ++ tailWord_7588562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588562).length < 2 ^ (prefixWord ++ tailWord_7588562).sum := by decide
  have hdescent : baseEnd_7588562 < baseStart_7588562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588565 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7588565 : Nat := 118140960795 + 7588565 * 2 ^ 59
def prefixEnd_7588565 : Nat := 4983230072969 + 3 ^ 40 * 7588565 * 2
def baseEnd_7588565 : Nat := 3896581322886207438238331

theorem tailTrace_7588565 : CollatzResearch.WordTrace tailWord_7588565 prefixEnd_7588565 3896581322886207438238331 := by
  unfold tailWord_7588565
  simp only [CollatzResearch.WordTrace]
  refine ⟨276777703752932503565391149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184518469168621669043594099 276777703752932503565391149)
  ·
    refine ⟨103791638907349688837021681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276777703752932503565391149 103791638907349688837021681)
    ·
      refine ⟨77843729180512266627766261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103791638907349688837021681 77843729180512266627766261)
      ·
        refine ⟨7297849610673024996353087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77843729180512266627766261 7297849610673024996353087)
        ·
          refine ⟨10946774416009537494529631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297849610673024996353087 10946774416009537494529631)
          ·
            refine ⟨16420161624014306241794447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10946774416009537494529631 16420161624014306241794447)
            ·
              refine ⟨24630242436021459362691671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16420161624014306241794447 24630242436021459362691671)
              ·
                refine ⟨36945363654032189044037507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24630242436021459362691671 36945363654032189044037507)
                ·
                  refine ⟨55418045481048283566056261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36945363654032189044037507 55418045481048283566056261)
                  ·
                    refine ⟨10390883527696553168635549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55418045481048283566056261 10390883527696553168635549)
                    ·
                      refine ⟨3896581322886207438238331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10390883527696553168635549 3896581322886207438238331)
                      ·
                        rfl

theorem cell23_7588565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7588565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588565 prefixEnd_7588565 := by exact prefixLift 7588565
  have htrace : WordTrace (prefixWord ++ tailWord_7588565) baseStart_7588565 baseEnd_7588565 := by
    simpa [prefixWord, tailWord_7588565, baseEnd_7588565] using wordTrace_append hprefix tailTrace_7588565
  have hstable : (prefixWord ++ tailWord_7588565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588565).length < 2 ^ (prefixWord ++ tailWord_7588565).sum := by decide
  have hdescent : baseEnd_7588565 < baseStart_7588565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588572 : List Nat := [2, 2, 5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7588572 : Nat := 118140960795 + 7588572 * 2 ^ 59
def prefixEnd_7588572 : Nat := 4983230072969 + 3 ^ 40 * 7588572 * 2
def baseEnd_7588572 : Nat := 1298861639083596303616933

theorem tailTrace_7588572 : CollatzResearch.WordTrace tailWord_7588572 prefixEnd_7588572 1298861639083596303616933 := by
  unfold tailWord_7588572
  simp only [CollatzResearch.WordTrace]
  refine ⟨138388979531953571880447985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184518639375938095840597313 138388979531953571880447985)
  ·
    refine ⟨103791734648965178910335989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138388979531953571880447985 103791734648965178910335989)
    ·
      refine ⟨9730475123340485522843999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103791734648965178910335989 9730475123340485522843999)
      ·
        refine ⟨14595712685010728284265999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9730475123340485522843999 14595712685010728284265999)
        ·
          refine ⟨21893569027516092426398999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14595712685010728284265999 21893569027516092426398999)
          ·
            refine ⟨32840353541274138639598499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21893569027516092426398999 32840353541274138639598499)
            ·
              refine ⟨49260530311911207959397749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32840353541274138639598499 49260530311911207959397749)
              ·
                refine ⟨4618174716741675746193539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49260530311911207959397749 4618174716741675746193539)
                ·
                  refine ⟨6927262075112513619290309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618174716741675746193539 6927262075112513619290309)
                  ·
                    refine ⟨1298861639083596303616933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6927262075112513619290309 1298861639083596303616933)
                    ·
                      rfl

theorem cell23_7588572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7588572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588572 prefixEnd_7588572 := by exact prefixLift 7588572
  have htrace : WordTrace (prefixWord ++ tailWord_7588572) baseStart_7588572 baseEnd_7588572 := by
    simpa [prefixWord, tailWord_7588572, baseEnd_7588572] using wordTrace_append hprefix tailTrace_7588572
  have hstable : (prefixWord ++ tailWord_7588572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588572).length < 2 ^ (prefixWord ++ tailWord_7588572).sum := by decide
  have hdescent : baseEnd_7588572 < baseStart_7588572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588588 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 4, 3, 2]
def baseStart_7588588 : Nat := 118140960795 + 7588588 * 2 ^ 59
def prefixEnd_7588588 : Nat := 4983230072969 + 3 ^ 40 * 7588588 * 2
def baseEnd_7588588 : Nat := 3896593132941260848250725

theorem tailTrace_7588588 : CollatzResearch.WordTrace tailWord_7588588 prefixEnd_7588588 3896593132941260848250725 := by
  unfold tailWord_7588588
  simp only [CollatzResearch.WordTrace]
  refine ⟨138389271315924589246739209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184519028421232785662318945 138389271315924589246739209)
  ·
    refine ⟨103791953486943441935054407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138389271315924589246739209 103791953486943441935054407)
    ·
      refine ⟨155687930230415162902581611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103791953486943441935054407 155687930230415162902581611)
      ·
        refine ⟨233531895345622744353872417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155687930230415162902581611 233531895345622744353872417)
        ·
          refine ⟨175148921509217058265404313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233531895345622744353872417 175148921509217058265404313)
          ·
            refine ⟨131361691131912793699053235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175148921509217058265404313 131361691131912793699053235)
            ·
              refine ⟨197042536697869190548579853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131361691131912793699053235 197042536697869190548579853)
              ·
                refine ⟨73890951261700946455717445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197042536697869190548579853 73890951261700946455717445)
                ·
                  refine ⟨13854553361568927460447021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73890951261700946455717445 13854553361568927460447021)
                  ·
                    refine ⟨5195457510588347797667633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13854553361568927460447021 5195457510588347797667633)
                    ·
                      refine ⟨3896593132941260848250725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195457510588347797667633 3896593132941260848250725)
                      ·
                        rfl

theorem cell23_7588588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_7588588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588588 prefixEnd_7588588 := by exact prefixLift 7588588
  have htrace : WordTrace (prefixWord ++ tailWord_7588588) baseStart_7588588 baseEnd_7588588 := by
    simpa [prefixWord, tailWord_7588588, baseEnd_7588588] using wordTrace_append hprefix tailTrace_7588588
  have hstable : (prefixWord ++ tailWord_7588588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588588).length < 2 ^ (prefixWord ++ tailWord_7588588).sum := by decide
  have hdescent : baseEnd_7588588 < baseStart_7588588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588601 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_7588601 : Nat := 118140960795 + 7588601 * 2 ^ 59
def prefixEnd_7588601 : Nat := 4983230072969 + 3 ^ 40 * 7588601 * 2
def baseEnd_7588601 : Nat := 3896599808189769297388165

theorem tailTrace_7588601 : CollatzResearch.WordTrace tailWord_7588601 prefixEnd_7588601 3896599808189769297388165 := by
  unfold tailWord_7588601
  simp only [CollatzResearch.WordTrace]
  refine ⟨276779016780802081713701657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184519344520534721142467771 276779016780802081713701657)
  ·
    refine ⟨207584262585601561285276243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276779016780802081713701657 207584262585601561285276243)
    ·
      refine ⟨311376393878402341927914365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207584262585601561285276243 311376393878402341927914365)
      ·
        refine ⟨116766147704400878222967887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311376393878402341927914365 116766147704400878222967887)
        ·
          refine ⟨175149221556601317334451831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116766147704400878222967887 175149221556601317334451831)
          ·
            refine ⟨262723832334901976001677747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175149221556601317334451831 262723832334901976001677747)
            ·
              refine ⟨394085748502352964002516621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262723832334901976001677747 394085748502352964002516621)
              ·
                refine ⟨147782155688382361500943733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394085748502352964002516621 147782155688382361500943733)
                ·
                  refine ⟨13854577095785846390713475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147782155688382361500943733 13854577095785846390713475)
                  ·
                    refine ⟨20781865643678769586070213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13854577095785846390713475 20781865643678769586070213)
                    ·
                      refine ⟨3896599808189769297388165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20781865643678769586070213 3896599808189769297388165)
                      ·
                        rfl

theorem cell23_7588601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_7588601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588601 prefixEnd_7588601 := by exact prefixLift 7588601
  have htrace : WordTrace (prefixWord ++ tailWord_7588601) baseStart_7588601 baseEnd_7588601 := by
    simpa [prefixWord, tailWord_7588601, baseEnd_7588601] using wordTrace_append hprefix tailTrace_7588601
  have hstable : (prefixWord ++ tailWord_7588601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588601).length < 2 ^ (prefixWord ++ tailWord_7588601).sum := by decide
  have hdescent : baseEnd_7588601 < baseStart_7588601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588615 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 1, 5]
def baseStart_7588615 : Nat := 118140960795 + 7588615 * 2 ^ 59
def prefixEnd_7588615 : Nat := 4983230072969 + 3 ^ 40 * 7588615 * 2
def baseEnd_7588615 : Nat := 1298868998972977414204367

theorem tailTrace_7588615 : CollatzResearch.WordTrace tailWord_7588615 prefixEnd_7588615 1298868998972977414204367 := by
  unfold tailWord_7588615
  simp only [CollatzResearch.WordTrace]
  refine ⟨276779527402751362104711299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184519684935167574736474199 276779527402751362104711299)
  ·
    refine ⟨415169291104127043157066949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276779527402751362104711299 415169291104127043157066949)
    ·
      refine ⟨77844242082023820591950053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415169291104127043157066949 77844242082023820591950053)
      ·
        refine ⟨14595795390379466360990635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77844242082023820591950053 14595795390379466360990635)
        ·
          refine ⟨21893693085569199541485953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14595795390379466360990635 21893693085569199541485953)
          ·
            refine ⟨16420269814176899656114465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21893693085569199541485953 16420269814176899656114465)
            ·
              refine ⟨12315202360632674742085849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16420269814176899656114465 12315202360632674742085849)
              ·
                refine ⟨9236401770474506056564387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12315202360632674742085849 9236401770474506056564387)
                ·
                  refine ⟨13854602655711759084846581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236401770474506056564387 13854602655711759084846581)
                  ·
                    refine ⟨1298868998972977414204367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13854602655711759084846581 1298868998972977414204367)
                    ·
                      rfl

theorem cell23_7588615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_7588615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588615 prefixEnd_7588615 := by exact prefixLift 7588615
  have htrace : WordTrace (prefixWord ++ tailWord_7588615) baseStart_7588615 baseEnd_7588615 := by
    simpa [prefixWord, tailWord_7588615, baseEnd_7588615] using wordTrace_append hprefix tailTrace_7588615
  have hstable : (prefixWord ++ tailWord_7588615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588615).length < 2 ^ (prefixWord ++ tailWord_7588615).sum := by decide
  have hdescent : baseEnd_7588615 < baseStart_7588615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588618 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_7588618 : Nat := 118140960795 + 7588618 * 2 ^ 59
def prefixEnd_7588618 : Nat := 4983230072969 + 3 ^ 40 * 7588618 * 2
def baseEnd_7588618 : Nat := 3896608537360895730875587

theorem tailTrace_7588618 : CollatzResearch.WordTrace tailWord_7588618 prefixEnd_7588618 3896608537360895730875587 := by
  unfold tailWord_7588618
  simp only [CollatzResearch.WordTrace]
  refine ⟨69194909205435123404267627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184519757881160329078047005 69194909205435123404267627)
  ·
    refine ⟨103792363808152685106401441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69194909205435123404267627 103792363808152685106401441)
    ·
      refine ⟨77844272856114513829801081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103792363808152685106401441 77844272856114513829801081)
      ·
        refine ⟨58383204642085885372350811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77844272856114513829801081 58383204642085885372350811)
        ·
          refine ⟨87574806963128828058526217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58383204642085885372350811 87574806963128828058526217)
          ·
            refine ⟨65681105222346621043894663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87574806963128828058526217 65681105222346621043894663)
            ·
              refine ⟨98521657833519931565841995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65681105222346621043894663 98521657833519931565841995)
              ·
                refine ⟨147782486750279897348762993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98521657833519931565841995 147782486750279897348762993)
                ·
                  refine ⟨110836865062709923011572245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147782486750279897348762993 110836865062709923011572245)
                  ·
                    refine ⟨5195478049814527641167449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110836865062709923011572245 5195478049814527641167449)
                    ·
                      refine ⟨3896608537360895730875587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195478049814527641167449 3896608537360895730875587)
                      ·
                        rfl

theorem cell23_7588618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_7588618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588618 prefixEnd_7588618 := by exact prefixLift 7588618
  have htrace : WordTrace (prefixWord ++ tailWord_7588618) baseStart_7588618 baseEnd_7588618 := by
    simpa [prefixWord, tailWord_7588618, baseEnd_7588618] using wordTrace_append hprefix tailTrace_7588618
  have hstable : (prefixWord ++ tailWord_7588618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588618).length < 2 ^ (prefixWord ++ tailWord_7588618).sum := by decide
  have hdescent : baseEnd_7588618 < baseStart_7588618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588668 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_7588668 : Nat := 118140960795 + 7588668 * 2 ^ 59
def prefixEnd_7588668 : Nat := 4983230072969 + 3 ^ 40 * 7588668 * 2
def baseEnd_7588668 : Nat := 3896634211393620535250357

theorem tailTrace_7588668 : CollatzResearch.WordTrace tailWord_7588668 prefixEnd_7588668 3896634211393620535250357 := by
  unfold tailWord_7588668
  simp only [CollatzResearch.WordTrace]
  refine ⟨138390730235779676078195329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184520973647706234770927105 138390730235779676078195329)
  ·
    refine ⟨103793047676834757058646497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138390730235779676078195329 103793047676834757058646497)
    ·
      refine ⟨77844785757626067793984873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103793047676834757058646497 77844785757626067793984873)
      ·
        refine ⟨58383589318219550845488655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77844785757626067793984873 58383589318219550845488655)
        ·
          refine ⟨87575383977329326268232983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58383589318219550845488655 87575383977329326268232983)
          ·
            refine ⟨131363075965993989402349475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87575383977329326268232983 131363075965993989402349475)
            ·
              refine ⟨197044613948990984103524213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131363075965993989402349475 197044613948990984103524213)
              ·
                refine ⟨18472932557717904759705395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197044613948990984103524213 18472932557717904759705395)
                ·
                  refine ⟨27709398836576857139558093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18472932557717904759705395 27709398836576857139558093)
                  ·
                    refine ⟨10391024563716321427334285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27709398836576857139558093 10391024563716321427334285)
                    ·
                      refine ⟨3896634211393620535250357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10391024563716321427334285 3896634211393620535250357)
                      ·
                        rfl

theorem cell23_7588668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_7588668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588668 prefixEnd_7588668 := by exact prefixLift 7588668
  have htrace : WordTrace (prefixWord ++ tailWord_7588668) baseStart_7588668 baseEnd_7588668 := by
    simpa [prefixWord, tailWord_7588668, baseEnd_7588668] using wordTrace_append hprefix tailTrace_7588668
  have hstable : (prefixWord ++ tailWord_7588668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588668).length < 2 ^ (prefixWord ++ tailWord_7588668).sum := by decide
  have hdescent : baseEnd_7588668 < baseStart_7588668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588669 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_7588669 : Nat := 118140960795 + 7588669 * 2 ^ 59
def prefixEnd_7588669 : Nat := 4983230072969 + 3 ^ 40 * 7588669 * 2
def baseEnd_7588669 : Nat := 3896634724874275031337853

theorem tailTrace_7588669 : CollatzResearch.WordTrace tailWord_7588669 prefixEnd_7588669 3896634724874275031337853 := by
  unfold tailWord_7588669
  simp only [CollatzResearch.WordTrace]
  refine ⟨276781496944555729327177061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184520997963037152884784707 276781496944555729327177061)
  ·
    refine ⟨51896530677104199248845699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276781496944555729327177061 51896530677104199248845699)
    ·
      refine ⟨77844796015656298873268549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51896530677104199248845699 77844796015656298873268549)
      ·
        refine ⟨14595899252935556038737853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77844796015656298873268549 14595899252935556038737853)
        ·
          refine ⟨5473462219850833514526695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14595899252935556038737853 5473462219850833514526695)
          ·
            refine ⟨8210193329776250271790043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473462219850833514526695 8210193329776250271790043)
            ·
              refine ⟨12315289994664375407685065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8210193329776250271790043 12315289994664375407685065)
              ·
                refine ⟨9236467495998281555763799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12315289994664375407685065 9236467495998281555763799)
                ·
                  refine ⟨13854701243997422333645699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236467495998281555763799 13854701243997422333645699)
                  ·
                    refine ⟨20782051865996133500468549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13854701243997422333645699 20782051865996133500468549)
                    ·
                      refine ⟨3896634724874275031337853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20782051865996133500468549 3896634724874275031337853)
                      ·
                        rfl

theorem cell23_7588669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_7588669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588669 prefixEnd_7588669 := by exact prefixLift 7588669
  have htrace : WordTrace (prefixWord ++ tailWord_7588669) baseStart_7588669 baseEnd_7588669 := by
    simpa [prefixWord, tailWord_7588669, baseEnd_7588669] using wordTrace_append hprefix tailTrace_7588669
  have hstable : (prefixWord ++ tailWord_7588669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588669).length < 2 ^ (prefixWord ++ tailWord_7588669).sum := by decide
  have hdescent : baseEnd_7588669 < baseStart_7588669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588691 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 4]
def baseStart_7588691 : Nat := 118140960795 + 7588691 * 2 ^ 59
def prefixEnd_7588691 : Nat := 4983230072969 + 3 ^ 40 * 7588691 * 2
def baseEnd_7588691 : Nat := 3896646021448673945262751

theorem tailTrace_7588691 : CollatzResearch.WordTrace tailWord_7588691 prefixEnd_7588691 3896646021448673945262751 := by
  unfold tailWord_7588691
  simp only [CollatzResearch.WordTrace]
  refine ⟨276782299350476027084477927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184521532900317351389651951 276782299350476027084477927)
  ·
    refine ⟨415173449025714040626716891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276782299350476027084477927 415173449025714040626716891)
    ·
      refine ⟨622760173538571060940075337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415173449025714040626716891 622760173538571060940075337)
      ·
        refine ⟨467070130153928295705056503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622760173538571060940075337 467070130153928295705056503)
        ·
          refine ⟨700605195230892443557584755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467070130153928295705056503 700605195230892443557584755)
          ·
            refine ⟨1050907792846338665336377133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700605195230892443557584755 1050907792846338665336377133)
            ·
              refine ⟨394090422317376999501141425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050907792846338665336377133 394090422317376999501141425)
              ·
                refine ⟨295567816738032749625856069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394090422317376999501141425 295567816738032749625856069)
                ·
                  refine ⟨55418965638381140554848013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295567816738032749625856069 55418965638381140554848013)
                  ·
                    refine ⟨20782112114392927708068005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55418965638381140554848013 20782112114392927708068005)
                    ·
                      refine ⟨3896646021448673945262751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20782112114392927708068005 3896646021448673945262751)
                      ·
                        rfl

theorem cell23_7588691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_7588691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588691 prefixEnd_7588691 := by exact prefixLift 7588691
  have htrace : WordTrace (prefixWord ++ tailWord_7588691) baseStart_7588691 baseEnd_7588691 := by
    simpa [prefixWord, tailWord_7588691, baseEnd_7588691] using wordTrace_append hprefix tailTrace_7588691
  have hstable : (prefixWord ++ tailWord_7588691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588691).length < 2 ^ (prefixWord ++ tailWord_7588691).sum := by decide
  have hdescent : baseEnd_7588691 < baseStart_7588691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588708 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_7588708 : Nat := 118140960795 + 7588708 * 2 ^ 59
def prefixEnd_7588708 : Nat := 4983230072969 + 3 ^ 40 * 7588708 * 2
def baseEnd_7588708 : Nat := 3896654750619800378750173

theorem tailTrace_7588708 : CollatzResearch.WordTrace tailWord_7588708 prefixEnd_7588708 3896654750619800378750173 := by
  unfold tailWord_7588708
  simp only [CollatzResearch.WordTrace]
  refine ⟨138391459695707219493923389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184521946260942959325231185 138391459695707219493923389)
  ·
    refine ⟨51896797385890207310221271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138391459695707219493923389 51896797385890207310221271)
    ·
      refine ⟨77845196078835310965331907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51896797385890207310221271 77845196078835310965331907)
      ·
        refine ⟨116767794118252966447997861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77845196078835310965331907 116767794118252966447997861)
        ·
          refine ⟨21893961397172431208999599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116767794118252966447997861 21893961397172431208999599)
          ·
            refine ⟨32840942095758646813499399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21893961397172431208999599 32840942095758646813499399)
            ·
              refine ⟨49261413143637970220249099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32840942095758646813499399 49261413143637970220249099)
              ·
                refine ⟨73892119715456955330373649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49261413143637970220249099 73892119715456955330373649)
                ·
                  refine ⟨55419089786592716497780237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73892119715456955330373649 55419089786592716497780237)
                  ·
                    refine ⟨20782158669972268686667589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55419089786592716497780237 20782158669972268686667589)
                    ·
                      refine ⟨3896654750619800378750173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20782158669972268686667589 3896654750619800378750173)
                      ·
                        rfl

theorem cell23_7588708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_7588708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588708 prefixEnd_7588708 := by exact prefixLift 7588708
  have htrace : WordTrace (prefixWord ++ tailWord_7588708) baseStart_7588708 baseEnd_7588708 := by
    simpa [prefixWord, tailWord_7588708, baseEnd_7588708] using wordTrace_append hprefix tailTrace_7588708
  have hstable : (prefixWord ++ tailWord_7588708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588708).length < 2 ^ (prefixWord ++ tailWord_7588708).sum := by decide
  have hdescent : baseEnd_7588708 < baseStart_7588708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588731 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 9]
def baseStart_7588731 : Nat := 118140960795 + 7588731 * 2 ^ 59
def prefixEnd_7588731 : Nat := 4983230072969 + 3 ^ 40 * 7588731 * 2
def baseEnd_7588731 : Nat := 432962951186094865418063

theorem tailTrace_7588731 : CollatzResearch.WordTrace tailWord_7588731 prefixEnd_7588731 432962951186094865418063 := by
  unfold tailWord_7588731
  simp only [CollatzResearch.WordTrace]
  refine ⟨276783758270331113915934047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184522505513554075943956031 276783758270331113915934047)
  ·
    refine ⟨415175637405496670873901071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276783758270331113915934047 415175637405496670873901071)
    ·
      refine ⟨622763456108245006310851607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415175637405496670873901071 622763456108245006310851607)
      ·
        refine ⟨934145184162367509466277411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622763456108245006310851607 934145184162367509466277411)
        ·
          refine ⟨1401217776243551264199416117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934145184162367509466277411 1401217776243551264199416117)
          ·
            refine ⟨131364166522832931018695261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1401217776243551264199416117 131364166522832931018695261)
            ·
              refine ⟨49261562446062349132010723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131364166522832931018695261 49261562446062349132010723)
              ·
                refine ⟨73892343669093523698016085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49261562446062349132010723 73892343669093523698016085)
                ·
                  refine ⟨432962951186094865418063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73892343669093523698016085 432962951186094865418063)
                  ·
                    rfl

theorem cell23_7588731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 9].length) (baseStart_7588731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588731 prefixEnd_7588731 := by exact prefixLift 7588731
  have htrace : WordTrace (prefixWord ++ tailWord_7588731) baseStart_7588731 baseEnd_7588731 := by
    simpa [prefixWord, tailWord_7588731, baseEnd_7588731] using wordTrace_append hprefix tailTrace_7588731
  have hstable : (prefixWord ++ tailWord_7588731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588731).length < 2 ^ (prefixWord ++ tailWord_7588731).sum := by decide
  have hdescent : baseEnd_7588731 < baseStart_7588731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588746 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_7588746 : Nat := 118140960795 + 7588746 * 2 ^ 59
def prefixEnd_7588746 : Nat := 4983230072969 + 3 ^ 40 * 7588746 * 2
def baseEnd_7588746 : Nat := 3896674262884671230074999

theorem tailTrace_7588746 : CollatzResearch.WordTrace tailWord_7588746 prefixEnd_7588746 3896674262884671230074999 := by
  unfold tailWord_7588746
  simp only [CollatzResearch.WordTrace]
  refine ⟨69196076341319192869432523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184522870243517847651820061 69196076341319192869432523)
  ·
    refine ⟨103794114511978789304148785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69196076341319192869432523 103794114511978789304148785)
    ·
      refine ⟨77845585883984091978111589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103794114511978789304148785 77845585883984091978111589)
      ·
        refine ⟨14596047353247017245895923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77845585883984091978111589 14596047353247017245895923)
        ·
          refine ⟨21894071029870525868843885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14596047353247017245895923 21894071029870525868843885)
          ·
            refine ⟨8210276636201447200816457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21894071029870525868843885 8210276636201447200816457)
            ·
              refine ⟨6157707477151085400612343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8210276636201447200816457 6157707477151085400612343)
              ·
                refine ⟨9236561215726628100918515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157707477151085400612343 9236561215726628100918515)
                ·
                  refine ⟨13854841823589942151377773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236561215726628100918515 13854841823589942151377773)
                  ·
                    refine ⟨5195565683846228306766665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13854841823589942151377773 5195565683846228306766665)
                    ·
                      refine ⟨3896674262884671230074999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195565683846228306766665 3896674262884671230074999)
                      ·
                        rfl

theorem cell23_7588746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_7588746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588746 prefixEnd_7588746 := by exact prefixLift 7588746
  have htrace : WordTrace (prefixWord ++ tailWord_7588746) baseStart_7588746 baseEnd_7588746 := by
    simpa [prefixWord, tailWord_7588746, baseEnd_7588746] using wordTrace_append hprefix tailTrace_7588746
  have hstable : (prefixWord ++ tailWord_7588746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588746).length < 2 ^ (prefixWord ++ tailWord_7588746).sum := by decide
  have hdescent : baseEnd_7588746 < baseStart_7588746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588765 : List Nat := [1, 4, 2, 1, 2, 1, 1, 6, 5]
def baseStart_7588765 : Nat := 118140960795 + 7588765 * 2 ^ 59
def prefixEnd_7588765 : Nat := 4983230072969 + 3 ^ 40 * 7588765 * 2
def baseEnd_7588765 : Nat := 432964891001900739526379

theorem tailTrace_7588765 : CollatzResearch.WordTrace tailWord_7588765 prefixEnd_7588765 432964891001900739526379 := by
  unfold tailWord_7588765
  simp only [CollatzResearch.WordTrace]
  refine ⟨276784998352207937722671749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184523332234805291815114499 276784998352207937722671749)
  ·
    refine ⟨51897187191038988323000953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276784998352207937722671749 51897187191038988323000953)
    ·
      refine ⟨38922890393279241242250715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51897187191038988323000953 38922890393279241242250715)
      ·
        refine ⟨58384335589918861863376073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38922890393279241242250715 58384335589918861863376073)
        ·
          refine ⟨43788251692439146397532055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58384335589918861863376073 43788251692439146397532055)
          ·
            refine ⟨65682377538658719596298083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43788251692439146397532055 65682377538658719596298083)
            ·
              refine ⟨98523566307988079394447125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65682377538658719596298083 98523566307988079394447125)
              ·
                refine ⟨4618292170686941221614709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98523566307988079394447125 4618292170686941221614709)
                ·
                  refine ⟨432964891001900739526379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4618292170686941221614709 432964891001900739526379)
                  ·
                    rfl

theorem cell23_7588765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_7588765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588765 prefixEnd_7588765 := by exact prefixLift 7588765
  have htrace : WordTrace (prefixWord ++ tailWord_7588765) baseStart_7588765 baseEnd_7588765 := by
    simpa [prefixWord, tailWord_7588765, baseEnd_7588765] using wordTrace_append hprefix tailTrace_7588765
  have hstable : (prefixWord ++ tailWord_7588765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588765).length < 2 ^ (prefixWord ++ tailWord_7588765).sum := by decide
  have hdescent : baseEnd_7588765 < baseStart_7588765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588815 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_7588815 : Nat := 118140960795 + 7588815 * 2 ^ 59
def prefixEnd_7588815 : Nat := 4983230072969 + 3 ^ 40 * 7588815 * 2
def baseEnd_7588815 : Nat := 3896709693049831460112181

theorem tailTrace_7588815 : CollatzResearch.WordTrace tailWord_7588815 prefixEnd_7588815 3896709693049831460112181 := by
  unfold tailWord_7588815
  simp only [CollatzResearch.WordTrace]
  refine ⟨276786822002026796261991899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184524548001351197507994599 276786822002026796261991899)
  ·
    refine ⟨415180233003040194392987849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276786822002026796261991899 415180233003040194392987849)
    ·
      refine ⟨311385174752280145794740887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415180233003040194392987849 311385174752280145794740887)
      ·
        refine ⟨467077762128420218692111331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311385174752280145794740887 467077762128420218692111331)
        ·
          refine ⟨700616643192630328038166997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467077762128420218692111331 700616643192630328038166997)
          ·
            refine ⟨16420702574827273313394539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 700616643192630328038166997 16420702574827273313394539)
            ·
              refine ⟨24631053862240909970091809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16420702574827273313394539 24631053862240909970091809)
              ·
                refine ⟨18473290396680682477568857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24631053862240909970091809 18473290396680682477568857)
                ·
                  refine ⟨13854967797510511858176643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18473290396680682477568857 13854967797510511858176643)
                  ·
                    refine ⟨20782451696265767787264965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13854967797510511858176643 20782451696265767787264965)
                    ·
                      refine ⟨3896709693049831460112181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20782451696265767787264965 3896709693049831460112181)
                      ·
                        rfl

theorem cell23_7588815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_7588815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588815 prefixEnd_7588815 := by exact prefixLift 7588815
  have htrace : WordTrace (prefixWord ++ tailWord_7588815) baseStart_7588815 baseEnd_7588815 := by
    simpa [prefixWord, tailWord_7588815, baseEnd_7588815] using wordTrace_append hprefix tailTrace_7588815
  have hstable : (prefixWord ++ tailWord_7588815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588815).length < 2 ^ (prefixWord ++ tailWord_7588815).sum := by decide
  have hdescent : baseEnd_7588815 < baseStart_7588815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588822 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7588822 : Nat := 118140960795 + 7588822 * 2 ^ 59
def prefixEnd_7588822 : Nat := 4983230072969 + 3 ^ 40 * 7588822 * 2
def baseEnd_7588822 : Nat := 3896713287414412932724649

theorem tailTrace_7588822 : CollatzResearch.WordTrace tailWord_7588822 prefixEnd_7588822 3896713287414412932724649 := by
  unfold tailWord_7588822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17299192332062589778593545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184524718208667624304997813 17299192332062589778593545)
  ·
    refine ⟨12974394249046942333945159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17299192332062589778593545 12974394249046942333945159)
    ·
      refine ⟨19461591373570413500917739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12974394249046942333945159 19461591373570413500917739)
      ·
        refine ⟨29192387060355620251376609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19461591373570413500917739 29192387060355620251376609)
        ·
          refine ⟨21894290295266715188532457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29192387060355620251376609 21894290295266715188532457)
          ·
            refine ⟨16420717721450036391399343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21894290295266715188532457 16420717721450036391399343)
            ·
              refine ⟨24631076582175054587099015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16420717721450036391399343 24631076582175054587099015)
              ·
                refine ⟨36946614873262581880648523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24631076582175054587099015 36946614873262581880648523)
                ·
                  refine ⟨55419922309893872820972785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36946614873262581880648523 55419922309893872820972785)
                  ·
                    refine ⟨41564941732420404615729589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55419922309893872820972785 41564941732420404615729589)
                    ·
                      refine ⟨3896713287414412932724649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41564941732420404615729589 3896713287414412932724649)
                      ·
                        rfl

theorem cell23_7588822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7588822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588822 prefixEnd_7588822 := by exact prefixLift 7588822
  have htrace : WordTrace (prefixWord ++ tailWord_7588822) baseStart_7588822 baseEnd_7588822 := by
    simpa [prefixWord, tailWord_7588822, baseEnd_7588822] using wordTrace_append hprefix tailTrace_7588822
  have hstable : (prefixWord ++ tailWord_7588822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588822).length < 2 ^ (prefixWord ++ tailWord_7588822).sum := by decide
  have hdescent : baseEnd_7588822 < baseStart_7588822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588835 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 3]
def baseStart_7588835 : Nat := 118140960795 + 7588835 * 2 ^ 59
def prefixEnd_7588835 : Nat := 4983230072969 + 3 ^ 40 * 7588835 * 2
def baseEnd_7588835 : Nat := 3896719962662921381862089

theorem tailTrace_7588835 : CollatzResearch.WordTrace tailWord_7588835 prefixEnd_7588835 3896719962662921381862089 := by
  unfold tailWord_7588835
  simp only [CollatzResearch.WordTrace]
  refine ⟨276787551461954339677719959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184525034307969559785146639 276787551461954339677719959)
  ·
    refine ⟨415181327192931509516579939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276787551461954339677719959 415181327192931509516579939)
    ·
      refine ⟨622771990789397264274869909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415181327192931509516579939 622771990789397264274869909)
      ·
        refine ⟨29192437068252996762884527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 622771990789397264274869909 29192437068252996762884527)
        ·
          refine ⟨43788655602379495144326791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29192437068252996762884527 43788655602379495144326791)
          ·
            refine ⟨65682983403569242716490187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43788655602379495144326791 65682983403569242716490187)
            ·
              refine ⟨98524475105353864074735281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65682983403569242716490187 98524475105353864074735281)
              ·
                refine ⟨73893356329015398056051461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98524475105353864074735281 73893356329015398056051461)
                ·
                  refine ⟨13855004311690387135509649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73893356329015398056051461 13855004311690387135509649)
                  ·
                    refine ⟨10391253233767790351632237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13855004311690387135509649 10391253233767790351632237)
                    ·
                      refine ⟨3896719962662921381862089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10391253233767790351632237 3896719962662921381862089)
                      ·
                        rfl

theorem cell23_7588835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_7588835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588835 prefixEnd_7588835 := by exact prefixLift 7588835
  have htrace : WordTrace (prefixWord ++ tailWord_7588835) baseStart_7588835 baseEnd_7588835 := by
    simpa [prefixWord, tailWord_7588835, baseEnd_7588835] using wordTrace_append hprefix tailTrace_7588835
  have hstable : (prefixWord ++ tailWord_7588835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588835).length < 2 ^ (prefixWord ++ tailWord_7588835).sum := by decide
  have hdescent : baseEnd_7588835 < baseStart_7588835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588876 : List Nat := [2, 2, 1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_7588876 : Nat := 118140960795 + 7588876 * 2 ^ 59
def prefixEnd_7588876 : Nat := 4983230072969 + 3 ^ 40 * 7588876 * 2
def baseEnd_7588876 : Nat := 1298913671789918573816467

theorem tailTrace_7588876 : CollatzResearch.WordTrace tailWord_7588876 prefixEnd_7588876 1298913671789918573816467 := by
  unfold tailWord_7588876
  simp only [CollatzResearch.WordTrace]
  refine ⟨138394523427402901839981241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184526031236537202453308321 138394523427402901839981241)
  ·
    refine ⟨103795892570552176379985931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138394523427402901839981241 103795892570552176379985931)
    ·
      refine ⟨155693838855828264569978897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103795892570552176379985931 155693838855828264569978897)
      ·
        refine ⟨116770379141871198427484173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155693838855828264569978897 116770379141871198427484173)
        ·
          refine ⟨43788892178201699410306565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116770379141871198427484173 43788892178201699410306565)
          ·
            refine ⟨8210417283412818639432481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43788892178201699410306565 8210417283412818639432481)
            ·
              refine ⟨6157812962559613979574361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8210417283412818639432481 6157812962559613979574361)
              ·
                refine ⟨4618359721919710484680771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6157812962559613979574361 4618359721919710484680771)
                ·
                  refine ⟨6927539582879565727021157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618359721919710484680771 6927539582879565727021157)
                  ·
                    refine ⟨1298913671789918573816467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6927539582879565727021157 1298913671789918573816467)
                    ·
                      rfl

theorem cell23_7588876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_7588876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588876 prefixEnd_7588876 := by exact prefixLift 7588876
  have htrace : WordTrace (prefixWord ++ tailWord_7588876) baseStart_7588876 baseEnd_7588876 := by
    simpa [prefixWord, tailWord_7588876, baseEnd_7588876] using wordTrace_append hprefix tailTrace_7588876
  have hstable : (prefixWord ++ tailWord_7588876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588876).length < 2 ^ (prefixWord ++ tailWord_7588876).sum := by decide
  have hdescent : baseEnd_7588876 < baseStart_7588876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588885 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_7588885 : Nat := 118140960795 + 7588885 * 2 ^ 59
def prefixEnd_7588885 : Nat := 4983230072969 + 3 ^ 40 * 7588885 * 2
def baseEnd_7588885 : Nat := 1298915212231882062078953

theorem tailTrace_7588885 : CollatzResearch.WordTrace tailWord_7588885 prefixEnd_7588885 1298915212231882062078953 := by
  unfold tailWord_7588885
  simp only [CollatzResearch.WordTrace]
  refine ⟨276789375111773198217040109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184526250074515465478026739 276789375111773198217040109)
  ·
    refine ⟨103796015666914949331390041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276789375111773198217040109 103796015666914949331390041)
    ·
      refine ⟨77847011750186211998542531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103796015666914949331390041 77847011750186211998542531)
      ·
        refine ⟨116770517625279317997813797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77847011750186211998542531 116770517625279317997813797)
        ·
          refine ⟨21894472054739872124590087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116770517625279317997813797 21894472054739872124590087)
          ·
            refine ⟨32841708082109808186885131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21894472054739872124590087 32841708082109808186885131)
            ·
              refine ⟨49262562123164712280327697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32841708082109808186885131 49262562123164712280327697)
              ·
                refine ⟨36946921592373534210245773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49262562123164712280327697 36946921592373534210245773)
                ·
                  refine ⟨13855095597140075328842165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36946921592373534210245773 13855095597140075328842165)
                  ·
                    refine ⟨1298915212231882062078953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13855095597140075328842165 1298915212231882062078953)
                    ·
                      rfl

theorem cell23_7588885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_7588885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588885 prefixEnd_7588885 := by exact prefixLift 7588885
  have htrace : WordTrace (prefixWord ++ tailWord_7588885) baseStart_7588885 baseEnd_7588885 := by
    simpa [prefixWord, tailWord_7588885, baseEnd_7588885] using wordTrace_append hprefix tailTrace_7588885
  have hstable : (prefixWord ++ tailWord_7588885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588885).length < 2 ^ (prefixWord ++ tailWord_7588885).sum := by decide
  have hdescent : baseEnd_7588885 < baseStart_7588885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588915 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 4, 4]
def baseStart_7588915 : Nat := 118140960795 + 7588915 * 2 ^ 59
def prefixEnd_7588915 : Nat := 4983230072969 + 3 ^ 40 * 7588915 * 2
def baseEnd_7588915 : Nat := 1298920347038427022953907

theorem tailTrace_7588915 : CollatzResearch.WordTrace tailWord_7588915 prefixEnd_7588915 1298920347038427022953907 := by
  unfold tailWord_7588915
  simp only [CollatzResearch.WordTrace]
  refine ⟨276790469301664513340632199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184526979534443008893754799 276790469301664513340632199)
  ·
    refine ⟨415185703952496770010948299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276790469301664513340632199 415185703952496770010948299)
    ·
      refine ⟨622778555928745155016422449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415185703952496770010948299 622778555928745155016422449)
      ·
        refine ⟨467083916946558866262316837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622778555928745155016422449 467083916946558866262316837)
        ·
          refine ⟨87578234427479787424184407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 467083916946558866262316837 87578234427479787424184407)
          ·
            refine ⟨131367351641219681136276611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87578234427479787424184407 131367351641219681136276611)
            ·
              refine ⟨197051027461829521704414917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131367351641219681136276611 197051027461829521704414917)
              ·
                refine ⟨36947067649093035319577797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197051027461829521704414917 36947067649093035319577797)
                ·
                  refine ⟨6927575184204944122420837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36947067649093035319577797 6927575184204944122420837)
                  ·
                    refine ⟨1298920347038427022953907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6927575184204944122420837 1298920347038427022953907)
                    ·
                      rfl

theorem cell23_7588915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 4].length) (baseStart_7588915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588915 prefixEnd_7588915 := by exact prefixLift 7588915
  have htrace : WordTrace (prefixWord ++ tailWord_7588915) baseStart_7588915 baseEnd_7588915 := by
    simpa [prefixWord, tailWord_7588915, baseEnd_7588915] using wordTrace_append hprefix tailTrace_7588915
  have hstable : (prefixWord ++ tailWord_7588915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588915).length < 2 ^ (prefixWord ++ tailWord_7588915).sum := by decide
  have hdescent : baseEnd_7588915 < baseStart_7588915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588928 : List Nat := [2, 1, 1, 2, 2, 3, 12]
def baseStart_7588928 : Nat := 118140960795 + 7588928 * 2 ^ 59
def prefixEnd_7588928 : Nat := 4983230072969 + 3 ^ 40 * 7588928 * 2
def baseEnd_7588928 : Nat := 48108243411898636024681

theorem tailTrace_7588928 : CollatzResearch.WordTrace tailWord_7588928 prefixEnd_7588928 48108243411898636024681 := by
  unfold tailWord_7588928
  simp only [CollatzResearch.WordTrace]
  refine ⟨138395471725308708280427719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184527295633744944373903625 138395471725308708280427719)
  ·
    refine ⟨207593207587963062420641579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138395471725308708280427719 207593207587963062420641579)
    ·
      refine ⟨311389811381944593630962369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207593207587963062420641579 311389811381944593630962369)
      ·
        refine ⟨233542358536458445223221777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311389811381944593630962369 233542358536458445223221777)
        ·
          refine ⟨175156768902343833917416333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233542358536458445223221777 175156768902343833917416333)
          ·
            refine ⟨65683788338378937719031125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175156768902343833917416333 65683788338378937719031125)
            ·
              refine ⟨48108243411898636024681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 65683788338378937719031125 48108243411898636024681)
              ·
                rfl

theorem cell23_7588928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 12].length) (baseStart_7588928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588928 prefixEnd_7588928 := by exact prefixLift 7588928
  have htrace : WordTrace (prefixWord ++ tailWord_7588928) baseStart_7588928 baseEnd_7588928 := by
    simpa [prefixWord, tailWord_7588928, baseEnd_7588928] using wordTrace_append hprefix tailTrace_7588928
  have hstable : (prefixWord ++ tailWord_7588928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588928).length < 2 ^ (prefixWord ++ tailWord_7588928).sum := by decide
  have hdescent : baseEnd_7588928 < baseStart_7588928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588949 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_7588949 : Nat := 118140960795 + 7588949 * 2 ^ 59
def prefixEnd_7588949 : Nat := 4983230072969 + 3 ^ 40 * 7588949 * 2
def baseEnd_7588949 : Nat := 1298926166485844645278855

theorem tailTrace_7588949 : CollatzResearch.WordTrace tailWord_7588949 prefixEnd_7588949 1298926166485844645278855 := by
  unfold tailWord_7588949
  simp only [CollatzResearch.WordTrace]
  refine ⟨276791709383541337147369901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184527806255694224764913267 276791709383541337147369901)
  ·
    refine ⟨103796891018828001430263713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276791709383541337147369901 103796891018828001430263713)
    ·
      refine ⟨77847668264121001072697785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103796891018828001430263713 77847668264121001072697785)
      ·
        refine ⟨58385751198090750804523339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77847668264121001072697785 58385751198090750804523339)
        ·
          refine ⟨87578626797136126206785009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58385751198090750804523339 87578626797136126206785009)
          ·
            refine ⟨65683970097852094655088757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87578626797136126206785009 65683970097852094655088757)
            ·
              refine ⟨6157872196673633873914571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65683970097852094655088757 6157872196673633873914571)
              ·
                refine ⟨9236808295010450810871857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157872196673633873914571 9236808295010450810871857)
                ·
                  refine ⟨6927606221257838108153893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9236808295010450810871857 6927606221257838108153893)
                  ·
                    refine ⟨1298926166485844645278855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6927606221257838108153893 1298926166485844645278855)
                    ·
                      rfl

theorem cell23_7588949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_7588949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588949 prefixEnd_7588949 := by exact prefixLift 7588949
  have htrace : WordTrace (prefixWord ++ tailWord_7588949) baseStart_7588949 baseEnd_7588949 := by
    simpa [prefixWord, tailWord_7588949, baseEnd_7588949] using wordTrace_append hprefix tailTrace_7588949
  have hstable : (prefixWord ++ tailWord_7588949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588949).length < 2 ^ (prefixWord ++ tailWord_7588949).sum := by decide
  have hdescent : baseEnd_7588949 < baseStart_7588949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588962 : List Nat := [3, 3, 2, 2, 1, 2, 1, 9]
def baseStart_7588962 : Nat := 118140960795 + 7588962 * 2 ^ 59
def prefixEnd_7588962 : Nat := 4983230072969 + 3 ^ 40 * 7588962 * 2
def baseEnd_7588962 : Nat := 144325376840964532776815

theorem tailTrace_7588962 : CollatzResearch.WordTrace tailWord_7588962 prefixEnd_7588962 144325376840964532776815 := by
  unfold tailWord_7588962
  simp only [CollatzResearch.WordTrace]
  refine ⟨69198045883123560091898285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184528122354996160245062093 69198045883123560091898285)
  ·
    refine ⟨25949267206171335034461857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69198045883123560091898285 25949267206171335034461857)
    ·
      refine ⟨19461950404628501275846393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25949267206171335034461857 19461950404628501275846393)
      ·
        refine ⟨14596462803471375956884795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19461950404628501275846393 14596462803471375956884795)
        ·
          refine ⟨21894694205207063935327193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14596462803471375956884795 21894694205207063935327193)
          ·
            refine ⟨16421020653905297951495395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21894694205207063935327193 16421020653905297951495395)
            ·
              refine ⟨24631530980857946927243093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16421020653905297951495395 24631530980857946927243093)
              ·
                refine ⟨144325376840964532776815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24631530980857946927243093 144325376840964532776815)
                ·
                  rfl

theorem cell23_7588962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 9].length) (baseStart_7588962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588962 prefixEnd_7588962 := by exact prefixLift 7588962
  have htrace : WordTrace (prefixWord ++ tailWord_7588962) baseStart_7588962 baseEnd_7588962 := by
    simpa [prefixWord, tailWord_7588962, baseEnd_7588962] using wordTrace_append hprefix tailTrace_7588962
  have hstable : (prefixWord ++ tailWord_7588962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588962).length < 2 ^ (prefixWord ++ tailWord_7588962).sum := by decide
  have hdescent : baseEnd_7588962 < baseStart_7588962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588972 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 3]
def baseStart_7588972 : Nat := 118140960795 + 7588972 * 2 ^ 59
def prefixEnd_7588972 : Nat := 4983230072969 + 3 ^ 40 * 7588972 * 2
def baseEnd_7588972 : Nat := 3896790309512587345848959

theorem tailTrace_7588972 : CollatzResearch.WordTrace tailWord_7588972 prefixEnd_7588972 3896790309512587345848959 := by
  unfold tailWord_7588972
  simp only [CollatzResearch.WordTrace]
  refine ⟨138396274131229006037728585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184528365508305341383638113 138396274131229006037728585)
  ·
    refine ⟨103797205598421754528296439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138396274131229006037728585 103797205598421754528296439)
    ·
      refine ⟨155695808397632631792444659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103797205598421754528296439 155695808397632631792444659)
      ·
        refine ⟨233543712596448947688666989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155695808397632631792444659 233543712596448947688666989)
        ·
          refine ⟨87578892223668355383250121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233543712596448947688666989 87578892223668355383250121)
          ·
            refine ⟨65684169167751266537437591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87578892223668355383250121 65684169167751266537437591)
            ·
              refine ⟨98526253751626899806156387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65684169167751266537437591 98526253751626899806156387)
              ·
                refine ⟨147789380627440349709234581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98526253751626899806156387 147789380627440349709234581)
                ·
                  refine ⟨6927627216911266392620371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147789380627440349709234581 6927627216911266392620371)
                  ·
                    refine ⟨10391440825366899588930557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6927627216911266392620371 10391440825366899588930557)
                    ·
                      refine ⟨3896790309512587345848959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10391440825366899588930557 3896790309512587345848959)
                      ·
                        rfl

theorem cell23_7588972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_7588972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588972 prefixEnd_7588972 := by exact prefixLift 7588972
  have htrace : WordTrace (prefixWord ++ tailWord_7588972) baseStart_7588972 baseEnd_7588972 := by
    simpa [prefixWord, tailWord_7588972, baseEnd_7588972] using wordTrace_append hprefix tailTrace_7588972
  have hstable : (prefixWord ++ tailWord_7588972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588972).length < 2 ^ (prefixWord ++ tailWord_7588972).sum := by decide
  have hdescent : baseEnd_7588972 < baseStart_7588972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588973 : List Nat := [1, 5, 1, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_7588973 : Nat := 118140960795 + 7588973 * 2 ^ 59
def prefixEnd_7588973 : Nat := 4983230072969 + 3 ^ 40 * 7588973 * 2
def baseEnd_7588973 : Nat := 3896790822993241841936455

theorem tailTrace_7588973 : CollatzResearch.WordTrace tailWord_7588973 prefixEnd_7588973 3896790822993241841936455 := by
  unfold tailWord_7588973
  simp only [CollatzResearch.WordTrace]
  refine ⟨276792584735454389246243573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184528389823636259497495715 276792584735454389246243573)
  ·
    refine ⟨25949304818948848991835335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276792584735454389246243573 25949304818948848991835335)
    ·
      refine ⟨38923957228423273487753003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25949304818948848991835335 38923957228423273487753003)
      ·
        refine ⟨58385935842634910231629505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38923957228423273487753003 58385935842634910231629505)
        ·
          refine ⟨43789451881976182673722129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58385935842634910231629505 43789451881976182673722129)
          ·
            refine ⟨32842088911482137005291597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43789451881976182673722129 32842088911482137005291597)
            ·
              refine ⟨12315783341805801376984349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32842088911482137005291597 12315783341805801376984349)
              ·
                refine ⟨4618418753177175516369131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12315783341805801376984349 4618418753177175516369131)
                ·
                  refine ⟨6927628129765763274553697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618418753177175516369131 6927628129765763274553697)
                  ·
                    refine ⟨5195721097324322455915273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6927628129765763274553697 5195721097324322455915273)
                    ·
                      refine ⟨3896790822993241841936455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195721097324322455915273 3896790822993241841936455)
                      ·
                        rfl

theorem cell23_7588973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_7588973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588973 prefixEnd_7588973 := by exact prefixLift 7588973
  have htrace : WordTrace (prefixWord ++ tailWord_7588973) baseStart_7588973 baseEnd_7588973 := by
    simpa [prefixWord, tailWord_7588973, baseEnd_7588973] using wordTrace_append hprefix tailTrace_7588973
  have hstable : (prefixWord ++ tailWord_7588973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588973).length < 2 ^ (prefixWord ++ tailWord_7588973).sum := by decide
  have hdescent : baseEnd_7588973 < baseStart_7588973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588989 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_7588989 : Nat := 118140960795 + 7588989 * 2 ^ 59
def prefixEnd_7588989 : Nat := 4983230072969 + 3 ^ 40 * 7588989 * 2
def baseEnd_7588989 : Nat := 3896799038683713779336381

theorem tailTrace_7588989 : CollatzResearch.WordTrace tailWord_7588989 prefixEnd_7588989 3896799038683713779336381 := by
  unfold tailWord_7588989
  simp only [CollatzResearch.WordTrace]
  refine ⟨276793168303396423978826021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184528778868930949319217347 276793168303396423978826021)
  ·
    refine ⟨51898719056886829496029879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276793168303396423978826021 51898719056886829496029879)
    ·
      refine ⟨77848078585330244244044819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51898719056886829496029879 77848078585330244244044819)
      ·
        refine ⟨116772117877995366366067229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77848078585330244244044819 116772117877995366366067229)
        ·
          refine ⟨43789544204248262387275211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116772117877995366366067229 43789544204248262387275211)
          ·
            refine ⟨65684316306372393580912817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43789544204248262387275211 65684316306372393580912817)
            ·
              refine ⟨49263237229779295185684613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65684316306372393580912817 49263237229779295185684613)
              ·
                refine ⟨9236856980583617847315865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49263237229779295185684613 9236856980583617847315865)
                ·
                  refine ⟨6927642735437713385486899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9236856980583617847315865 6927642735437713385486899)
                  ·
                    refine ⟨10391464103156570078230349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6927642735437713385486899 10391464103156570078230349)
                    ·
                      refine ⟨3896799038683713779336381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10391464103156570078230349 3896799038683713779336381)
                      ·
                        rfl

theorem cell23_7588989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_7588989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588989 prefixEnd_7588989 := by exact prefixLift 7588989
  have htrace : WordTrace (prefixWord ++ tailWord_7588989) baseStart_7588989 baseEnd_7588989 := by
    simpa [prefixWord, tailWord_7588989, baseEnd_7588989] using wordTrace_append hprefix tailTrace_7588989
  have hstable : (prefixWord ++ tailWord_7588989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588989).length < 2 ^ (prefixWord ++ tailWord_7588989).sum := by decide
  have hdescent : baseEnd_7588989 < baseStart_7588989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7588995 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 4]
def baseStart_7588995 : Nat := 118140960795 + 7588995 * 2 ^ 59
def prefixEnd_7588995 : Nat := 4983230072969 + 3 ^ 40 * 7588995 * 2
def baseEnd_7588995 : Nat := 3896802119567640755861353

theorem tailTrace_7588995 : CollatzResearch.WordTrace tailWord_7588995 prefixEnd_7588995 3896802119567640755861353 := by
  unfold tailWord_7588995
  simp only [CollatzResearch.WordTrace]
  refine ⟨276793387141374687003544439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184528924760916458002362959 276793387141374687003544439)
  ·
    refine ⟨415190080712062030505316659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276793387141374687003544439 415190080712062030505316659)
    ·
      refine ⟨622785121068093045757974989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415190080712062030505316659 622785121068093045757974989)
      ·
        refine ⟨233544420400534892159240621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622785121068093045757974989 233544420400534892159240621)
        ·
          refine ⟨87579157650200584559715233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233544420400534892159240621 87579157650200584559715233)
          ·
            refine ⟨65684368237650438419786425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87579157650200584559715233 65684368237650438419786425)
            ·
              refine ⟨49263276178237828814839819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65684368237650438419786425 49263276178237828814839819)
              ·
                refine ⟨73894914267356743222259729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49263276178237828814839819 73894914267356743222259729)
                ·
                  refine ⟨55421185700517557416694797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73894914267356743222259729 55421185700517557416694797)
                  ·
                    refine ⟨20782944637694084031260549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55421185700517557416694797 20782944637694084031260549)
                    ·
                      refine ⟨3896802119567640755861353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20782944637694084031260549 3896802119567640755861353)
                      ·
                        rfl

theorem cell23_7588995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_7588995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7588995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7588995 prefixEnd_7588995 := by exact prefixLift 7588995
  have htrace : WordTrace (prefixWord ++ tailWord_7588995) baseStart_7588995 baseEnd_7588995 := by
    simpa [prefixWord, tailWord_7588995, baseEnd_7588995] using wordTrace_append hprefix tailTrace_7588995
  have hstable : (prefixWord ++ tailWord_7588995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7588995).length < 2 ^ (prefixWord ++ tailWord_7588995).sum := by decide
  have hdescent : baseEnd_7588995 < baseStart_7588995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7588995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589006 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_7589006 : Nat := 118140960795 + 7589006 * 2 ^ 59
def prefixEnd_7589006 : Nat := 4983230072969 + 3 ^ 40 * 7589006 * 2
def baseEnd_7589006 : Nat := 3896807767854840212823803

theorem tailTrace_7589006 : CollatzResearch.WordTrace tailWord_7589006 prefixEnd_7589006 3896807767854840212823803 := by
  unfold tailWord_7589006
  simp only [CollatzResearch.WordTrace]
  refine ⟨34599223543041854485274359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184529192229556557254796581 34599223543041854485274359)
  ·
    refine ⟨51898835314562781727911539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34599223543041854485274359 51898835314562781727911539)
    ·
      refine ⟨77848252971844172591867309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51898835314562781727911539 77848252971844172591867309)
      ·
        refine ⟨29193094864441564721950241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77848252971844172591867309 29193094864441564721950241)
        ·
          refine ⟨21894821148331173541462681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29193094864441564721950241 21894821148331173541462681)
          ·
            refine ⟨16421115861248380156097011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21894821148331173541462681 16421115861248380156097011)
            ·
              refine ⟨24631673791872570234145517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16421115861248380156097011 24631673791872570234145517)
              ·
                refine ⟨9236877671952213837804569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24631673791872570234145517 9236877671952213837804569)
                ·
                  refine ⟨6927658253964160378353427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9236877671952213837804569 6927658253964160378353427)
                  ·
                    refine ⟨10391487380946240567530141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6927658253964160378353427 10391487380946240567530141)
                    ·
                      refine ⟨3896807767854840212823803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10391487380946240567530141 3896807767854840212823803)
                      ·
                        rfl

theorem cell23_7589006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_7589006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589006 prefixEnd_7589006 := by exact prefixLift 7589006
  have htrace : WordTrace (prefixWord ++ tailWord_7589006) baseStart_7589006 baseEnd_7589006 := by
    simpa [prefixWord, tailWord_7589006, baseEnd_7589006] using wordTrace_append hprefix tailTrace_7589006
  have hstable : (prefixWord ++ tailWord_7589006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589006).length < 2 ^ (prefixWord ++ tailWord_7589006).sum := by decide
  have hdescent : baseEnd_7589006 < baseStart_7589006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589016 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 1, 3, 2]
def baseStart_7589016 : Nat := 118140960795 + 7589016 * 2 ^ 59
def prefixEnd_7589016 : Nat := 4983230072969 + 3 ^ 40 * 7589016 * 2
def baseEnd_7589016 : Nat := 3896812902661385173698757

theorem tailTrace_7589016 : CollatzResearch.WordTrace tailWord_7589016 prefixEnd_7589016 3896812902661385173698757 := by
  unfold tailWord_7589016
  simp only [CollatzResearch.WordTrace]
  refine ⟨138397076537149303795029451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184529435382865738393372601 138397076537149303795029451)
  ·
    refine ⟨207595614805723955692544177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138397076537149303795029451 207595614805723955692544177)
    ·
      refine ⟨155696711104292966769408133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207595614805723955692544177 155696711104292966769408133)
      ·
        refine ⟨29193133332054931269264025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155696711104292966769408133 29193133332054931269264025)
        ·
          refine ⟨21894849999041198451948019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29193133332054931269264025 21894849999041198451948019)
          ·
            refine ⟨32842274998561797677922029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21894849999041198451948019 32842274998561797677922029)
            ·
              refine ⟨12315853124460674129220761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32842274998561797677922029 12315853124460674129220761)
              ·
                refine ⟨9236889843345505596915571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12315853124460674129220761 9236889843345505596915571)
                ·
                  refine ⟨13855334765018258395373357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236889843345505596915571 13855334765018258395373357)
                  ·
                    refine ⟨5195750536881846898265009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13855334765018258395373357 5195750536881846898265009)
                    ·
                      refine ⟨3896812902661385173698757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195750536881846898265009 3896812902661385173698757)
                      ·
                        rfl

theorem cell23_7589016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_7589016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589016 prefixEnd_7589016 := by exact prefixLift 7589016
  have htrace : WordTrace (prefixWord ++ tailWord_7589016) baseStart_7589016 baseEnd_7589016 := by
    simpa [prefixWord, tailWord_7589016, baseEnd_7589016] using wordTrace_append hprefix tailTrace_7589016
  have hstable : (prefixWord ++ tailWord_7589016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589016).length < 2 ^ (prefixWord ++ tailWord_7589016).sum := by decide
  have hdescent : baseEnd_7589016 < baseStart_7589016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589029 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 1, 4, 2]
def baseStart_7589029 : Nat := 118140960795 + 7589029 * 2 ^ 59
def prefixEnd_7589029 : Nat := 4983230072969 + 3 ^ 40 * 7589029 * 2
def baseEnd_7589029 : Nat := 3896819577909893622836197

theorem tailTrace_7589029 : CollatzResearch.WordTrace tailWord_7589029 prefixEnd_7589029 3896819577909893622836197 := by
  unfold tailWord_7589029
  simp only [CollatzResearch.WordTrace]
  refine ⟨276794627223251510810282141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184529751482167673873521427 276794627223251510810282141)
  ·
    refine ⟨103797985208719316553855803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276794627223251510810282141 103797985208719316553855803)
    ·
      refine ⟨155696977813078974830783705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103797985208719316553855803 155696977813078974830783705)
      ·
        refine ⟨116772733359809231123087779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155696977813078974830783705 116772733359809231123087779)
        ·
          refine ⟨175159100039713846684631669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116772733359809231123087779 175159100039713846684631669)
          ·
            refine ⟨16421165628723173126684219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175159100039713846684631669 16421165628723173126684219)
            ·
              refine ⟨24631748443084759690026329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16421165628723173126684219 24631748443084759690026329)
              ·
                refine ⟨18473811332313569767519747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24631748443084759690026329 18473811332313569767519747)
                ·
                  refine ⟨27710716998470354651279621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18473811332313569767519747 27710716998470354651279621)
                  ·
                    refine ⟨5195759437213191497114929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27710716998470354651279621 5195759437213191497114929)
                    ·
                      refine ⟨3896819577909893622836197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195759437213191497114929 3896819577909893622836197)
                      ·
                        rfl

theorem cell23_7589029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_7589029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589029 prefixEnd_7589029 := by exact prefixLift 7589029
  have htrace : WordTrace (prefixWord ++ tailWord_7589029) baseStart_7589029 baseEnd_7589029 := by
    simpa [prefixWord, tailWord_7589029, baseEnd_7589029] using wordTrace_append hprefix tailTrace_7589029
  have hstable : (prefixWord ++ tailWord_7589029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589029).length < 2 ^ (prefixWord ++ tailWord_7589029).sum := by decide
  have hdescent : baseEnd_7589029 < baseStart_7589029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589119 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 2, 4, 2]
def baseStart_7589119 : Nat := 118140960795 + 7589119 * 2 ^ 59
def prefixEnd_7589119 : Nat := 4983230072969 + 3 ^ 40 * 7589119 * 2
def baseEnd_7589119 : Nat := 3896865791168798270710783

theorem tailTrace_7589119 : CollatzResearch.WordTrace tailWord_7589119 prefixEnd_7589119 3896865791168798270710783 := by
  unfold tailWord_7589119
  simp only [CollatzResearch.WordTrace]
  refine ⟨276797909792925456181058411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184531939861950304120705607 276797909792925456181058411)
  ·
    refine ⟨415196864689388184271587617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276797909792925456181058411 415196864689388184271587617)
    ·
      refine ⟨311397648517041138203690713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415196864689388184271587617 311397648517041138203690713)
      ·
        refine ⟨233548236387780853652768035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311397648517041138203690713 233548236387780853652768035)
        ·
          refine ⟨350322354581671280479152053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233548236387780853652768035 350322354581671280479152053)
          ·
            refine ⟨32842720742031682544920505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350322354581671280479152053 32842720742031682544920505)
            ·
              refine ⟨24632040556523761908690379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32842720742031682544920505 24632040556523761908690379)
              ·
                refine ⟨36948060834785642863035569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24632040556523761908690379 36948060834785642863035569)
                ·
                  refine ⟨27711045626089232147276677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36948060834785642863035569 27711045626089232147276677)
                  ·
                    refine ⟨5195821054891731027614377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27711045626089232147276677 5195821054891731027614377)
                    ·
                      refine ⟨3896865791168798270710783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195821054891731027614377 3896865791168798270710783)
                      ·
                        rfl

theorem cell23_7589119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_7589119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589119 prefixEnd_7589119 := by exact prefixLift 7589119
  have htrace : WordTrace (prefixWord ++ tailWord_7589119) baseStart_7589119 baseEnd_7589119 := by
    simpa [prefixWord, tailWord_7589119, baseEnd_7589119] using wordTrace_append hprefix tailTrace_7589119
  have hstable : (prefixWord ++ tailWord_7589119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589119).length < 2 ^ (prefixWord ++ tailWord_7589119).sum := by decide
  have hdescent : baseEnd_7589119 < baseStart_7589119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589135 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_7589135 : Nat := 118140960795 + 7589135 * 2 ^ 59
def prefixEnd_7589135 : Nat := 4983230072969 + 3 ^ 40 * 7589135 * 2
def baseEnd_7589135 : Nat := 3896874006859270208110709

theorem tailTrace_7589135 : CollatzResearch.WordTrace tailWord_7589135 prefixEnd_7589135 3896874006859270208110709 := by
  unfold tailWord_7589135
  simp only [CollatzResearch.WordTrace]
  refine ⟨276798493360867490913640859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184532328907244993942427239 276798493360867490913640859)
  ·
    refine ⟨415197740041301236370461289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276798493360867490913640859 415197740041301236370461289)
    ·
      refine ⟨311398305030975927277845967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415197740041301236370461289 311398305030975927277845967)
      ·
        refine ⟨467097457546463890916768951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311398305030975927277845967 467097457546463890916768951)
        ·
          refine ⟨700646186319695836375153427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467097457546463890916768951 700646186319695836375153427)
          ·
            refine ⟨1050969279479543754562730141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700646186319695836375153427 1050969279479543754562730141)
            ·
              refine ⟨394113479804828907961023803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050969279479543754562730141 394113479804828907961023803)
              ·
                refine ⟨591170219707243361941535705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394113479804828907961023803 591170219707243361941535705)
                ·
                  refine ⟨443377664780432521456151779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591170219707243361941535705 443377664780432521456151779)
                  ·
                    refine ⟨665066497170648782184227669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443377664780432521456151779 665066497170648782184227669)
                    ·
                      refine ⟨3896874006859270208110709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 665066497170648782184227669 3896874006859270208110709)
                      ·
                        rfl

theorem cell23_7589135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_7589135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589135 prefixEnd_7589135 := by exact prefixLift 7589135
  have htrace : WordTrace (prefixWord ++ tailWord_7589135) baseStart_7589135 baseEnd_7589135 := by
    simpa [prefixWord, tailWord_7589135, baseEnd_7589135] using wordTrace_append hprefix tailTrace_7589135
  have hstable : (prefixWord ++ tailWord_7589135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589135).length < 2 ^ (prefixWord ++ tailWord_7589135).sum := by decide
  have hdescent : baseEnd_7589135 < baseStart_7589135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589196 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 2, 3, 2]
def baseStart_7589196 : Nat := 118140960795 + 7589196 * 2 ^ 59
def prefixEnd_7589196 : Nat := 4983230072969 + 3 ^ 40 * 7589196 * 2
def baseEnd_7589196 : Nat := 3896905329179194469447929

theorem tailTrace_7589196 : CollatzResearch.WordTrace tailWord_7589196 prefixEnd_7589196 3896905329179194469447929 := by
  unfold tailWord_7589196
  simp only [CollatzResearch.WordTrace]
  refine ⟨138400359106823249165805721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184533812142430998887740961 138400359106823249165805721)
  ·
    refine ⟨103800269330117436874354291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138400359106823249165805721 103800269330117436874354291)
    ·
      refine ⟨155700403995176155311531437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103800269330117436874354291 155700403995176155311531437)
      ·
        refine ⟨58387651498191058241824289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155700403995176155311531437 58387651498191058241824289)
        ·
          refine ⟨43790738623643293681368217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58387651498191058241824289 43790738623643293681368217)
          ·
            refine ⟨32843053967732470261026163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43790738623643293681368217 32843053967732470261026163)
            ·
              refine ⟨49264580951598705391539245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32843053967732470261026163 49264580951598705391539245)
              ·
                refine ⟨18474217856849514521827217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49264580951598705391539245 18474217856849514521827217)
                ·
                  refine ⟨13855663392637135891370413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18474217856849514521827217 13855663392637135891370413)
                  ·
                    refine ⟨5195873772238925959263905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13855663392637135891370413 5195873772238925959263905)
                    ·
                      refine ⟨3896905329179194469447929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195873772238925959263905 3896905329179194469447929)
                      ·
                        rfl

theorem cell23_7589196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_7589196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589196 prefixEnd_7589196 := by exact prefixLift 7589196
  have htrace : WordTrace (prefixWord ++ tailWord_7589196) baseStart_7589196 baseEnd_7589196 := by
    simpa [prefixWord, tailWord_7589196, baseEnd_7589196] using wordTrace_append hprefix tailTrace_7589196
  have hstable : (prefixWord ++ tailWord_7589196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589196).length < 2 ^ (prefixWord ++ tailWord_7589196).sum := by decide
  have hdescent : baseEnd_7589196 < baseStart_7589196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
