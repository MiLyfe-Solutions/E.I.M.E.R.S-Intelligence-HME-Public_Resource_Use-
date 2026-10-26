import V185TrunkScan23Chunk0677

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4009463 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 1, 6]
def baseStart_4009463 : Nat := 118140960795 + 4009463 * 2 ^ 59
def prefixEnd_4009463 : Nat := 4983230072969 + 3 ^ 40 * 4009463 * 2
def baseEnd_4009463 : Nat := 686260561805983897091107

theorem tailTrace_4009463 : CollatzResearch.WordTrace tailWord_4009463 prefixEnd_4009463 686260561805983897091107 := by
  unfold tailWord_4009463
  simp only [CollatzResearch.WordTrace]
  refine ⟨146237129473407787608841043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97491419648938525072560695 146237129473407787608841043)
  ·
    refine ⟨219355694210111681413261565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146237129473407787608841043 219355694210111681413261565)
    ·
      refine ⟨82258385328791880529973087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219355694210111681413261565 82258385328791880529973087)
      ·
        refine ⟨123387577993187820794959631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82258385328791880529973087 123387577993187820794959631)
        ·
          refine ⟨185081366989781731192439447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123387577993187820794959631 185081366989781731192439447)
          ·
            refine ⟨277622050484672596788659171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185081366989781731192439447 277622050484672596788659171)
            ·
              refine ⟨416433075727008895182988757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277622050484672596788659171 416433075727008895182988757)
              ·
                refine ⟨9760150212351770980851299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 416433075727008895182988757 9760150212351770980851299)
                ·
                  refine ⟨14640225318527656471276949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760150212351770980851299 14640225318527656471276949)
                  ·
                    refine ⟨686260561805983897091107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14640225318527656471276949 686260561805983897091107)
                    ·
                      rfl

theorem cell23_4009463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_4009463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009463 prefixEnd_4009463 := by exact prefixLift 4009463
  have htrace : WordTrace (prefixWord ++ tailWord_4009463) baseStart_4009463 baseEnd_4009463 := by
    simpa [prefixWord, tailWord_4009463, baseEnd_4009463] using wordTrace_append hprefix tailTrace_4009463
  have hstable : (prefixWord ++ tailWord_4009463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009463).length < 2 ^ (prefixWord ++ tailWord_4009463).sum := by decide
  have hdescent : baseEnd_4009463 < baseStart_4009463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009474 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4009474 : Nat := 118140960795 + 4009474 * 2 ^ 59
def prefixEnd_4009474 : Nat := 4983230072969 + 3 ^ 40 * 4009474 * 2
def baseEnd_4009474 : Nat := 2058787333705151148235771

theorem tailTrace_4009474 : CollatzResearch.WordTrace tailWord_4009474 prefixEnd_4009474 2058787333705151148235771 := by
  unfold tailWord_4009474
  simp only [CollatzResearch.WordTrace]
  refine ⟨36559382669091984121872869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97491687117578624324994317 36559382669091984121872869)
  ·
    refine ⟨6854884250454747022851163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36559382669091984121872869 6854884250454747022851163)
    ·
      refine ⟨10282326375682120534276745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6854884250454747022851163 10282326375682120534276745)
      ·
        refine ⟨7711744781761590400707559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10282326375682120534276745 7711744781761590400707559)
        ·
          refine ⟨11567617172642385601061339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7711744781761590400707559 11567617172642385601061339)
          ·
            refine ⟨17351425758963578401592009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11567617172642385601061339 17351425758963578401592009)
            ·
              refine ⟨13013569319222683801194007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17351425758963578401592009 13013569319222683801194007)
              ·
                refine ⟨19520353978834025701791011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13013569319222683801194007 19520353978834025701791011)
                ·
                  refine ⟨29280530968251038552686517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19520353978834025701791011 29280530968251038552686517)
                  ·
                    refine ⟨2745049778273534864314361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29280530968251038552686517 2745049778273534864314361)
                    ·
                      refine ⟨2058787333705151148235771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745049778273534864314361 2058787333705151148235771)
                      ·
                        rfl

theorem cell23_4009474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4009474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009474 prefixEnd_4009474 := by exact prefixLift 4009474
  have htrace : WordTrace (prefixWord ++ tailWord_4009474) baseStart_4009474 baseEnd_4009474 := by
    simpa [prefixWord, tailWord_4009474, baseEnd_4009474] using wordTrace_append hprefix tailTrace_4009474
  have hstable : (prefixWord ++ tailWord_4009474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009474).length < 2 ^ (prefixWord ++ tailWord_4009474).sum := by decide
  have hdescent : baseEnd_4009474 < baseStart_4009474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009480 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 4, 4]
def baseStart_4009480 : Nat := 118140960795 + 4009480 * 2 ^ 59
def prefixEnd_4009480 : Nat := 4983230072969 + 3 ^ 40 * 4009480 * 2
def baseEnd_4009480 : Nat := 686263471529692708253581

theorem tailTrace_4009480 : CollatzResearch.WordTrace tailWord_4009480 prefixEnd_4009480 686263471529692708253581 := by
  unfold tailWord_4009480
  simp only [CollatzResearch.WordTrace]
  refine ⟨73118874757173099756104947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97491833009564133008139929 73118874757173099756104947)
  ·
    refine ⟨109678312135759649634157421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73118874757173099756104947 109678312135759649634157421)
    ·
      refine ⟨41129367050909868612809033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109678312135759649634157421 41129367050909868612809033)
      ·
        refine ⟨30847025288182401459606775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41129367050909868612809033 30847025288182401459606775)
        ·
          refine ⟨46270537932273602189410163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30847025288182401459606775 46270537932273602189410163)
          ·
            refine ⟨69405806898410403284115245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46270537932273602189410163 69405806898410403284115245)
            ·
              refine ⟨26027177586903901231543217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69405806898410403284115245 26027177586903901231543217)
              ·
                refine ⟨19520383190177925923657413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26027177586903901231543217 19520383190177925923657413)
                ·
                  refine ⟨3660071848158361110685765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19520383190177925923657413 3660071848158361110685765)
                  ·
                    refine ⟨686263471529692708253581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660071848158361110685765 686263471529692708253581)
                    ·
                      rfl

theorem cell23_4009480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_4009480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009480 prefixEnd_4009480 := by exact prefixLift 4009480
  have htrace : WordTrace (prefixWord ++ tailWord_4009480) baseStart_4009480 baseEnd_4009480 := by
    simpa [prefixWord, tailWord_4009480, baseEnd_4009480] using wordTrace_append hprefix tailTrace_4009480
  have hstable : (prefixWord ++ tailWord_4009480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009480).length < 2 ^ (prefixWord ++ tailWord_4009480).sum := by decide
  have hdescent : baseEnd_4009480 < baseStart_4009480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009493 : List Nat := [1, 3, 2, 1, 3, 2, 11]
def baseStart_4009493 : Nat := 118140960795 + 4009493 * 2 ^ 59
def prefixEnd_4009493 : Nat := 4983230072969 + 3 ^ 40 * 4009493 * 2
def baseEnd_4009493 : Nat := 25417248022686253998743

theorem tailTrace_4009493 : CollatzResearch.WordTrace tailWord_4009493 prefixEnd_4009493 25417248022686253998743 := by
  unfold tailWord_4009493
  simp only [CollatzResearch.WordTrace]
  refine ⟨146238223663299102732433133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97492149108866068488288755 146238223663299102732433133)
  ·
    refine ⟨54839333873737163524662425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146238223663299102732433133 54839333873737163524662425)
    ·
      refine ⟨41129500405302872643496819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54839333873737163524662425 41129500405302872643496819)
      ·
        refine ⟨61694250607954308965245229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41129500405302872643496819 61694250607954308965245229)
        ·
          refine ⟨23135343977982865861966961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61694250607954308965245229 23135343977982865861966961)
          ·
            refine ⟨17351507983487149396475221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23135343977982865861966961 17351507983487149396475221)
            ·
              refine ⟨25417248022686253998743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17351507983487149396475221 25417248022686253998743)
              ·
                rfl

theorem cell23_4009493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 11].length) (baseStart_4009493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009493 prefixEnd_4009493 := by exact prefixLift 4009493
  have htrace : WordTrace (prefixWord ++ tailWord_4009493) baseStart_4009493 baseEnd_4009493 := by
    simpa [prefixWord, tailWord_4009493, baseEnd_4009493] using wordTrace_append hprefix tailTrace_4009493
  have hstable : (prefixWord ++ tailWord_4009493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009493).length < 2 ^ (prefixWord ++ tailWord_4009493).sum := by decide
  have hdescent : baseEnd_4009493 < baseStart_4009493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009520 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 3]
def baseStart_4009520 : Nat := 118140960795 + 4009520 * 2 ^ 59
def prefixEnd_4009520 : Nat := 4983230072969 + 3 ^ 40 * 4009520 * 2
def baseEnd_4009520 : Nat := 2058810953815257968260559

theorem tailTrace_4009520 : CollatzResearch.WordTrace tailWord_4009520 prefixEnd_4009520 2058810953815257968260559 := by
  unfold tailWord_4009520
  simp only [CollatzResearch.WordTrace]
  refine ⟨73119604217100643171833007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97492805622800857562444009 73119604217100643171833007)
  ·
    refine ⟨109679406325650964757749511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73119604217100643171833007 109679406325650964757749511)
    ·
      refine ⟨164519109488476447136624267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109679406325650964757749511 164519109488476447136624267)
      ·
        refine ⟨246778664232714670704936401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164519109488476447136624267 246778664232714670704936401)
        ·
          refine ⟨185083998174536003028702301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246778664232714670704936401 185083998174536003028702301)
          ·
            refine ⟨69406499315451001135763363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185083998174536003028702301 69406499315451001135763363)
            ·
              refine ⟨104109748973176501703645045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69406499315451001135763363 104109748973176501703645045)
              ·
                refine ⟨9760288966235297034716723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104109748973176501703645045 9760288966235297034716723)
                ·
                  refine ⟨14640433449352945552075085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760288966235297034716723 14640433449352945552075085)
                  ·
                    refine ⟨5490162543507354582028157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14640433449352945552075085 5490162543507354582028157)
                    ·
                      refine ⟨2058810953815257968260559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490162543507354582028157 2058810953815257968260559)
                      ·
                        rfl

theorem cell23_4009520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_4009520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009520 prefixEnd_4009520 := by exact prefixLift 4009520
  have htrace : WordTrace (prefixWord ++ tailWord_4009520) baseStart_4009520 baseEnd_4009520 := by
    simpa [prefixWord, tailWord_4009520, baseEnd_4009520] using wordTrace_append hprefix tailTrace_4009520
  have hstable : (prefixWord ++ tailWord_4009520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009520).length < 2 ^ (prefixWord ++ tailWord_4009520).sum := by decide
  have hdescent : baseEnd_4009520 < baseStart_4009520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009537 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_4009537 : Nat := 118140960795 + 4009537 * 2 ^ 59
def prefixEnd_4009537 : Nat := 4983230072969 + 3 ^ 40 * 4009537 * 2
def baseEnd_4009537 : Nat := 2058819682986384401747981

theorem tailTrace_4009537 : CollatzResearch.WordTrace tailWord_4009537 prefixEnd_4009537 2058819682986384401747981 := by
  unfold tailWord_4009537
  simp only [CollatzResearch.WordTrace]
  refine ⟨146239828475139698247034865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97493218983426465498023243 146239828475139698247034865)
  ·
    refine ⟨109679871356354773685276149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146239828475139698247034865 109679871356354773685276149)
    ·
      refine ⟨10282487939658260032994639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109679871356354773685276149 10282487939658260032994639)
      ·
        refine ⟨15423731909487390049491959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10282487939658260032994639 15423731909487390049491959)
        ·
          refine ⟨23135597864231085074237939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15423731909487390049491959 23135597864231085074237939)
          ·
            refine ⟨34703396796346627611356909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23135597864231085074237939 34703396796346627611356909)
            ·
              refine ⟨13013773798629985354258841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34703396796346627611356909 13013773798629985354258841)
              ·
                refine ⟨9760330348972489015694131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13013773798629985354258841 9760330348972489015694131)
                ·
                  refine ⟨14640495523458733523541197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760330348972489015694131 14640495523458733523541197)
                  ·
                    refine ⟨5490185821297025071327949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14640495523458733523541197 5490185821297025071327949)
                    ·
                      refine ⟨2058819682986384401747981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490185821297025071327949 2058819682986384401747981)
                      ·
                        rfl

theorem cell23_4009537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_4009537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009537 prefixEnd_4009537 := by exact prefixLift 4009537
  have htrace : WordTrace (prefixWord ++ tailWord_4009537) baseStart_4009537 baseEnd_4009537 := by
    simpa [prefixWord, tailWord_4009537, baseEnd_4009537] using wordTrace_append hprefix tailTrace_4009537
  have hstable : (prefixWord ++ tailWord_4009537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009537).length < 2 ^ (prefixWord ++ tailWord_4009537).sum := by decide
  have hdescent : baseEnd_4009537 < baseStart_4009537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009554 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_4009554 : Nat := 118140960795 + 4009554 * 2 ^ 59
def prefixEnd_4009554 : Nat := 4983230072969 + 3 ^ 40 * 4009554 * 2
def baseEnd_4009554 : Nat := 2058828412157510835235403

theorem tailTrace_4009554 : CollatzResearch.WordTrace tailWord_4009554 prefixEnd_4009554 2058828412157510835235403 := by
  unfold tailWord_4009554
  simp only [CollatzResearch.WordTrace]
  refine ⟨36560112129019527537600929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97493632344052073433602477 36560112129019527537600929)
  ·
    refine ⟨27420084096764645653200697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36560112129019527537600929 27420084096764645653200697)
    ·
      refine ⟨20565063072573484239900523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27420084096764645653200697 20565063072573484239900523)
      ·
        refine ⟨30847594608860226359850785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20565063072573484239900523 30847594608860226359850785)
        ·
          refine ⟨23135695956645169769888089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30847594608860226359850785 23135695956645169769888089)
          ·
            refine ⟨17351771967483877327416067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23135695956645169769888089 17351771967483877327416067)
            ·
              refine ⟨26027657951225815991124101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17351771967483877327416067 26027657951225815991124101)
              ·
                refine ⟨4880185865854840498335769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26027657951225815991124101 4880185865854840498335769)
                ·
                  refine ⟨3660139399391130373751827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4880185865854840498335769 3660139399391130373751827)
                  ·
                    refine ⟨5490209099086695560627741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3660139399391130373751827 5490209099086695560627741)
                    ·
                      refine ⟨2058828412157510835235403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490209099086695560627741 2058828412157510835235403)
                      ·
                        rfl

theorem cell23_4009554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_4009554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009554 prefixEnd_4009554 := by exact prefixLift 4009554
  have htrace : WordTrace (prefixWord ++ tailWord_4009554) baseStart_4009554 baseEnd_4009554 := by
    simpa [prefixWord, tailWord_4009554, baseEnd_4009554] using wordTrace_append hprefix tailTrace_4009554
  have hstable : (prefixWord ++ tailWord_4009554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009554).length < 2 ^ (prefixWord ++ tailWord_4009554).sum := by decide
  have hdescent : baseEnd_4009554 < baseStart_4009554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009564 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_4009564 : Nat := 118140960795 + 4009564 * 2 ^ 59
def prefixEnd_4009564 : Nat := 4983230072969 + 3 ^ 40 * 4009564 * 2
def baseEnd_4009564 : Nat := 2058833546964055796110357

theorem tailTrace_4009564 : CollatzResearch.WordTrace tailWord_4009564 prefixEnd_4009564 2058833546964055796110357 := by
  unfold tailWord_4009564
  simp only [CollatzResearch.WordTrace]
  refine ⟨73120406623020940929133873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97493875497361254572178497 73120406623020940929133873)
  ·
    refine ⟨54840304967265705696850405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73120406623020940929133873 54840304967265705696850405)
    ·
      refine ⟨10282557181362319818159451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54840304967265705696850405 10282557181362319818159451)
      ·
        refine ⟨15423835772043479727239177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10282557181362319818159451 15423835772043479727239177)
        ·
          refine ⟨11567876829032609795429383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15423835772043479727239177 11567876829032609795429383)
          ·
            refine ⟨17351815243548914693144075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11567876829032609795429383 17351815243548914693144075)
            ·
              refine ⟨26027722865323372039716113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17351815243548914693144075 26027722865323372039716113)
              ·
                refine ⟨19520792148992529029787085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26027722865323372039716113 19520792148992529029787085)
                ·
                  refine ⟨7320297055872198386170157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19520792148992529029787085 7320297055872198386170157)
                  ·
                    refine ⟨2745111395952074394813809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7320297055872198386170157 2745111395952074394813809)
                    ·
                      refine ⟨2058833546964055796110357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745111395952074394813809 2058833546964055796110357)
                      ·
                        rfl

theorem cell23_4009564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_4009564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009564 prefixEnd_4009564 := by exact prefixLift 4009564
  have htrace : WordTrace (prefixWord ++ tailWord_4009564) baseStart_4009564 baseEnd_4009564 := by
    simpa [prefixWord, tailWord_4009564, baseEnd_4009564] using wordTrace_append hprefix tailTrace_4009564
  have hstable : (prefixWord ++ tailWord_4009564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009564).length < 2 ^ (prefixWord ++ tailWord_4009564).sum := by decide
  have hdescent : baseEnd_4009564 < baseStart_4009564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009577 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 1, 4, 2]
def baseStart_4009577 : Nat := 118140960795 + 4009577 * 2 ^ 59
def prefixEnd_4009577 : Nat := 4983230072969 + 3 ^ 40 * 4009577 * 2
def baseEnd_4009577 : Nat := 2058840222212564245247797

theorem tailTrace_4009577 : CollatzResearch.WordTrace tailWord_4009577 prefixEnd_4009577 2058840222212564245247797 := by
  unfold tailWord_4009577
  simp only [CollatzResearch.WordTrace]
  refine ⟨146241287394994785078490985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97494191596663190052327323 146241287394994785078490985)
  ·
    refine ⟨109680965546246088808868239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146241287394994785078490985 109680965546246088808868239)
    ·
      refine ⟨164521448319369133213302359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109680965546246088808868239 164521448319369133213302359)
      ·
        refine ⟨246782172479053699819953539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164521448319369133213302359 246782172479053699819953539)
        ·
          refine ⟨370173258718580549729930309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246782172479053699819953539 370173258718580549729930309)
          ·
            refine ⟨69407486009733853074361933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370173258718580549729930309 69407486009733853074361933)
            ·
              refine ⟨26027807253650194902885725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69407486009733853074361933 26027807253650194902885725)
              ·
                refine ⟨9760427720118823088582147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26027807253650194902885725 9760427720118823088582147)
                ·
                  refine ⟨14640641580178234632873221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760427720118823088582147 14640641580178234632873221)
                  ·
                    refine ⟨2745120296283418993663729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14640641580178234632873221 2745120296283418993663729)
                    ·
                      refine ⟨2058840222212564245247797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745120296283418993663729 2058840222212564245247797)
                      ·
                        rfl

theorem cell23_4009577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 4, 2].length) (baseStart_4009577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009577 prefixEnd_4009577 := by exact prefixLift 4009577
  have htrace : WordTrace (prefixWord ++ tailWord_4009577) baseStart_4009577 baseEnd_4009577 := by
    simpa [prefixWord, tailWord_4009577, baseEnd_4009577] using wordTrace_append hprefix tailTrace_4009577
  have hstable : (prefixWord ++ tailWord_4009577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009577).length < 2 ^ (prefixWord ++ tailWord_4009577).sum := by decide
  have hdescent : baseEnd_4009577 < baseStart_4009577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009580 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_4009580 : Nat := 118140960795 + 4009580 * 2 ^ 59
def prefixEnd_4009580 : Nat := 4983230072969 + 3 ^ 40 * 4009580 * 2
def baseEnd_4009580 : Nat := 2058841762654527733510283

theorem tailTrace_4009580 : CollatzResearch.WordTrace tailWord_4009580 prefixEnd_4009580 2058841762654527733510283 := by
  unfold tailWord_4009580
  simp only [CollatzResearch.WordTrace]
  refine ⟨73120698406991958295425097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97494264542655944393900129 73120698406991958295425097)
  ·
    refine ⟨54840523805243968721568823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73120698406991958295425097 54840523805243968721568823)
    ·
      refine ⟨82260785707865953082353235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54840523805243968721568823 82260785707865953082353235)
      ·
        refine ⟨123391178561798929623529853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82260785707865953082353235 123391178561798929623529853)
        ·
          refine ⟨46271691960674598608823695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123391178561798929623529853 46271691960674598608823695)
          ·
            refine ⟨69407537941011897913235543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46271691960674598608823695 69407537941011897913235543)
            ·
              refine ⟨104111306911517846869853315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69407537941011897913235543 104111306911517846869853315)
              ·
                refine ⟨156166960367276770304779973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104111306911517846869853315 156166960367276770304779973)
                ·
                  refine ⟨29281305068864394432146245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156166960367276770304779973 29281305068864394432146245)
                  ·
                    refine ⟨5490244700412073956027421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29281305068864394432146245 5490244700412073956027421)
                    ·
                      refine ⟨2058841762654527733510283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490244700412073956027421 2058841762654527733510283)
                      ·
                        rfl

theorem cell23_4009580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_4009580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009580 prefixEnd_4009580 := by exact prefixLift 4009580
  have htrace : WordTrace (prefixWord ++ tailWord_4009580) baseStart_4009580 baseEnd_4009580 := by
    simpa [prefixWord, tailWord_4009580, baseEnd_4009580] using wordTrace_append hprefix tailTrace_4009580
  have hstable : (prefixWord ++ tailWord_4009580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009580).length < 2 ^ (prefixWord ++ tailWord_4009580).sum := by decide
  have hdescent : baseEnd_4009580 < baseStart_4009580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009628 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_4009628 : Nat := 118140960795 + 4009628 * 2 ^ 59
def prefixEnd_4009628 : Nat := 4983230072969 + 3 ^ 40 * 4009628 * 2
def baseEnd_4009628 : Nat := 2058866409725943545710063

theorem tailTrace_4009628 : CollatzResearch.WordTrace tailWord_4009628 prefixEnd_4009628 2058866409725943545710063 := by
  unfold tailWord_4009628
  simp only [CollatzResearch.WordTrace]
  refine ⟨73121573758905010394298769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97495431678540013859065025 73121573758905010394298769)
  ·
    refine ⟨54841180319178757795724077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73121573758905010394298769 54841180319178757795724077)
    ·
      refine ⟨20565442619692034173396529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54841180319178757795724077 20565442619692034173396529)
      ·
        refine ⟨15424081964769025630047397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20565442619692034173396529 15424081964769025630047397)
        ·
          refine ⟨2892015368394192305633887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15424081964769025630047397 2892015368394192305633887)
          ·
            refine ⟨4338023052591288458450831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892015368394192305633887 4338023052591288458450831)
            ·
              refine ⟨6507034578886932687676247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338023052591288458450831 6507034578886932687676247)
              ·
                refine ⟨9760551868330399031514371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507034578886932687676247 9760551868330399031514371)
                ·
                  refine ⟨14640827802495598547271557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760551868330399031514371 14640827802495598547271557)
                  ·
                    refine ⟨2745155212967924727613417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14640827802495598547271557 2745155212967924727613417)
                    ·
                      refine ⟨2058866409725943545710063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745155212967924727613417 2058866409725943545710063)
                      ·
                        rfl

theorem cell23_4009628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_4009628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009628 prefixEnd_4009628 := by exact prefixLift 4009628
  have htrace : WordTrace (prefixWord ++ tailWord_4009628) baseStart_4009628 baseEnd_4009628 := by
    simpa [prefixWord, tailWord_4009628, baseEnd_4009628] using wordTrace_append hprefix tailTrace_4009628
  have hstable : (prefixWord ++ tailWord_4009628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009628).length < 2 ^ (prefixWord ++ tailWord_4009628).sum := by decide
  have hdescent : baseEnd_4009628 < baseStart_4009628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009637 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 2, 5, 2]
def baseStart_4009637 : Nat := 118140960795 + 4009637 * 2 ^ 59
def prefixEnd_4009637 : Nat := 4983230072969 + 3 ^ 40 * 4009637 * 2
def baseEnd_4009637 : Nat := 2058871031051834010497521

theorem tailTrace_4009637 : CollatzResearch.WordTrace tailWord_4009637 prefixEnd_4009637 2058871031051834010497521 := by
  unfold tailWord_4009637
  simp only [CollatzResearch.WordTrace]
  refine ⟨146243475774777415325675165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97495650516518276883783443 146243475774777415325675165)
  ·
    refine ⟨54841303415541530747128187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146243475774777415325675165 54841303415541530747128187)
    ·
      refine ⟨82261955123312296120692281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54841303415541530747128187 82261955123312296120692281)
      ·
        refine ⟨61696466342484222090519211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82261955123312296120692281 61696466342484222090519211)
        ·
          refine ⟨92544699513726333135778817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61696466342484222090519211 92544699513726333135778817)
          ·
            refine ⟨69408524635294749851834113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92544699513726333135778817 69408524635294749851834113)
            ·
              refine ⟨52056393476471062388875585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69408524635294749851834113 52056393476471062388875585)
              ·
                refine ⟨39042295107353296791656689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52056393476471062388875585 39042295107353296791656689)
                ·
                  refine ⟨29281721330514972593742517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39042295107353296791656689 29281721330514972593742517)
                  ·
                    refine ⟨2745161374735778680663361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29281721330514972593742517 2745161374735778680663361)
                    ·
                      refine ⟨2058871031051834010497521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745161374735778680663361 2058871031051834010497521)
                      ·
                        rfl

theorem cell23_4009637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_4009637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009637 prefixEnd_4009637 := by exact prefixLift 4009637
  have htrace : WordTrace (prefixWord ++ tailWord_4009637) baseStart_4009637 baseEnd_4009637 := by
    simpa [prefixWord, tailWord_4009637, baseEnd_4009637] using wordTrace_append hprefix tailTrace_4009637
  have hstable : (prefixWord ++ tailWord_4009637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009637).length < 2 ^ (prefixWord ++ tailWord_4009637).sum := by decide
  have hdescent : baseEnd_4009637 < baseStart_4009637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009680 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_4009680 : Nat := 118140960795 + 4009680 * 2 ^ 59
def prefixEnd_4009680 : Nat := 4983230072969 + 3 ^ 40 * 4009680 * 2
def baseEnd_4009680 : Nat := 2058893110719977342259823

theorem tailTrace_4009680 : CollatzResearch.WordTrace tailWord_4009680 prefixEnd_4009680 2058893110719977342259823 := by
  unfold tailWord_4009680
  simp only [CollatzResearch.WordTrace]
  refine ⟨73122522056810816834745247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97496696075747755779660329 73122522056810816834745247)
  ·
    refine ⟨109683783085216225252117871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73122522056810816834745247 109683783085216225252117871)
    ·
      refine ⟨164525674627824337878176807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109683783085216225252117871 164525674627824337878176807)
      ·
        refine ⟨246788511941736506817265211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164525674627824337878176807 246788511941736506817265211)
        ·
          refine ⟨370182767912604760225897817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246788511941736506817265211 370182767912604760225897817)
          ·
            refine ⟨277637075934453570169423363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370182767912604760225897817 277637075934453570169423363)
            ·
              refine ⟨416455613901680355254135045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277637075934453570169423363 416455613901680355254135045)
              ·
                refine ⟨78085427606565066610150321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416455613901680355254135045 78085427606565066610150321)
                ·
                  refine ⟨58564070704923799957612741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78085427606565066610150321 58564070704923799957612741)
                  ·
                    refine ⟨10980763257173212492052389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58564070704923799957612741 10980763257173212492052389)
                    ·
                      refine ⟨2058893110719977342259823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10980763257173212492052389 2058893110719977342259823)
                      ·
                        rfl

theorem cell23_4009680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_4009680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009680 prefixEnd_4009680 := by exact prefixLift 4009680
  have htrace : WordTrace (prefixWord ++ tailWord_4009680) baseStart_4009680 baseEnd_4009680 := by
    simpa [prefixWord, tailWord_4009680, baseEnd_4009680] using wordTrace_append hprefix tailTrace_4009680
  have hstable : (prefixWord ++ tailWord_4009680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009680).length < 2 ^ (prefixWord ++ tailWord_4009680).sum := by decide
  have hdescent : baseEnd_4009680 < baseStart_4009680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009687 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_4009687 : Nat := 118140960795 + 4009687 * 2 ^ 59
def prefixEnd_4009687 : Nat := 4983230072969 + 3 ^ 40 * 4009687 * 2
def baseEnd_4009687 : Nat := 2058896705084558814872291

theorem tailTrace_4009687 : CollatzResearch.WordTrace tailWord_4009687 prefixEnd_4009687 2058896705084558814872291 := by
  unfold tailWord_4009687
  simp only [CollatzResearch.WordTrace]
  refine ⟨146245299424596273864995315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97496866283064182576663543 146245299424596273864995315)
  ·
    refine ⟨219367949136894410797492973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146245299424596273864995315 219367949136894410797492973)
    ·
      refine ⟨82262980926335404049059865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219367949136894410797492973 82262980926335404049059865)
      ·
        refine ⟨61697235694751553036794899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82262980926335404049059865 61697235694751553036794899)
        ·
          refine ⟨92545853542127329555192349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61697235694751553036794899 92545853542127329555192349)
          ·
            refine ⟨34704695078297748583197131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92545853542127329555192349 34704695078297748583197131)
            ·
              refine ⟨52057042617446622874795697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34704695078297748583197131 52057042617446622874795697)
              ·
                refine ⟨39042781963084967156096773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52057042617446622874795697 39042781963084967156096773)
                ·
                  refine ⟨7320521618078431341768145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39042781963084967156096773 7320521618078431341768145)
                  ·
                    refine ⟨5490391213558823506326109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7320521618078431341768145 5490391213558823506326109)
                    ·
                      refine ⟨2058896705084558814872291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490391213558823506326109 2058896705084558814872291)
                      ·
                        rfl

theorem cell23_4009687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_4009687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009687 prefixEnd_4009687 := by exact prefixLift 4009687
  have htrace : WordTrace (prefixWord ++ tailWord_4009687) baseStart_4009687 baseEnd_4009687 := by
    simpa [prefixWord, tailWord_4009687, baseEnd_4009687] using wordTrace_append hprefix tailTrace_4009687
  have hstable : (prefixWord ++ tailWord_4009687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009687).length < 2 ^ (prefixWord ++ tailWord_4009687).sum := by decide
  have hdescent : baseEnd_4009687 < baseStart_4009687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009704 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_4009704 : Nat := 118140960795 + 4009704 * 2 ^ 59
def prefixEnd_4009704 : Nat := 4983230072969 + 3 ^ 40 * 4009704 * 2
def baseEnd_4009704 : Nat := 2058905434255685248359713

theorem tailTrace_4009704 : CollatzResearch.WordTrace tailWord_4009704 prefixEnd_4009704 2058905434255685248359713 := by
  unfold tailWord_4009704
  simp only [CollatzResearch.WordTrace]
  refine ⟨73122959732767342884182083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97497279643689790512242777 73122959732767342884182083)
  ·
    refine ⟨109684439599151014326273125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73122959732767342884182083 109684439599151014326273125)
    ·
      refine ⟨20565832424840815186176211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109684439599151014326273125 20565832424840815186176211)
      ·
        refine ⟨30848748637261222779264317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20565832424840815186176211 30848748637261222779264317)
        ·
          refine ⟨11568280738972958542224119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30848748637261222779264317 11568280738972958542224119)
          ·
            refine ⟨17352421108459437813336179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11568280738972958542224119 17352421108459437813336179)
            ·
              refine ⟨26028631662689156720004269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17352421108459437813336179 26028631662689156720004269)
              ·
                refine ⟨9760736873508433770001601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26028631662689156720004269 9760736873508433770001601)
                ·
                  refine ⟨7320552655131325327501201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9760736873508433770001601 7320552655131325327501201)
                  ·
                    refine ⟨5490414491348493995625901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7320552655131325327501201 5490414491348493995625901)
                    ·
                      refine ⟨2058905434255685248359713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490414491348493995625901 2058905434255685248359713)
                      ·
                        rfl

theorem cell23_4009704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_4009704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009704 prefixEnd_4009704 := by exact prefixLift 4009704
  have htrace : WordTrace (prefixWord ++ tailWord_4009704) baseStart_4009704 baseEnd_4009704 := by
    simpa [prefixWord, tailWord_4009704, baseEnd_4009704] using wordTrace_append hprefix tailTrace_4009704
  have hstable : (prefixWord ++ tailWord_4009704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009704).length < 2 ^ (prefixWord ++ tailWord_4009704).sum := by decide
  have hdescent : baseEnd_4009704 < baseStart_4009704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009751 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 3]
def baseStart_4009751 : Nat := 118140960795 + 4009751 * 2 ^ 59
def prefixEnd_4009751 : Nat := 4983230072969 + 3 ^ 40 * 4009751 * 2
def baseEnd_4009751 : Nat := 2058929567846446564471997

theorem tailTrace_4009751 : CollatzResearch.WordTrace tailWord_4009751 prefixEnd_4009751 2058929567846446564471997 := by
  unfold tailWord_4009751
  simp only [CollatzResearch.WordTrace]
  refine ⟨146247633696364412795325107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97498422464242941863550071 146247633696364412795325107)
  ·
    refine ⟨219371450544546619192987661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146247633696364412795325107 219371450544546619192987661)
    ·
      refine ⟨82264293954204982197370373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219371450544546619192987661 82264293954204982197370373)
      ·
        refine ⟨15424555116413434162006945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82264293954204982197370373 15424555116413434162006945)
        ·
          refine ⟨11568416337310075621505209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15424555116413434162006945 11568416337310075621505209)
          ·
            refine ⟨8676312252982556716128907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11568416337310075621505209 8676312252982556716128907)
            ·
              refine ⟨13014468379473835074193361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8676312252982556716128907 13014468379473835074193361)
              ·
                refine ⟨9760851284605376305645021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13014468379473835074193361 9760851284605376305645021)
                ·
                  refine ⟨3660319231727016114616883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9760851284605376305645021 3660319231727016114616883)
                  ·
                    refine ⟨5490478847590524171925325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3660319231727016114616883 5490478847590524171925325)
                    ·
                      refine ⟨2058929567846446564471997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490478847590524171925325 2058929567846446564471997)
                      ·
                        rfl

theorem cell23_4009751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_4009751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009751 prefixEnd_4009751 := by exact prefixLift 4009751
  have htrace : WordTrace (prefixWord ++ tailWord_4009751) baseStart_4009751 baseEnd_4009751 := by
    simpa [prefixWord, tailWord_4009751, baseEnd_4009751] using wordTrace_append hprefix tailTrace_4009751
  have hstable : (prefixWord ++ tailWord_4009751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009751).length < 2 ^ (prefixWord ++ tailWord_4009751).sum := by decide
  have hdescent : baseEnd_4009751 < baseStart_4009751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009761 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_4009761 : Nat := 118140960795 + 4009761 * 2 ^ 59
def prefixEnd_4009761 : Nat := 4983230072969 + 3 ^ 40 * 4009761 * 2
def baseEnd_4009761 : Nat := 2058934702652991525346951

theorem tailTrace_4009761 : CollatzResearch.WordTrace tailWord_4009761 prefixEnd_4009761 2058934702652991525346951 := by
  unfold tailWord_4009761
  simp only [CollatzResearch.WordTrace]
  refine ⟨146247998426328184503189137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97498665617552123002126091 146247998426328184503189137)
  ·
    refine ⟨109685998819746138377391853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146247998426328184503189137 109685998819746138377391853)
    ·
      refine ⟨41132249557404801891521945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109685998819746138377391853 41132249557404801891521945)
      ·
        refine ⟨30849187168053601418641459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41132249557404801891521945 30849187168053601418641459)
        ·
          refine ⟨46273780752080402127962189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30849187168053601418641459 46273780752080402127962189)
          ·
            refine ⟨17352667782030150797985821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46273780752080402127962189 17352667782030150797985821)
            ·
              refine ⟨6507250418261306549244683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17352667782030150797985821 6507250418261306549244683)
              ·
                refine ⟨9760875627391959823867025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507250418261306549244683 9760875627391959823867025)
                ·
                  refine ⟨7320656720543969867900269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9760875627391959823867025 7320656720543969867900269)
                  ·
                    refine ⟨2745246270203988700462601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7320656720543969867900269 2745246270203988700462601)
                    ·
                      refine ⟨2058934702652991525346951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745246270203988700462601 2058934702652991525346951)
                      ·
                        rfl

theorem cell23_4009761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_4009761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009761 prefixEnd_4009761 := by exact prefixLift 4009761
  have htrace : WordTrace (prefixWord ++ tailWord_4009761) baseStart_4009761 baseEnd_4009761 := by
    simpa [prefixWord, tailWord_4009761, baseEnd_4009761] using wordTrace_append hprefix tailTrace_4009761
  have hstable : (prefixWord ++ tailWord_4009761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009761).length < 2 ^ (prefixWord ++ tailWord_4009761).sum := by decide
  have hdescent : baseEnd_4009761 < baseStart_4009761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009768 : List Nat := [2, 1, 5, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_4009768 : Nat := 118140960795 + 4009768 * 2 ^ 59
def prefixEnd_4009768 : Nat := 4983230072969 + 3 ^ 40 * 4009768 * 2
def baseEnd_4009768 : Nat := 2058938297017572997959419

theorem tailTrace_4009768 : CollatzResearch.WordTrace tailWord_4009768 prefixEnd_4009768 2058938297017572997959419 := by
  unfold tailWord_4009768
  simp only [CollatzResearch.WordTrace]
  refine ⟨73124126868651412349346979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97498835824868549799129305 73124126868651412349346979)
  ·
    refine ⟨109686190302977118524020469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73124126868651412349346979 109686190302977118524020469)
    ·
      refine ⟨10283080340904104861626919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109686190302977118524020469 10283080340904104861626919)
      ·
        refine ⟨15424620511356157292440379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10283080340904104861626919 15424620511356157292440379)
        ·
          refine ⟨23136930767034235938660569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15424620511356157292440379 23136930767034235938660569)
          ·
            refine ⟨17352698075275676953995427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23136930767034235938660569 17352698075275676953995427)
            ·
              refine ⟨26029047112913515430993141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17352698075275676953995427 26029047112913515430993141)
              ·
                refine ⟨2440223166835642071655607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26029047112913515430993141 2440223166835642071655607)
                ·
                  refine ⟨3660334750253463107483411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440223166835642071655607 3660334750253463107483411)
                  ·
                    refine ⟨5490502125380194661225117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3660334750253463107483411 5490502125380194661225117)
                    ·
                      refine ⟨2058938297017572997959419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490502125380194661225117 2058938297017572997959419)
                      ·
                        rfl

theorem cell23_4009768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_4009768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009768 prefixEnd_4009768 := by exact prefixLift 4009768
  have htrace : WordTrace (prefixWord ++ tailWord_4009768) baseStart_4009768 baseEnd_4009768 := by
    simpa [prefixWord, tailWord_4009768, baseEnd_4009768] using wordTrace_append hprefix tailTrace_4009768
  have hstable : (prefixWord ++ tailWord_4009768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009768).length < 2 ^ (prefixWord ++ tailWord_4009768).sum := by decide
  have hdescent : baseEnd_4009768 < baseStart_4009768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009784 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 4, 4]
def baseStart_4009784 : Nat := 118140960795 + 4009784 * 2 ^ 59
def prefixEnd_4009784 : Nat := 4983230072969 + 3 ^ 40 * 4009784 * 2
def baseEnd_4009784 : Nat := 686315504236014978453115

theorem tailTrace_4009784 : CollatzResearch.WordTrace tailWord_4009784 prefixEnd_4009784 686315504236014978453115 := by
  unfold tailWord_4009784
  simp only [CollatzResearch.WordTrace]
  refine ⟨73124418652622429715638203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97499224870163239620850937 73124418652622429715638203)
  ·
    refine ⟨109686627978933644573457305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73124418652622429715638203 109686627978933644573457305)
    ·
      refine ⟨82264970984200233430092979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109686627978933644573457305 82264970984200233430092979)
      ·
        refine ⟨123397456476300350145139469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82264970984200233430092979 123397456476300350145139469)
        ·
          refine ⟨46274046178612631304427301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123397456476300350145139469 46274046178612631304427301)
          ·
            refine ⟨8676383658489868369580119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46274046178612631304427301 8676383658489868369580119)
            ·
              refine ⟨13014575487734802554370179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8676383658489868369580119 13014575487734802554370179)
              ·
                refine ⟨19521863231602203831555269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13014575487734802554370179 19521863231602203831555269)
                ·
                  refine ⟨3660349355925413218416613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19521863231602203831555269 3660349355925413218416613)
                  ·
                    refine ⟨686315504236014978453115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660349355925413218416613 686315504236014978453115)
                    ·
                      rfl

theorem cell23_4009784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_4009784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009784 prefixEnd_4009784 := by exact prefixLift 4009784
  have htrace : WordTrace (prefixWord ++ tailWord_4009784) baseStart_4009784 baseEnd_4009784 := by
    simpa [prefixWord, tailWord_4009784, baseEnd_4009784] using wordTrace_append hprefix tailTrace_4009784
  have hstable : (prefixWord ++ tailWord_4009784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009784).length < 2 ^ (prefixWord ++ tailWord_4009784).sum := by decide
  have hdescent : baseEnd_4009784 < baseStart_4009784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009801 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 2, 4]
def baseStart_4009801 : Nat := 118140960795 + 4009801 * 2 ^ 59
def prefixEnd_4009801 : Nat := 4983230072969 + 3 ^ 40 * 4009801 * 2
def baseEnd_4009801 : Nat := 686318413959723789615589

theorem tailTrace_4009801 : CollatzResearch.WordTrace tailWord_4009801 prefixEnd_4009801 686318413959723789615589 := by
  unfold tailWord_4009801
  simp only [CollatzResearch.WordTrace]
  refine ⟨146249457346183271334645257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97499638230788847556430171 146249457346183271334645257)
  ·
    refine ⟨109687093009637453500983943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146249457346183271334645257 109687093009637453500983943)
    ·
      refine ⟨164530639514456180251475915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109687093009637453500983943 164530639514456180251475915)
      ·
        refine ⟨246795959271684270377213873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164530639514456180251475915 246795959271684270377213873)
        ·
          refine ⟨185096969453763202782910405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246795959271684270377213873 185096969453763202782910405)
          ·
            refine ⟨34705681772580600521795701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185096969453763202782910405 34705681772580600521795701)
            ·
              refine ⟨3253657666179431298918347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34705681772580600521795701 3253657666179431298918347)
              ·
                refine ⟨4880486499269146948377521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3253657666179431298918347 4880486499269146948377521)
                ·
                  refine ⟨3660364874451860211283141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4880486499269146948377521 3660364874451860211283141)
                  ·
                    refine ⟨686318413959723789615589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660364874451860211283141 686318413959723789615589)
                    ·
                      rfl

theorem cell23_4009801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 4].length) (baseStart_4009801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009801 prefixEnd_4009801 := by exact prefixLift 4009801
  have htrace : WordTrace (prefixWord ++ tailWord_4009801) baseStart_4009801 baseEnd_4009801 := by
    simpa [prefixWord, tailWord_4009801, baseEnd_4009801] using wordTrace_append hprefix tailTrace_4009801
  have hstable : (prefixWord ++ tailWord_4009801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009801).length < 2 ^ (prefixWord ++ tailWord_4009801).sum := by decide
  have hdescent : baseEnd_4009801 < baseStart_4009801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009804 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_4009804 : Nat := 118140960795 + 4009804 * 2 ^ 59
def prefixEnd_4009804 : Nat := 4983230072969 + 3 ^ 40 * 4009804 * 2
def baseEnd_4009804 : Nat := 2058956782321134857109253

theorem tailTrace_4009804 : CollatzResearch.WordTrace tailWord_4009804 prefixEnd_4009804 2058956782321134857109253 := by
  unfold tailWord_4009804
  simp only [CollatzResearch.WordTrace]
  refine ⟨73124783382586201423502233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97499711176781601898002977 73124783382586201423502233)
  ·
    refine ⟨54843587536939651067626675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73124783382586201423502233 54843587536939651067626675)
    ·
      refine ⟨82265381305409476601440013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54843587536939651067626675 82265381305409476601440013)
      ·
        refine ⟨30849517989528553725540005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82265381305409476601440013 30849517989528553725540005)
        ·
          refine ⟨5784284623036603823538751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30849517989528553725540005 5784284623036603823538751)
          ·
            refine ⟨8676426934554905735308127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5784284623036603823538751 8676426934554905735308127)
            ·
              refine ⟨13014640401832358602962191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8676426934554905735308127 13014640401832358602962191)
              ·
                refine ⟨19521960602748537904443287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13014640401832358602962191 19521960602748537904443287)
                ·
                  refine ⟨29282940904122806856664931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19521960602748537904443287 29282940904122806856664931)
                  ·
                    refine ⟨43924411356184210284997397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29282940904122806856664931 43924411356184210284997397)
                    ·
                      refine ⟨2058956782321134857109253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43924411356184210284997397 2058956782321134857109253)
                      ·
                        rfl

theorem cell23_4009804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_4009804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009804 prefixEnd_4009804 := by exact prefixLift 4009804
  have htrace : WordTrace (prefixWord ++ tailWord_4009804) baseStart_4009804 baseEnd_4009804 := by
    simpa [prefixWord, tailWord_4009804, baseEnd_4009804] using wordTrace_append hprefix tailTrace_4009804
  have hstable : (prefixWord ++ tailWord_4009804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009804).length < 2 ^ (prefixWord ++ tailWord_4009804).sum := by decide
  have hdescent : baseEnd_4009804 < baseStart_4009804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009841 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 3]
def baseStart_4009841 : Nat := 118140960795 + 4009841 * 2 ^ 59
def prefixEnd_4009841 : Nat := 4983230072969 + 3 ^ 40 * 4009841 * 2
def baseEnd_4009841 : Nat := 2058975781105351212346583

theorem tailTrace_4009841 : CollatzResearch.WordTrace tailWord_4009841 prefixEnd_4009841 2058975781105351212346583 := by
  unfold tailWord_4009841
  simp only [CollatzResearch.WordTrace]
  refine ⟨146250916266038358166101377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97500610844025572110734251 146250916266038358166101377)
  ·
    refine ⟨109688187199528768624576033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146250916266038358166101377 109688187199528768624576033)
    ·
      refine ⟨82266140399646576468432025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109688187199528768624576033 82266140399646576468432025)
      ·
        refine ⟨61699605299734932351324019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82266140399646576468432025 61699605299734932351324019)
        ·
          refine ⟨92549407949602398526986029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61699605299734932351324019 92549407949602398526986029)
          ·
            refine ⟨34706027981100899447619761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92549407949602398526986029 34706027981100899447619761)
            ·
              refine ⟨26029520985825674585714821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34706027981100899447619761 26029520985825674585714821)
              ·
                refine ⟨4880535184842313984821529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26029520985825674585714821 4880535184842313984821529)
                ·
                  refine ⟨3660401388631735488616147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4880535184842313984821529 3660401388631735488616147)
                  ·
                    refine ⟨5490602082947603232924221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3660401388631735488616147 5490602082947603232924221)
                    ·
                      refine ⟨2058975781105351212346583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490602082947603232924221 2058975781105351212346583)
                      ·
                        rfl

theorem cell23_4009841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_4009841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009841 prefixEnd_4009841 := by exact prefixLift 4009841
  have htrace : WordTrace (prefixWord ++ tailWord_4009841) baseStart_4009841 baseEnd_4009841 := by
    simpa [prefixWord, tailWord_4009841, baseEnd_4009841] using wordTrace_append hprefix tailTrace_4009841
  have hstable : (prefixWord ++ tailWord_4009841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009841).length < 2 ^ (prefixWord ++ tailWord_4009841).sum := by decide
  have hdescent : baseEnd_4009841 < baseStart_4009841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009881 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 6, 2, 2]
def baseStart_4009881 : Nat := 118140960795 + 4009881 * 2 ^ 59
def prefixEnd_4009881 : Nat := 4983230072969 + 3 ^ 40 * 4009881 * 2
def baseEnd_4009881 : Nat := 2058996320331531055846399

theorem tailTrace_4009881 : CollatzResearch.WordTrace tailWord_4009881 prefixEnd_4009881 2058996320331531055846399 := by
  unfold tailWord_4009881
  simp only [CollatzResearch.WordTrace]
  refine ⟨146252375185893444997557497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97501583457262296665038331 146252375185893444997557497)
  ·
    refine ⟨109689281389420083748168123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146252375185893444997557497 109689281389420083748168123)
    ·
      refine ⟨164533922084130125622252185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109689281389420083748168123 164533922084130125622252185)
      ·
        refine ⟨123400441563097594216689139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164533922084130125622252185 123400441563097594216689139)
        ·
          refine ⟨185100662344646391325033709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123400441563097594216689139 185100662344646391325033709)
          ·
            refine ⟨69412748379242396746887641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185100662344646391325033709 69412748379242396746887641)
            ·
              refine ⟨52059561284431797560165731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69412748379242396746887641 52059561284431797560165731)
              ·
                refine ⟨78089341926647696340248597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52059561284431797560165731 78089341926647696340248597)
                ·
                  refine ⟨3660437902811610765949153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78089341926647696340248597 3660437902811610765949153)
                  ·
                    refine ⟨2745328427108708074461865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3660437902811610765949153 2745328427108708074461865)
                    ·
                      refine ⟨2058996320331531055846399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745328427108708074461865 2058996320331531055846399)
                      ·
                        rfl

theorem cell23_4009881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_4009881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009881 prefixEnd_4009881 := by exact prefixLift 4009881
  have htrace : WordTrace (prefixWord ++ tailWord_4009881) baseStart_4009881 baseEnd_4009881 := by
    simpa [prefixWord, tailWord_4009881, baseEnd_4009881] using wordTrace_append hprefix tailTrace_4009881
  have hstable : (prefixWord ++ tailWord_4009881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009881).length < 2 ^ (prefixWord ++ tailWord_4009881).sum := by decide
  have hdescent : baseEnd_4009881 < baseStart_4009881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009885 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_4009885 : Nat := 118140960795 + 4009885 * 2 ^ 59
def prefixEnd_4009885 : Nat := 4983230072969 + 3 ^ 40 * 4009885 * 2
def baseEnd_4009885 : Nat := 2058998374254149040196381

theorem tailTrace_4009885 : CollatzResearch.WordTrace tailWord_4009885 prefixEnd_4009885 2058998374254149040196381 := by
  unfold tailWord_4009885
  simp only [CollatzResearch.WordTrace]
  refine ⟨146252521077878953680703109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97501680718585969120468739 146252521077878953680703109)
  ·
    refine ⟨27422347702102303815131833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146252521077878953680703109 27422347702102303815131833)
    ·
      refine ⟨20566760776576727861348875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27422347702102303815131833 20566760776576727861348875)
      ·
        refine ⟨30850141164865091792023313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20566760776576727861348875 30850141164865091792023313)
        ·
          refine ⟨23137605873648818844017485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30850141164865091792023313 23137605873648818844017485)
          ·
            refine ⟨8676602202618307066506557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23137605873648818844017485 8676602202618307066506557)
            ·
              refine ⟨3253725825981865149939959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8676602202618307066506557 3253725825981865149939959)
              ·
                refine ⟨4880588738972797724909939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3253725825981865149939959 4880588738972797724909939)
                ·
                  refine ⟨7320883108459196587364909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880588738972797724909939 7320883108459196587364909)
                  ·
                    refine ⟨2745331165672198720261841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7320883108459196587364909 2745331165672198720261841)
                    ·
                      refine ⟨2058998374254149040196381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745331165672198720261841 2058998374254149040196381)
                      ·
                        rfl

theorem cell23_4009885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_4009885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009885 prefixEnd_4009885 := by exact prefixLift 4009885
  have htrace : WordTrace (prefixWord ++ tailWord_4009885) baseStart_4009885 baseEnd_4009885 := by
    simpa [prefixWord, tailWord_4009885, baseEnd_4009885] using wordTrace_append hprefix tailTrace_4009885
  have hstable : (prefixWord ++ tailWord_4009885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009885).length < 2 ^ (prefixWord ++ tailWord_4009885).sum := by decide
  have hdescent : baseEnd_4009885 < baseStart_4009885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009908 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_4009908 : Nat := 118140960795 + 4009908 * 2 ^ 59
def prefixEnd_4009908 : Nat := 4983230072969 + 3 ^ 40 * 4009908 * 2
def baseEnd_4009908 : Nat := 686336728103067483402925

theorem tailTrace_4009908 : CollatzResearch.WordTrace tailWord_4009908 prefixEnd_4009908 686336728103067483402925 := by
  unfold tailWord_4009908
  simp only [CollatzResearch.WordTrace]
  refine ⟨73126679978397814304395189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97502239971197085739193585 73126679978397814304395189)
  ·
    refine ⟨6855626247974795091037049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73126679978397814304395189 6855626247974795091037049)
    ·
      refine ⟨5141719685981096318277787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6855626247974795091037049 5141719685981096318277787)
      ·
        refine ⟨7712579528971644477416681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141719685981096318277787 7712579528971644477416681)
        ·
          refine ⟨5784434646728733358062511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7712579528971644477416681 5784434646728733358062511)
          ·
            refine ⟨8676651970093100037093767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5784434646728733358062511 8676651970093100037093767)
            ·
              refine ⟨13014977955139650055640651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8676651970093100037093767 13014977955139650055640651)
              ·
                refine ⟨19522466932709475083460977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13014977955139650055640651 19522466932709475083460977)
                ·
                  refine ⟨14641850199532106312595733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19522466932709475083460977 14641850199532106312595733)
                  ·
                    refine ⟨686336728103067483402925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14641850199532106312595733 686336728103067483402925)
                    ·
                      rfl

theorem cell23_4009908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_4009908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009908 prefixEnd_4009908 := by exact prefixLift 4009908
  have htrace : WordTrace (prefixWord ++ tailWord_4009908) baseStart_4009908 baseEnd_4009908 := by
    simpa [prefixWord, tailWord_4009908, baseEnd_4009908] using wordTrace_append hprefix tailTrace_4009908
  have hstable : (prefixWord ++ tailWord_4009908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009908).length < 2 ^ (prefixWord ++ tailWord_4009908).sum := by decide
  have hdescent : baseEnd_4009908 < baseStart_4009908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009934 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_4009934 : Nat := 118140960795 + 4009934 * 2 ^ 59
def prefixEnd_4009934 : Nat := 4983230072969 + 3 ^ 40 * 4009934 * 2
def baseEnd_4009934 : Nat := 686341178268739782827885

theorem tailTrace_4009934 : CollatzResearch.WordTrace tailWord_4009934 prefixEnd_4009934 686341178268739782827885 := by
  unfold tailWord_4009934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18281788531837679381154607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97502872169800956699491237 18281788531837679381154607)
  ·
    refine ⟨27422682797756519071731911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18281788531837679381154607 27422682797756519071731911)
    ·
      refine ⟨41134024196634778607597867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27422682797756519071731911 41134024196634778607597867)
      ·
        refine ⟨61701036294952167911396801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41134024196634778607597867 61701036294952167911396801)
        ·
          refine ⟨46275777221214125933547601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61701036294952167911396801 46275777221214125933547601)
          ·
            refine ⟨34706832915910594450160701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46275777221214125933547601 34706832915910594450160701)
            ·
              refine ⟨13015062343466472918810263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34706832915910594450160701 13015062343466472918810263)
              ·
                refine ⟨19522593515199709378215395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13015062343466472918810263 19522593515199709378215395)
                ·
                  refine ⟨29283890272799564067323093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19522593515199709378215395 29283890272799564067323093)
                  ·
                    refine ⟨686341178268739782827885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29283890272799564067323093 686341178268739782827885)
                    ·
                      rfl

theorem cell23_4009934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_4009934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009934 prefixEnd_4009934 := by exact prefixLift 4009934
  have htrace : WordTrace (prefixWord ++ tailWord_4009934) baseStart_4009934 baseEnd_4009934 := by
    simpa [prefixWord, tailWord_4009934, baseEnd_4009934] using wordTrace_append hprefix tailTrace_4009934
  have hstable : (prefixWord ++ tailWord_4009934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009934).length < 2 ^ (prefixWord ++ tailWord_4009934).sum := by decide
  have hdescent : baseEnd_4009934 < baseStart_4009934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009949 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_4009949 : Nat := 118140960795 + 4009949 * 2 ^ 59
def prefixEnd_4009949 : Nat := 4983230072969 + 3 ^ 40 * 4009949 * 2
def baseEnd_4009949 : Nat := 2059031237016036789796087

theorem tailTrace_4009949 : CollatzResearch.WordTrace tailWord_4009949 prefixEnd_4009949 2059031237016036789796087 := by
  unfold tailWord_4009949
  simp only [CollatzResearch.WordTrace]
  refine ⟨146254855349647092611032901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97503236899764728407355267 146254855349647092611032901)
  ·
    refine ⟨27422785378058829864568669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146254855349647092611032901 27422785378058829864568669)
    ·
      refine ⟨10283544516772061199213251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27422785378058829864568669 10283544516772061199213251)
      ·
        refine ⟨15425316775158091798819877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10283544516772061199213251 15425316775158091798819877)
        ·
          refine ⟨2892246895342142212278727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15425316775158091798819877 2892246895342142212278727)
          ·
            refine ⟨4338370343013213318418091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892246895342142212278727 4338370343013213318418091)
            ·
              refine ⟨6507555514519819977627137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338370343013213318418091 6507555514519819977627137)
              ·
                refine ⟨4880666635889864983220353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6507555514519819977627137 4880666635889864983220353)
                ·
                  refine ⟨3660499976917398737415265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4880666635889864983220353 3660499976917398737415265)
                  ·
                    refine ⟨2745374982688049053061449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3660499976917398737415265 2745374982688049053061449)
                    ·
                      refine ⟨2059031237016036789796087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745374982688049053061449 2059031237016036789796087)
                      ·
                        rfl

theorem cell23_4009949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_4009949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009949 prefixEnd_4009949 := by exact prefixLift 4009949
  have htrace : WordTrace (prefixWord ++ tailWord_4009949) baseStart_4009949 baseEnd_4009949 := by
    simpa [prefixWord, tailWord_4009949, baseEnd_4009949] using wordTrace_append hprefix tailTrace_4009949
  have hstable : (prefixWord ++ tailWord_4009949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009949).length < 2 ^ (prefixWord ++ tailWord_4009949).sum := by decide
  have hdescent : baseEnd_4009949 < baseStart_4009949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009981 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_4009981 : Nat := 118140960795 + 4009981 * 2 ^ 59
def prefixEnd_4009981 : Nat := 4983230072969 + 3 ^ 40 * 4009981 * 2
def baseEnd_4009981 : Nat := 686349222798993554865313

theorem tailTrace_4009981 : CollatzResearch.WordTrace tailWord_4009981 prefixEnd_4009981 686349222798993554865313 := by
  unfold tailWord_4009981
  simp only [CollatzResearch.WordTrace]
  refine ⟨146256022485531162076197797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97504014990354108050798531 146256022485531162076197797)
  ·
    refine ⟨27423004216037092889287087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146256022485531162076197797 27423004216037092889287087)
    ·
      refine ⟨41134506324055639333930631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27423004216037092889287087 41134506324055639333930631)
      ·
        refine ⟨61701759486083459000895947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41134506324055639333930631 61701759486083459000895947)
        ·
          refine ⟨92552639229125188501343921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61701759486083459000895947 92552639229125188501343921)
          ·
            refine ⟨69414479421843891376007941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92552639229125188501343921 69414479421843891376007941)
            ·
              refine ⟨13015214891595729633001489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69414479421843891376007941 13015214891595729633001489)
              ·
                refine ⟨9761411168696797224751117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13015214891595729633001489 9761411168696797224751117)
                ·
                  refine ⟨3660529188261298959281669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9761411168696797224751117 3660529188261298959281669)
                  ·
                    refine ⟨686349222798993554865313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660529188261298959281669 686349222798993554865313)
                    ·
                      rfl

theorem cell23_4009981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_4009981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009981 prefixEnd_4009981 := by exact prefixLift 4009981
  have htrace : WordTrace (prefixWord ++ tailWord_4009981) baseStart_4009981 baseEnd_4009981 := by
    simpa [prefixWord, tailWord_4009981, baseEnd_4009981] using wordTrace_append hprefix tailTrace_4009981
  have hstable : (prefixWord ++ tailWord_4009981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009981).length < 2 ^ (prefixWord ++ tailWord_4009981).sum := by decide
  have hdescent : baseEnd_4009981 < baseStart_4009981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4009991 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_4009991 : Nat := 118140960795 + 4009991 * 2 ^ 59
def prefixEnd_4009991 : Nat := 4983230072969 + 3 ^ 40 * 4009991 * 2
def baseEnd_4009991 : Nat := 2059052803203525625470893

theorem tailTrace_4009991 : CollatzResearch.WordTrace tailWord_4009991 prefixEnd_4009991 2059052803203525625470893 := by
  unfold tailWord_4009991
  simp only [CollatzResearch.WordTrace]
  refine ⟨146256387215494933784061827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97504258143663289189374551 146256387215494933784061827)
  ·
    refine ⟨219384580823242400676092741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146256387215494933784061827 219384580823242400676092741)
    ·
      refine ⟨41134608904357950126767389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219384580823242400676092741 41134608904357950126767389)
      ·
        refine ⟨15425478339134231297537771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41134608904357950126767389 15425478339134231297537771)
        ·
          refine ⟨23138217508701346946306657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15425478339134231297537771 23138217508701346946306657)
          ·
            refine ⟨17353663131526010209729993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23138217508701346946306657 17353663131526010209729993)
            ·
              refine ⟨13015247348644507657297495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17353663131526010209729993 13015247348644507657297495)
              ·
                refine ⟨19522871022966761485946243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13015247348644507657297495 19522871022966761485946243)
                ·
                  refine ⟨29284306534450142228919365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19522871022966761485946243 29284306534450142228919365)
                  ·
                    refine ⟨5490807475209401667922381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29284306534450142228919365 5490807475209401667922381)
                    ·
                      refine ⟨2059052803203525625470893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490807475209401667922381 2059052803203525625470893)
                      ·
                        rfl

theorem cell23_4009991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_4009991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4009991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4009991 prefixEnd_4009991 := by exact prefixLift 4009991
  have htrace : WordTrace (prefixWord ++ tailWord_4009991) baseStart_4009991 baseEnd_4009991 := by
    simpa [prefixWord, tailWord_4009991, baseEnd_4009991] using wordTrace_append hprefix tailTrace_4009991
  have hstable : (prefixWord ++ tailWord_4009991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4009991).length < 2 ^ (prefixWord ++ tailWord_4009991).sum := by decide
  have hdescent : baseEnd_4009991 < baseStart_4009991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4009991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010015 : List Nat := [1, 1, 2, 4, 1, 2, 5, 2, 1, 4]
def baseStart_4010015 : Nat := 118140960795 + 4010015 * 2 ^ 59
def prefixEnd_4010015 : Nat := 4983230072969 + 3 ^ 40 * 4010015 * 2
def baseEnd_4010015 : Nat := 686355042246411177190261

theorem tailTrace_4010015 : CollatzResearch.WordTrace tailWord_4010015 prefixEnd_4010015 686355042246411177190261 := by
  unfold tailWord_4010015
  simp only [CollatzResearch.WordTrace]
  refine ⟨146257262567407985882935499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97504841711605323921956999 146257262567407985882935499)
  ·
    refine ⟨219385893851111978824403249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146257262567407985882935499 219385893851111978824403249)
    ·
      refine ⟨164539420388333984118302437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219385893851111978824403249 164539420388333984118302437)
      ·
        refine ⟨30851141322812622022181707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164539420388333984118302437 30851141322812622022181707)
        ·
          refine ⟨46276711984218933033272561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30851141322812622022181707 46276711984218933033272561)
          ·
            refine ⟨34707533988164199774954421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46276711984218933033272561 34707533988164199774954421)
            ·
              refine ⟨3253831311390393728901977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34707533988164199774954421 3253831311390393728901977)
              ·
                refine ⟨2440373483542795296676483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3253831311390393728901977 2440373483542795296676483)
                ·
                  refine ⟨3660560225314192945014725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440373483542795296676483 3660560225314192945014725)
                  ·
                    refine ⟨686355042246411177190261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660560225314192945014725 686355042246411177190261)
                    ·
                      rfl

theorem cell23_4010015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 4].length) (baseStart_4010015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010015 prefixEnd_4010015 := by exact prefixLift 4010015
  have htrace : WordTrace (prefixWord ++ tailWord_4010015) baseStart_4010015 baseEnd_4010015 := by
    simpa [prefixWord, tailWord_4010015, baseEnd_4010015] using wordTrace_append hprefix tailTrace_4010015
  have hstable : (prefixWord ++ tailWord_4010015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010015).length < 2 ^ (prefixWord ++ tailWord_4010015).sum := by decide
  have hdescent : baseEnd_4010015 < baseStart_4010015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010031 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 1, 5, 2]
def baseStart_4010031 : Nat := 118140960795 + 4010031 * 2 ^ 59
def prefixEnd_4010031 : Nat := 4983230072969 + 3 ^ 40 * 4010031 * 2
def baseEnd_4010031 : Nat := 2059073342429705468970709

theorem tailTrace_4010031 : CollatzResearch.WordTrace tailWord_4010031 prefixEnd_4010031 2059073342429705468970709 := by
  unfold tailWord_4010031
  simp only [CollatzResearch.WordTrace]
  refine ⟨146257846135350020615517947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97505230756900013743678631 146257846135350020615517947)
  ·
    refine ⟨219386769203025030923276921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146257846135350020615517947 219386769203025030923276921)
    ·
      refine ⟨164540076902268773192457691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219386769203025030923276921 164540076902268773192457691)
      ·
        refine ⟨246810115353403159788686537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164540076902268773192457691 246810115353403159788686537)
        ·
          refine ⟨185107586515052369841514903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246810115353403159788686537 185107586515052369841514903)
          ·
            refine ⟨277661379772578554762272355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185107586515052369841514903 277661379772578554762272355)
            ·
              refine ⟨416492069658867832143408533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277661379772578554762272355 416492069658867832143408533)
              ·
                refine ⟨19523065765259429631722275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 416492069658867832143408533 19523065765259429631722275)
                ·
                  refine ⟨29284598647889144447583413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19523065765259429631722275 29284598647889144447583413)
                  ·
                    refine ⟨2745431123239607291960945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29284598647889144447583413 2745431123239607291960945)
                    ·
                      refine ⟨2059073342429705468970709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745431123239607291960945 2059073342429705468970709)
                      ·
                        rfl

theorem cell23_4010031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 5, 2].length) (baseStart_4010031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010031 prefixEnd_4010031 := by exact prefixLift 4010031
  have htrace : WordTrace (prefixWord ++ tailWord_4010031) baseStart_4010031 baseEnd_4010031 := by
    simpa [prefixWord, tailWord_4010031, baseEnd_4010031] using wordTrace_append hprefix tailTrace_4010031
  have hstable : (prefixWord ++ tailWord_4010031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010031).length < 2 ^ (prefixWord ++ tailWord_4010031).sum := by decide
  have hdescent : baseEnd_4010031 < baseStart_4010031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010048 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 2, 3, 2]
def baseStart_4010048 : Nat := 118140960795 + 4010048 * 2 ^ 59
def prefixEnd_4010048 : Nat := 4983230072969 + 3 ^ 40 * 4010048 * 2
def baseEnd_4010048 : Nat := 2059082071600831902458131

theorem tailTrace_4010048 : CollatzResearch.WordTrace tailWord_4010048 prefixEnd_4010048 2059082071600831902458131 := by
  unfold tailWord_4010048
  simp only [CollatzResearch.WordTrace]
  refine ⟨73129233088144216259443399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97505644117525621679257865 73129233088144216259443399)
  ·
    refine ⟨109693849632216324389165099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73129233088144216259443399 109693849632216324389165099)
    ·
      refine ⟨164540774448324486583747649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109693849632216324389165099 164540774448324486583747649)
      ·
        refine ⟨123405580836243364937810737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164540774448324486583747649 123405580836243364937810737)
        ·
          refine ⟨92554185627182523703358053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123405580836243364937810737 92554185627182523703358053)
          ·
            refine ⟨17353909805096723194379635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92554185627182523703358053 17353909805096723194379635)
            ·
              refine ⟨26030864707645084791569453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17353909805096723194379635 26030864707645084791569453)
              ·
                refine ⟨9761574265366906796838545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26030864707645084791569453 9761574265366906796838545)
                ·
                  refine ⟨7321180699025180097628909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9761574265366906796838545 7321180699025180097628909)
                  ·
                    refine ⟨2745442762134442536610841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7321180699025180097628909 2745442762134442536610841)
                    ·
                      refine ⟨2059082071600831902458131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745442762134442536610841 2059082071600831902458131)
                      ·
                        rfl

theorem cell23_4010048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_4010048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010048 prefixEnd_4010048 := by exact prefixLift 4010048
  have htrace : WordTrace (prefixWord ++ tailWord_4010048) baseStart_4010048 baseEnd_4010048 := by
    simpa [prefixWord, tailWord_4010048, baseEnd_4010048] using wordTrace_append hprefix tailTrace_4010048
  have hstable : (prefixWord ++ tailWord_4010048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010048).length < 2 ^ (prefixWord ++ tailWord_4010048).sum := by decide
  have hdescent : baseEnd_4010048 < baseStart_4010048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010055 : List Nat := [1, 1, 4, 1, 3, 1, 2, 5, 1, 1, 3]
def baseStart_4010055 : Nat := 118140960795 + 4010055 * 2 ^ 59
def prefixEnd_4010055 : Nat := 4983230072969 + 3 ^ 40 * 4010055 * 2
def baseEnd_4010055 : Nat := 2059085665965413375070599

theorem tailTrace_4010055 : CollatzResearch.WordTrace tailWord_4010055 prefixEnd_4010055 2059085665965413375070599 := by
  unfold tailWord_4010055
  simp only [CollatzResearch.WordTrace]
  refine ⟨146258721487263072714391619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97505814324842048476261079 146258721487263072714391619)
  ·
    refine ⟨219388082230894609071587429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146258721487263072714391619 219388082230894609071587429)
    ·
      refine ⟨41135265418292739200922643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219388082230894609071587429 41135265418292739200922643)
      ·
        refine ⟨61702898127439108801383965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41135265418292739200922643 61702898127439108801383965)
        ·
          refine ⟨23138586797789665800518987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61702898127439108801383965 23138586797789665800518987)
          ·
            refine ⟨34707880196684498700778481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23138586797789665800518987 34707880196684498700778481)
            ·
              refine ⟨26030910147513374025583861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34707880196684498700778481 26030910147513374025583861)
              ·
                refine ⟨2440397826329378814898487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26030910147513374025583861 2440397826329378814898487)
                ·
                  refine ⟨3660596739494068222347731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440397826329378814898487 3660596739494068222347731)
                  ·
                    refine ⟨5490895109241102333521597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3660596739494068222347731 5490895109241102333521597)
                    ·
                      refine ⟨2059085665965413375070599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490895109241102333521597 2059085665965413375070599)
                      ·
                        rfl

theorem cell23_4010055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_4010055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010055 prefixEnd_4010055 := by exact prefixLift 4010055
  have htrace : WordTrace (prefixWord ++ tailWord_4010055) baseStart_4010055 baseEnd_4010055 := by
    simpa [prefixWord, tailWord_4010055, baseEnd_4010055] using wordTrace_append hprefix tailTrace_4010055
  have hstable : (prefixWord ++ tailWord_4010055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010055).length < 2 ^ (prefixWord ++ tailWord_4010055).sum := by decide
  have hdescent : baseEnd_4010055 < baseStart_4010055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010071 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 4, 4]
def baseStart_4010071 : Nat := 118140960795 + 4010071 * 2 ^ 59
def prefixEnd_4010071 : Nat := 4983230072969 + 3 ^ 40 * 4010071 * 2
def baseEnd_4010071 : Nat := 686364627218628437490175

theorem tailTrace_4010071 : CollatzResearch.WordTrace tailWord_4010071 prefixEnd_4010071 686364627218628437490175 := by
  unfold tailWord_4010071
  simp only [CollatzResearch.WordTrace]
  refine ⟨146259305055205107446974067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97506203370136738297982711 146259305055205107446974067)
  ·
    refine ⟨219388957582807661170461101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146259305055205107446974067 219388957582807661170461101)
    ·
      refine ⟨82270859093552872938922913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219388957582807661170461101 82270859093552872938922913)
      ·
        refine ⟨61703144320164654704192185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82270859093552872938922913 61703144320164654704192185)
        ·
          refine ⟨46277358240123491028144139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61703144320164654704192185 46277358240123491028144139)
          ·
            refine ⟨69416037360185236542216209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46277358240123491028144139 69416037360185236542216209)
            ·
              refine ⟨52062028020138927406662157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69416037360185236542216209 52062028020138927406662157)
              ·
                refine ⟨19523260507552097777498309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52062028020138927406662157 19523260507552097777498309)
                ·
                  refine ⟨3660611345166018333280933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19523260507552097777498309 3660611345166018333280933)
                  ·
                    refine ⟨686364627218628437490175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660611345166018333280933 686364627218628437490175)
                    ·
                      rfl

theorem cell23_4010071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_4010071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010071 prefixEnd_4010071 := by exact prefixLift 4010071
  have htrace : WordTrace (prefixWord ++ tailWord_4010071) baseStart_4010071 baseEnd_4010071 := by
    simpa [prefixWord, tailWord_4010071, baseEnd_4010071] using wordTrace_append hprefix tailTrace_4010071
  have hstable : (prefixWord ++ tailWord_4010071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010071).length < 2 ^ (prefixWord ++ tailWord_4010071).sum := by decide
  have hdescent : baseEnd_4010071 < baseStart_4010071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010072 : List Nat := [2, 1, 2, 2, 1, 4, 4, 2, 1, 1, 3]
def baseStart_4010072 : Nat := 118140960795 + 4010072 * 2 ^ 59
def prefixEnd_4010072 : Nat := 4983230072969 + 3 ^ 40 * 4010072 * 2
def baseEnd_4010072 : Nat := 2059094395136539808558021

theorem tailTrace_4010072 : CollatzResearch.WordTrace tailWord_4010072 prefixEnd_4010072 2059094395136539808558021 := by
  unfold tailWord_4010072
  simp only [CollatzResearch.WordTrace]
  refine ⟨73129670764100742308880235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97506227685467656411840313 73129670764100742308880235)
  ·
    refine ⟨109694506146151113463320353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73129670764100742308880235 109694506146151113463320353)
    ·
      refine ⟨82270879609613335097490265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109694506146151113463320353 82270879609613335097490265)
      ·
        refine ⟨61703159707210001323117699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82270879609613335097490265 61703159707210001323117699)
        ·
          refine ⟨92554739560815001984676549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61703159707210001323117699 92554739560815001984676549)
          ·
            refine ⟨17354013667652812872126853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92554739560815001984676549 17354013667652812872126853)
            ·
              refine ⟨3253877562684902413523785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17354013667652812872126853 3253877562684902413523785)
              ·
                refine ⟨2440408172013676810142839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3253877562684902413523785 2440408172013676810142839)
                ·
                  refine ⟨3660612258020515215214259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440408172013676810142839 3660612258020515215214259)
                  ·
                    refine ⟨5490918387030772822821389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3660612258020515215214259 5490918387030772822821389)
                    ·
                      refine ⟨2059094395136539808558021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490918387030772822821389 2059094395136539808558021)
                      ·
                        rfl

theorem cell23_4010072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_4010072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010072 prefixEnd_4010072 := by exact prefixLift 4010072
  have htrace : WordTrace (prefixWord ++ tailWord_4010072) baseStart_4010072 baseEnd_4010072 := by
    simpa [prefixWord, tailWord_4010072, baseEnd_4010072] using wordTrace_append hprefix tailTrace_4010072
  have hstable : (prefixWord ++ tailWord_4010072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010072).length < 2 ^ (prefixWord ++ tailWord_4010072).sum := by decide
  have hdescent : baseEnd_4010072 < baseStart_4010072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010095 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 3, 2, 2]
def baseStart_4010095 : Nat := 118140960795 + 4010095 * 2 ^ 59
def prefixEnd_4010095 : Nat := 4983230072969 + 3 ^ 40 * 4010095 * 2
def baseEnd_4010095 : Nat := 2059106205191593218570415

theorem tailTrace_4010095 : CollatzResearch.WordTrace tailWord_4010095 prefixEnd_4010095 2059106205191593218570415 := by
  unfold tailWord_4010095
  simp only [CollatzResearch.WordTrace]
  refine ⟨146260180407118159545847739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97506786938078773030565159 146260180407118159545847739)
  ·
    refine ⟨219390270610677239318771609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146260180407118159545847739 219390270610677239318771609)
    ·
      refine ⟨164542702958007929489078707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219390270610677239318771609 164542702958007929489078707)
      ·
        refine ⟨246814054437011894233618061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164542702958007929489078707 246814054437011894233618061)
        ·
          refine ⟨92555270413879460337606773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246814054437011894233618061 92555270413879460337606773)
          ·
            refine ⟨8677056601301199406650635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92555270413879460337606773 8677056601301199406650635)
            ·
              refine ⟨13015584901951799109975953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677056601301199406650635 13015584901951799109975953)
              ·
                refine ⟨9761688676463849332481965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13015584901951799109975953 9761688676463849332481965)
                ·
                  refine ⟨3660633253673943499680737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9761688676463849332481965 3660633253673943499680737)
                  ·
                    refine ⟨2745474940255457624760553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3660633253673943499680737 2745474940255457624760553)
                    ·
                      refine ⟨2059106205191593218570415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745474940255457624760553 2059106205191593218570415)
                      ·
                        rfl

theorem cell23_4010095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 2, 2].length) (baseStart_4010095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010095 prefixEnd_4010095 := by exact prefixLift 4010095
  have htrace : WordTrace (prefixWord ++ tailWord_4010095) baseStart_4010095 baseEnd_4010095 := by
    simpa [prefixWord, tailWord_4010095, baseEnd_4010095] using wordTrace_append hprefix tailTrace_4010095
  have hstable : (prefixWord ++ tailWord_4010095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010095).length < 2 ^ (prefixWord ++ tailWord_4010095).sum := by decide
  have hdescent : baseEnd_4010095 < baseStart_4010095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010098 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_4010098 : Nat := 118140960795 + 4010098 * 2 ^ 59
def prefixEnd_4010098 : Nat := 4983230072969 + 3 ^ 40 * 4010098 * 2
def baseEnd_4010098 : Nat := 2059107745633556706832901

theorem tailTrace_4010098 : CollatzResearch.WordTrace tailWord_4010098 prefixEnd_4010098 2059107745633556706832901 := by
  unfold tailWord_4010098
  simp only [CollatzResearch.WordTrace]
  refine ⟨36565072456526822764551737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97506859884071527372137965 36565072456526822764551737)
  ·
    refine ⟨27423804342395117073413803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36565072456526822764551737 27423804342395117073413803)
    ·
      refine ⟨41135706513592675610120705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27423804342395117073413803 41135706513592675610120705)
      ·
        refine ⟨30851779885194506707590529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41135706513592675610120705 30851779885194506707590529)
        ·
          refine ⟨23138834913895880030692897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30851779885194506707590529 23138834913895880030692897)
          ·
            refine ⟨17354126185421910023019673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23138834913895880030692897 17354126185421910023019673)
            ·
              refine ⟨13015594639066432517264755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17354126185421910023019673 13015594639066432517264755)
              ·
                refine ⟨19523391958599648775897133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13015594639066432517264755 19523391958599648775897133)
                ·
                  refine ⟨7321271984474868290961425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19523391958599648775897133 7321271984474868290961425)
                  ·
                    refine ⟨5490953988356151218221069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7321271984474868290961425 5490953988356151218221069)
                    ·
                      refine ⟨2059107745633556706832901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490953988356151218221069 2059107745633556706832901)
                      ·
                        rfl

theorem cell23_4010098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_4010098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010098 prefixEnd_4010098 := by exact prefixLift 4010098
  have htrace : WordTrace (prefixWord ++ tailWord_4010098) baseStart_4010098 baseEnd_4010098 := by
    simpa [prefixWord, tailWord_4010098, baseEnd_4010098] using wordTrace_append hprefix tailTrace_4010098
  have hstable : (prefixWord ++ tailWord_4010098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010098).length < 2 ^ (prefixWord ++ tailWord_4010098).sum := by decide
  have hdescent : baseEnd_4010098 < baseStart_4010098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010115 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 1, 2, 3]
def baseStart_4010115 : Nat := 118140960795 + 4010115 * 2 ^ 59
def prefixEnd_4010115 : Nat := 4983230072969 + 3 ^ 40 * 4010115 * 2
def baseEnd_4010115 : Nat := 2059116474804683140320323

theorem tailTrace_4010115 : CollatzResearch.WordTrace tailWord_4010115 prefixEnd_4010115 2059116474804683140320323 := by
  unfold tailWord_4010115
  simp only [CollatzResearch.WordTrace]
  refine ⟨146260909867045702961575799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97507273244697135307717199 146260909867045702961575799)
  ·
    refine ⟨219391364800568554442363699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146260909867045702961575799 219391364800568554442363699)
    ·
      refine ⟨329087047200852831663545549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219391364800568554442363699 329087047200852831663545549)
      ·
        refine ⟨123407642700319811873829581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329087047200852831663545549 123407642700319811873829581)
        ·
          refine ⟨46277866012619929452686093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123407642700319811873829581 46277866012619929452686093)
          ·
            refine ⟨17354199754732473544757285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46277866012619929452686093 17354199754732473544757285)
            ·
              refine ⟨3253912454012338789641991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17354199754732473544757285 3253912454012338789641991)
              ·
                refine ⟨4880868681018508184462987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3253912454012338789641991 4880868681018508184462987)
                ·
                  refine ⟨7321303021527762276694481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880868681018508184462987 7321303021527762276694481)
                  ·
                    refine ⟨5490977266145821707520861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7321303021527762276694481 5490977266145821707520861)
                    ·
                      refine ⟨2059116474804683140320323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490977266145821707520861 2059116474804683140320323)
                      ·
                        rfl

theorem cell23_4010115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_4010115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010115 prefixEnd_4010115 := by exact prefixLift 4010115
  have htrace : WordTrace (prefixWord ++ tailWord_4010115) baseStart_4010115 baseEnd_4010115 := by
    simpa [prefixWord, tailWord_4010115, baseEnd_4010115] using wordTrace_append hprefix tailTrace_4010115
  have hstable : (prefixWord ++ tailWord_4010115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010115).length < 2 ^ (prefixWord ++ tailWord_4010115).sum := by decide
  have hdescent : baseEnd_4010115 < baseStart_4010115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010128 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 4, 1, 3]
def baseStart_4010128 : Nat := 118140960795 + 4010128 * 2 ^ 59
def prefixEnd_4010128 : Nat := 4983230072969 + 3 ^ 40 * 4010128 * 2
def baseEnd_4010128 : Nat := 2059123150053191589457763

theorem tailTrace_4010128 : CollatzResearch.WordTrace tailWord_4010128 prefixEnd_4010128 2059123150053191589457763 := by
  unfold tailWord_4010128
  simp only [CollatzResearch.WordTrace]
  refine ⟨73130692007999303090899519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97507589343999070787866025 73130692007999303090899519)
  ·
    refine ⟨109696038011998954636349279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73130692007999303090899519 109696038011998954636349279)
    ·
      refine ⟨164544057017998431954523919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109696038011998954636349279 164544057017998431954523919)
      ·
        refine ⟨246816085526997647931785879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164544057017998431954523919 246816085526997647931785879)
        ·
          refine ⟨370224128290496471897678819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246816085526997647931785879 370224128290496471897678819)
          ·
            refine ⟨555336192435744707846518229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370224128290496471897678819 555336192435744707846518229)
            ·
              refine ⟨13015692010212766590152771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 555336192435744707846518229 13015692010212766590152771)
              ·
                refine ⟨19523538015319149885229157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13015692010212766590152771 19523538015319149885229157)
                ·
                  refine ⟨3660663377872340603480467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19523538015319149885229157 3660663377872340603480467)
                  ·
                    refine ⟨5490995066808510905220701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3660663377872340603480467 5490995066808510905220701)
                    ·
                      refine ⟨2059123150053191589457763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5490995066808510905220701 2059123150053191589457763)
                      ·
                        rfl

theorem cell23_4010128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 1, 3].length) (baseStart_4010128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010128 prefixEnd_4010128 := by exact prefixLift 4010128
  have htrace : WordTrace (prefixWord ++ tailWord_4010128) baseStart_4010128 baseEnd_4010128 := by
    simpa [prefixWord, tailWord_4010128, baseEnd_4010128] using wordTrace_append hprefix tailTrace_4010128
  have hstable : (prefixWord ++ tailWord_4010128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010128).length < 2 ^ (prefixWord ++ tailWord_4010128).sum := by decide
  have hdescent : baseEnd_4010128 < baseStart_4010128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010142 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_4010142 : Nat := 118140960795 + 4010142 * 2 ^ 59
def prefixEnd_4010142 : Nat := 4983230072969 + 3 ^ 40 * 4010142 * 2
def baseEnd_4010142 : Nat := 2059130338782354534682699

theorem tailTrace_4010142 : CollatzResearch.WordTrace tailWord_4010142 prefixEnd_4010142 2059130338782354534682699 := by
  unfold tailWord_4010142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18282736829743485821601085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97507929758631924381872453 18282736829743485821601085)
  ·
    refine ⟨6856026311153807183100407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18282736829743485821601085 6856026311153807183100407)
    ·
      refine ⟨10284039466730710774650611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856026311153807183100407 10284039466730710774650611)
      ·
        refine ⟨15426059200096066161975917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10284039466730710774650611 15426059200096066161975917)
        ·
          refine ⟨5784772200036024810740969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15426059200096066161975917 5784772200036024810740969)
          ·
            refine ⟨4338579150027018608055727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5784772200036024810740969 4338579150027018608055727)
            ·
              refine ⟨6507868725040527912083591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338579150027018608055727 6507868725040527912083591)
              ·
                refine ⟨9761803087560791868125387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507868725040527912083591 9761803087560791868125387)
                ·
                  refine ⟨14642704631341187802188081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9761803087560791868125387 14642704631341187802188081)
                  ·
                    refine ⟨10982028473505890851641061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14642704631341187802188081 10982028473505890851641061)
                    ·
                      refine ⟨2059130338782354534682699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10982028473505890851641061 2059130338782354534682699)
                      ·
                        rfl

theorem cell23_4010142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_4010142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010142 prefixEnd_4010142 := by exact prefixLift 4010142
  have htrace : WordTrace (prefixWord ++ tailWord_4010142) baseStart_4010142 baseEnd_4010142 := by
    simpa [prefixWord, tailWord_4010142, baseEnd_4010142] using wordTrace_append hprefix tailTrace_4010142
  have hstable : (prefixWord ++ tailWord_4010142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010142).length < 2 ^ (prefixWord ++ tailWord_4010142).sum := by decide
  have hdescent : baseEnd_4010142 < baseStart_4010142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010145 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_4010145 : Nat := 118140960795 + 4010145 * 2 ^ 59
def prefixEnd_4010145 : Nat := 4983230072969 + 3 ^ 40 * 4010145 * 2
def baseEnd_4010145 : Nat := 2059131879224318022945185

theorem tailTrace_4010145 : CollatzResearch.WordTrace tailWord_4010145 prefixEnd_4010145 2059131879224318022945185 := by
  unfold tailWord_4010145
  simp only [CollatzResearch.WordTrace]
  refine ⟨146262004056937018085167889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97508002704624678723445259 146262004056937018085167889)
  ·
    refine ⟨109696503042702763563875917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146262004056937018085167889 109696503042702763563875917)
    ·
      refine ⟨41136188641013536336453469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109696503042702763563875917 41136188641013536336453469)
      ·
        refine ⟨15426070740380076126170051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41136188641013536336453469 15426070740380076126170051)
        ·
          refine ⟨23139106110570114189255077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15426070740380076126170051 23139106110570114189255077)
          ·
            refine ⟨4338582395731896410485327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23139106110570114189255077 4338582395731896410485327)
            ·
              refine ⟨6507873593597844615727991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338582395731896410485327 6507873593597844615727991)
              ·
                refine ⟨9761810390396766923591987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507873593597844615727991 9761810390396766923591987)
                ·
                  refine ⟨14642715585595150385387981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9761810390396766923591987 14642715585595150385387981)
                  ·
                    refine ⟨5491018344598181394520493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14642715585595150385387981 5491018344598181394520493)
                    ·
                      refine ⟨2059131879224318022945185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5491018344598181394520493 2059131879224318022945185)
                      ·
                        rfl

theorem cell23_4010145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_4010145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010145 prefixEnd_4010145 := by exact prefixLift 4010145
  have htrace : WordTrace (prefixWord ++ tailWord_4010145) baseStart_4010145 baseEnd_4010145 := by
    simpa [prefixWord, tailWord_4010145, baseEnd_4010145] using wordTrace_append hprefix tailTrace_4010145
  have hstable : (prefixWord ++ tailWord_4010145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010145).length < 2 ^ (prefixWord ++ tailWord_4010145).sum := by decide
  have hdescent : baseEnd_4010145 < baseStart_4010145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010168 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 3, 4, 2]
def baseStart_4010168 : Nat := 118140960795 + 4010168 * 2 ^ 59
def prefixEnd_4010168 : Nat := 4983230072969 + 3 ^ 40 * 4010168 * 2
def baseEnd_4010168 : Nat := 2059143689279371432957579

theorem tailTrace_4010168 : CollatzResearch.WordTrace tailWord_4010168 prefixEnd_4010168 2059143689279371432957579 := by
  unfold tailWord_4010168
  simp only [CollatzResearch.WordTrace]
  refine ⟨73131421467926846506627579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97508561957235795342170105 73131421467926846506627579)
  ·
    refine ⟨109697132201890269759941369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73131421467926846506627579 109697132201890269759941369)
    ·
      refine ⟨82272849151417702319956027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109697132201890269759941369 82272849151417702319956027)
      ·
        refine ⟨123409273727126553479934041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82272849151417702319956027 123409273727126553479934041)
        ·
          refine ⟨92556955295344915109950531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123409273727126553479934041 92556955295344915109950531)
          ·
            refine ⟨138835432943017372664925797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92556955295344915109950531 138835432943017372664925797)
            ·
              refine ⟨26031643676815757374673587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138835432943017372664925797 26031643676815757374673587)
              ·
                refine ⟨39047465515223636062010381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26031643676815757374673587 39047465515223636062010381)
                ·
                  refine ⟨14642799568208863523253893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39047465515223636062010381 14642799568208863523253893)
                  ·
                    refine ⟨2745524919039161910610105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14642799568208863523253893 2745524919039161910610105)
                    ·
                      refine ⟨2059143689279371432957579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745524919039161910610105 2059143689279371432957579)
                      ·
                        rfl

theorem cell23_4010168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_4010168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010168 prefixEnd_4010168 := by exact prefixLift 4010168
  have htrace : WordTrace (prefixWord ++ tailWord_4010168) baseStart_4010168 baseEnd_4010168 := by
    simpa [prefixWord, tailWord_4010168, baseEnd_4010168] using wordTrace_append hprefix tailTrace_4010168
  have hstable : (prefixWord ++ tailWord_4010168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010168).length < 2 ^ (prefixWord ++ tailWord_4010168).sum := by decide
  have hdescent : baseEnd_4010168 < baseStart_4010168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010171 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 5]
def baseStart_4010171 : Nat := 118140960795 + 4010171 * 2 ^ 59
def prefixEnd_4010171 : Nat := 4983230072969 + 3 ^ 40 * 4010171 * 2
def baseEnd_4010171 : Nat := 2059145229721334921220065

theorem tailTrace_4010171 : CollatzResearch.WordTrace tailWord_4010171 prefixEnd_4010171 2059145229721334921220065 := by
  unfold tailWord_4010171
  simp only [CollatzResearch.WordTrace]
  refine ⟨146262952354842824525614367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97508634903228549683742911 146262952354842824525614367)
  ·
    refine ⟨219394428532264236788421551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146262952354842824525614367 219394428532264236788421551)
    ·
      refine ⟨329091642798396355182632327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219394428532264236788421551 329091642798396355182632327)
      ·
        refine ⟨493637464197594532773948491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329091642798396355182632327 493637464197594532773948491)
        ·
          refine ⟨740456196296391799160922737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493637464197594532773948491 740456196296391799160922737)
          ·
            refine ⟨555342147222293849370692053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740456196296391799160922737 555342147222293849370692053)
            ·
              refine ⟨13015831575522512094625595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 555342147222293849370692053 13015831575522512094625595)
              ·
                refine ⟨19523747363283768141938393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13015831575522512094625595 19523747363283768141938393)
                ·
                  refine ⟨14642810522462826106453795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19523747363283768141938393 14642810522462826106453795)
                  ·
                    refine ⟨21964215783694239159680693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14642810522462826106453795 21964215783694239159680693)
                    ·
                      refine ⟨2059145229721334921220065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21964215783694239159680693 2059145229721334921220065)
                      ·
                        rfl

theorem cell23_4010171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 5].length) (baseStart_4010171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010171 prefixEnd_4010171 := by exact prefixLift 4010171
  have htrace : WordTrace (prefixWord ++ tailWord_4010171) baseStart_4010171 baseEnd_4010171 := by
    simpa [prefixWord, tailWord_4010171, baseEnd_4010171] using wordTrace_append hprefix tailTrace_4010171
  have hstable : (prefixWord ++ tailWord_4010171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010171).length < 2 ^ (prefixWord ++ tailWord_4010171).sum := by decide
  have hdescent : baseEnd_4010171 < baseStart_4010171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010181 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_4010181 : Nat := 118140960795 + 4010181 * 2 ^ 59
def prefixEnd_4010181 : Nat := 4983230072969 + 3 ^ 40 * 4010181 * 2
def baseEnd_4010181 : Nat := 2059150364527879882095019

theorem tailTrace_4010181 : CollatzResearch.WordTrace tailWord_4010181 prefixEnd_4010181 2059150364527879882095019 := by
  unfold tailWord_4010181
  simp only [CollatzResearch.WordTrace]
  refine ⟨146263317084806596233478397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97508878056537730822318931 146263317084806596233478397)
  ·
    refine ⟨54848743906802473587554399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146263317084806596233478397 54848743906802473587554399)
    ·
      refine ⟨82273115860203710381331599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54848743906802473587554399 82273115860203710381331599)
      ·
        refine ⟨123409673790305565571997399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82273115860203710381331599 123409673790305565571997399)
        ·
          refine ⟨185114510685458348357996099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123409673790305565571997399 185114510685458348357996099)
          ·
            refine ⟨277671766028187522536994149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185114510685458348357996099 277671766028187522536994149)
            ·
              refine ⟨52063456130285160475686403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277671766028187522536994149 52063456130285160475686403)
              ·
                refine ⟨78095184195427740713529605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52063456130285160475686403 78095184195427740713529605)
                ·
                  refine ⟨14642847036642701383786801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78095184195427740713529605 14642847036642701383786801)
                  ·
                    refine ⟨10982135277482026037840101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14642847036642701383786801 10982135277482026037840101)
                    ·
                      refine ⟨2059150364527879882095019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10982135277482026037840101 2059150364527879882095019)
                      ·
                        rfl

theorem cell23_4010181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_4010181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010181 prefixEnd_4010181 := by exact prefixLift 4010181
  have htrace : WordTrace (prefixWord ++ tailWord_4010181) baseStart_4010181 baseEnd_4010181 := by
    simpa [prefixWord, tailWord_4010181, baseEnd_4010181] using wordTrace_append hprefix tailTrace_4010181
  have hstable : (prefixWord ++ tailWord_4010181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010181).length < 2 ^ (prefixWord ++ tailWord_4010181).sum := by decide
  have hdescent : baseEnd_4010181 < baseStart_4010181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010242 : List Nat := [3, 4, 1, 1, 2, 2, 1, 4, 5]
def baseStart_4010242 : Nat := 118140960795 + 4010242 * 2 ^ 59
def prefixEnd_4010242 : Nat := 4983230072969 + 3 ^ 40 * 4010242 * 2
def baseEnd_4010242 : Nat := 228797965205311571492471

theorem tailTrace_4010242 : CollatzResearch.WordTrace tailWord_4010242 prefixEnd_4010242 228797965205311571492471 := by
  unfold tailWord_4010242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36566385484396400912862245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97510361291723735767632653 36566385484396400912862245)
  ·
    refine ⟨6856197278324325171161671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36566385484396400912862245 6856197278324325171161671)
    ·
      refine ⟨10284295917486487756742507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856197278324325171161671 10284295917486487756742507)
      ·
        refine ⟨15426443876229731635113761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10284295917486487756742507 15426443876229731635113761)
        ·
          refine ⟨11569832907172298726335321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15426443876229731635113761 11569832907172298726335321)
          ·
            refine ⟨8677374680379224044751491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11569832907172298726335321 8677374680379224044751491)
            ·
              refine ⟨13016062020568836067127237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677374680379224044751491 13016062020568836067127237)
              ·
                refine ⟨2440511628856656762586357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13016062020568836067127237 2440511628856656762586357)
                ·
                  refine ⟨228797965205311571492471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2440511628856656762586357 228797965205311571492471)
                  ·
                    rfl

theorem cell23_4010242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_4010242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010242 prefixEnd_4010242 := by exact prefixLift 4010242
  have htrace : WordTrace (prefixWord ++ tailWord_4010242) baseStart_4010242 baseEnd_4010242 := by
    simpa [prefixWord, tailWord_4010242, baseEnd_4010242] using wordTrace_append hprefix tailTrace_4010242
  have hstable : (prefixWord ++ tailWord_4010242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010242).length < 2 ^ (prefixWord ++ tailWord_4010242).sum := by decide
  have hdescent : baseEnd_4010242 < baseStart_4010242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010248 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_4010248 : Nat := 118140960795 + 4010248 * 2 ^ 59
def prefixEnd_4010248 : Nat := 4983230072969 + 3 ^ 40 * 4010248 * 2
def baseEnd_4010248 : Nat := 2059184767731731119957211

theorem tailTrace_4010248 : CollatzResearch.WordTrace tailWord_4010248 prefixEnd_4010248 2059184767731731119957211 := by
  unfold tailWord_4010248
  simp only [CollatzResearch.WordTrace]
  refine ⟨73132880387781933338083699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97510507183709244450778265 73132880387781933338083699)
  ·
    refine ⟨109699320581672900007125549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73132880387781933338083699 109699320581672900007125549)
    ·
      refine ⟨41137245218127337502672081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109699320581672900007125549 41137245218127337502672081)
      ·
        refine ⟨30852933913595503127004061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41137245218127337502672081 30852933913595503127004061)
        ·
          refine ⟨11569850217598313672626523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30852933913595503127004061 11569850217598313672626523)
          ·
            refine ⟨17354775326397470508939785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569850217598313672626523 17354775326397470508939785)
            ·
              refine ⟨13016081494798102881704839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17354775326397470508939785 13016081494798102881704839)
              ·
                refine ⟨19524122242197154322557259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13016081494798102881704839 19524122242197154322557259)
                ·
                  refine ⟨29286183363295731483835889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19524122242197154322557259 29286183363295731483835889)
                  ·
                    refine ⟨21964637522471798612876917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29286183363295731483835889 21964637522471798612876917)
                    ·
                      refine ⟨2059184767731731119957211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21964637522471798612876917 2059184767731731119957211)
                      ·
                        rfl

theorem cell23_4010248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_4010248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010248 prefixEnd_4010248 := by exact prefixLift 4010248
  have htrace : WordTrace (prefixWord ++ tailWord_4010248) baseStart_4010248 baseEnd_4010248 := by
    simpa [prefixWord, tailWord_4010248, baseEnd_4010248] using wordTrace_append hprefix tailTrace_4010248
  have hstable : (prefixWord ++ tailWord_4010248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010248).length < 2 ^ (prefixWord ++ tailWord_4010248).sum := by decide
  have hdescent : baseEnd_4010248 < baseStart_4010248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010292 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_4010292 : Nat := 118140960795 + 4010292 * 2 ^ 59
def prefixEnd_4010292 : Nat := 4983230072969 + 3 ^ 40 * 4010292 * 2
def baseEnd_4010292 : Nat := 2059207360880528947807009

theorem tailTrace_4010292 : CollatzResearch.WordTrace tailWord_4010292 prefixEnd_4010292 2059207360880528947807009 := by
  unfold tailWord_4010292
  simp only [CollatzResearch.WordTrace]
  refine ⟨73133682793702231095384565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97511577058269641460512753 73133682793702231095384565)
  ·
    refine ⟨6856282761909584165192303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73133682793702231095384565 6856282761909584165192303)
    ·
      refine ⟨10284424142864376247788455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856282761909584165192303 10284424142864376247788455)
      ·
        refine ⟨15426636214296564371682683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10284424142864376247788455 15426636214296564371682683)
        ·
          refine ⟨23139954321444846557524025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15426636214296564371682683 23139954321444846557524025)
          ·
            refine ⟨17354965741083634918143019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23139954321444846557524025 17354965741083634918143019)
            ·
              refine ⟨26032448611625452377214529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17354965741083634918143019 26032448611625452377214529)
              ·
                refine ⟨19524336458719089282910897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26032448611625452377214529 19524336458719089282910897)
                ·
                  refine ⟨14643252344039316962183173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19524336458719089282910897 14643252344039316962183173)
                  ·
                    refine ⟨2745609814507371930409345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14643252344039316962183173 2745609814507371930409345)
                    ·
                      refine ⟨2059207360880528947807009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745609814507371930409345 2059207360880528947807009)
                      ·
                        rfl

theorem cell23_4010292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_4010292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010292 prefixEnd_4010292 := by exact prefixLift 4010292
  have htrace : WordTrace (prefixWord ++ tailWord_4010292) baseStart_4010292 baseEnd_4010292 := by
    simpa [prefixWord, tailWord_4010292, baseEnd_4010292] using wordTrace_append hprefix tailTrace_4010292
  have hstable : (prefixWord ++ tailWord_4010292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010292).length < 2 ^ (prefixWord ++ tailWord_4010292).sum := by decide
  have hdescent : baseEnd_4010292 < baseStart_4010292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010298 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 8]
def baseStart_4010298 : Nat := 118140960795 + 4010298 * 2 ^ 59
def prefixEnd_4010298 : Nat := 4983230072969 + 3 ^ 40 * 4010298 * 2
def baseEnd_4010298 : Nat := 228801160196050658259109

theorem tailTrace_4010298 : CollatzResearch.WordTrace tailWord_4010298 prefixEnd_4010298 228801160196050658259109 := by
  unfold tailWord_4010298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36566896106345681303871887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97511722950255150143658365 36566896106345681303871887)
  ·
    refine ⟨54850344159518521955807831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36566896106345681303871887 54850344159518521955807831)
    ·
      refine ⟨82275516239277782933711747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54850344159518521955807831 82275516239277782933711747)
      ·
        refine ⟨123413274358916674400567621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82275516239277782933711747 123413274358916674400567621)
        ·
          refine ⟨23139988942296876450106429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123413274358916674400567621 23139988942296876450106429)
          ·
            refine ⟨8677495853361328668789911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23139988942296876450106429 8677495853361328668789911)
            ·
              refine ⟨13016243780041993003184867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677495853361328668789911 13016243780041993003184867)
              ·
                refine ⟨19524365670062989504777301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13016243780041993003184867 19524365670062989504777301)
                ·
                  refine ⟨228801160196050658259109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19524365670062989504777301 228801160196050658259109)
                  ·
                    rfl

theorem cell23_4010298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_4010298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010298 prefixEnd_4010298 := by exact prefixLift 4010298
  have htrace : WordTrace (prefixWord ++ tailWord_4010298) baseStart_4010298 baseEnd_4010298 := by
    simpa [prefixWord, tailWord_4010298, baseEnd_4010298] using wordTrace_append hprefix tailTrace_4010298
  have hstable : (prefixWord ++ tailWord_4010298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010298).length < 2 ^ (prefixWord ++ tailWord_4010298).sum := by decide
  have hdescent : baseEnd_4010298 < baseStart_4010298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010302 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_4010302 : Nat := 118140960795 + 4010302 * 2 ^ 59
def prefixEnd_4010302 : Nat := 4983230072969 + 3 ^ 40 * 4010302 * 2
def baseEnd_4010302 : Nat := 686404165229024636227321

theorem tailTrace_4010302 : CollatzResearch.WordTrace tailWord_4010302 prefixEnd_4010302 686404165229024636227321 := by
  unfold tailWord_4010302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18283466289671029237329145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97511820211578822599088773 18283466289671029237329145)
  ·
    refine ⟨13712599717253271927996859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18283466289671029237329145 13712599717253271927996859)
    ·
      refine ⟨20568899575879907891995289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13712599717253271927996859 20568899575879907891995289)
      ·
        refine ⟨15426674681909930918996467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20568899575879907891995289 15426674681909930918996467)
        ·
          refine ⟨23140012022864896378494701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15426674681909930918996467 23140012022864896378494701)
          ·
            refine ⟨8677504508574336141935513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23140012022864896378494701 8677504508574336141935513)
            ·
              refine ⟨6508128381430752106451635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8677504508574336141935513 6508128381430752106451635)
              ·
                refine ⟨9762192572146128159677453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6508128381430752106451635 9762192572146128159677453)
                ·
                  refine ⟨3660822214554798059879045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9762192572146128159677453 3660822214554798059879045)
                  ·
                    refine ⟨686404165229024636227321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660822214554798059879045 686404165229024636227321)
                    ·
                      rfl

theorem cell23_4010302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_4010302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010302 prefixEnd_4010302 := by exact prefixLift 4010302
  have htrace : WordTrace (prefixWord ++ tailWord_4010302) baseStart_4010302 baseEnd_4010302 := by
    simpa [prefixWord, tailWord_4010302, baseEnd_4010302] using wordTrace_append hprefix tailTrace_4010302
  have hstable : (prefixWord ++ tailWord_4010302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010302).length < 2 ^ (prefixWord ++ tailWord_4010302).sum := by decide
  have hdescent : baseEnd_4010302 < baseStart_4010302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010335 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 1, 5, 2]
def baseStart_4010335 : Nat := 118140960795 + 4010335 * 2 ^ 59
def prefixEnd_4010335 : Nat := 4983230072969 + 3 ^ 40 * 4010335 * 2
def baseEnd_4010335 : Nat := 2059229440548672279569311

theorem tailTrace_4010335 : CollatzResearch.WordTrace tailWord_4010335 prefixEnd_4010335 2059229440548672279569311 := by
  unfold tailWord_4010335
  simp only [CollatzResearch.WordTrace]
  refine ⟨146268933926248680534584459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97512622617499120356389639 146268933926248680534584459)
  ·
    refine ⟨219403400889373020801876689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146268933926248680534584459 219403400889373020801876689)
    ·
      refine ⟨164552550667029765601407517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219403400889373020801876689 164552550667029765601407517)
      ·
        refine ⟨61707206500136162100527819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164552550667029765601407517 61707206500136162100527819)
        ·
          refine ⟨92560809750204243150791729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61707206500136162100527819 92560809750204243150791729)
          ·
            refine ⟨69420607312653182363093797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92560809750204243150791729 69420607312653182363093797)
            ·
              refine ⟨13016363871122471693080087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69420607312653182363093797 13016363871122471693080087)
              ·
                refine ⟨19524545806683707539620131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13016363871122471693080087 19524545806683707539620131)
                ·
                  refine ⟨29286818710025561309430197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19524545806683707539620131 29286818710025561309430197)
                  ·
                    refine ⟨2745639254064896372759081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29286818710025561309430197 2745639254064896372759081)
                    ·
                      refine ⟨2059229440548672279569311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745639254064896372759081 2059229440548672279569311)
                      ·
                        rfl

theorem cell23_4010335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_4010335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010335 prefixEnd_4010335 := by exact prefixLift 4010335
  have htrace : WordTrace (prefixWord ++ tailWord_4010335) baseStart_4010335 baseEnd_4010335 := by
    simpa [prefixWord, tailWord_4010335, baseEnd_4010335] using wordTrace_append hprefix tailTrace_4010335
  have hstable : (prefixWord ++ tailWord_4010335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010335).length < 2 ^ (prefixWord ++ tailWord_4010335).sum := by decide
  have hdescent : baseEnd_4010335 < baseStart_4010335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010336 : List Nat := [2, 1, 1, 3, 6, 1, 1, 3, 1, 4]
def baseStart_4010336 : Nat := 118140960795 + 4010336 * 2 ^ 59
def prefixEnd_4010336 : Nat := 4983230072969 + 3 ^ 40 * 4010336 * 2
def baseEnd_4010336 : Nat := 686409984676442258552269

theorem tailTrace_4010336 : CollatzResearch.WordTrace tailWord_4010336 prefixEnd_4010336 686409984676442258552269 := by
  unfold tailWord_4010336
  simp only [CollatzResearch.WordTrace]
  refine ⟨73134485199622528852685431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97512646932830038470247241 73134485199622528852685431)
  ·
    refine ⟨109701727799433793279028147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73134485199622528852685431 109701727799433793279028147)
    ·
      refine ⟨164552591699150689918542221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109701727799433793279028147 164552591699150689918542221)
      ·
        refine ⟨61707221887181508719453333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164552591699150689918542221 61707221887181508719453333)
        ·
          refine ⟨2892526025961633221224375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61707221887181508719453333 2892526025961633221224375)
          ·
            refine ⟨4338789038942449831836563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892526025961633221224375 4338789038942449831836563)
            ·
              refine ⟨6508183558413674747754845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338789038942449831836563 6508183558413674747754845)
              ·
                refine ⟨2440568834405128030408067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6508183558413674747754845 2440568834405128030408067)
                ·
                  refine ⟨3660853251607692045612101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440568834405128030408067 3660853251607692045612101)
                  ·
                    refine ⟨686409984676442258552269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660853251607692045612101 686409984676442258552269)
                    ·
                      rfl

theorem cell23_4010336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 4].length) (baseStart_4010336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010336 prefixEnd_4010336 := by exact prefixLift 4010336
  have htrace : WordTrace (prefixWord ++ tailWord_4010336) baseStart_4010336 baseEnd_4010336 := by
    simpa [prefixWord, tailWord_4010336, baseEnd_4010336] using wordTrace_append hprefix tailTrace_4010336
  have hstable : (prefixWord ++ tailWord_4010336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010336).length < 2 ^ (prefixWord ++ tailWord_4010336).sum := by decide
  have hdescent : baseEnd_4010336 < baseStart_4010336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010352 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 2, 3, 2]
def baseStart_4010352 : Nat := 118140960795 + 4010352 * 2 ^ 59
def prefixEnd_4010352 : Nat := 4983230072969 + 3 ^ 40 * 4010352 * 2
def baseEnd_4010352 : Nat := 2059238169719798713056733

theorem tailTrace_4010352 : CollatzResearch.WordTrace tailWord_4010352 prefixEnd_4010352 2059238169719798713056733 := by
  unfold tailWord_4010352
  simp only [CollatzResearch.WordTrace]
  refine ⟨73134776983593546218976655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97513035978124728291968873 73134776983593546218976655)
  ·
    refine ⟨109702165475390319328464983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73134776983593546218976655 109702165475390319328464983)
    ·
      refine ⟨164553248213085478992697475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109702165475390319328464983 164553248213085478992697475)
      ·
        refine ⟨246829872319628218489046213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164553248213085478992697475 246829872319628218489046213)
        ·
          refine ⟨46280601059930290966696165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246829872319628218489046213 46280601059930290966696165)
          ·
            refine ⟨8677612698736929556255531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46280601059930290966696165 8677612698736929556255531)
            ·
              refine ⟨13016419048105394334383297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677612698736929556255531 13016419048105394334383297)
              ·
                refine ⟨9762314286079045750787473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13016419048105394334383297 9762314286079045750787473)
                ·
                  refine ⟨7321735714559284313090605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9762314286079045750787473 7321735714559284313090605)
                  ·
                    refine ⟨2745650892959731617408977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7321735714559284313090605 2745650892959731617408977)
                    ·
                      refine ⟨2059238169719798713056733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745650892959731617408977 2059238169719798713056733)
                      ·
                        rfl

theorem cell23_4010352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 3, 2].length) (baseStart_4010352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010352 prefixEnd_4010352 := by exact prefixLift 4010352
  have htrace : WordTrace (prefixWord ++ tailWord_4010352) baseStart_4010352 baseEnd_4010352 := by
    simpa [prefixWord, tailWord_4010352, baseEnd_4010352] using wordTrace_append hprefix tailTrace_4010352
  have hstable : (prefixWord ++ tailWord_4010352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010352).length < 2 ^ (prefixWord ++ tailWord_4010352).sum := by decide
  have hdescent : baseEnd_4010352 < baseStart_4010352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010368 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 3]
def baseStart_4010368 : Nat := 118140960795 + 4010368 * 2 ^ 59
def prefixEnd_4010368 : Nat := 4983230072969 + 3 ^ 40 * 4010368 * 2
def baseEnd_4010368 : Nat := 2059246385410270650456659

theorem tailTrace_4010368 : CollatzResearch.WordTrace tailWord_4010368 prefixEnd_4010368 2059246385410270650456659 := by
  unfold tailWord_4010368
  simp only [CollatzResearch.WordTrace]
  refine ⟨73135068767564563585267879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97513425023419418113690505 73135068767564563585267879)
  ·
    refine ⟨109702603151346845377901819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73135068767564563585267879 109702603151346845377901819)
    ·
      refine ⟨164553904727020268066852729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109702603151346845377901819 164553904727020268066852729)
      ·
        refine ⟨123415428545265201050139547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164553904727020268066852729 123415428545265201050139547)
        ·
          refine ⟨185123142817897801575209321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123415428545265201050139547 185123142817897801575209321)
          ·
            refine ⟨138842357113423351181406991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185123142817897801575209321 138842357113423351181406991)
            ·
              refine ⟨208263535670135026772110487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138842357113423351181406991 208263535670135026772110487)
              ·
                refine ⟨312395303505202540158165731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208263535670135026772110487 312395303505202540158165731)
                ·
                  refine ⟨468592955257803810237248597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312395303505202540158165731 468592955257803810237248597)
                  ·
                    refine ⟨5491323694427388401217757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 468592955257803810237248597 5491323694427388401217757)
                    ·
                      refine ⟨2059246385410270650456659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5491323694427388401217757 2059246385410270650456659)
                      ·
                        rfl

theorem cell23_4010368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_4010368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010368 prefixEnd_4010368 := by exact prefixLift 4010368
  have htrace : WordTrace (prefixWord ++ tailWord_4010368) baseStart_4010368 baseEnd_4010368 := by
    simpa [prefixWord, tailWord_4010368, baseEnd_4010368] using wordTrace_append hprefix tailTrace_4010368
  have hstable : (prefixWord ++ tailWord_4010368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010368).length < 2 ^ (prefixWord ++ tailWord_4010368).sum := by decide
  have hdescent : baseEnd_4010368 < baseStart_4010368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010382 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4010382 : Nat := 118140960795 + 4010382 * 2 ^ 59
def prefixEnd_4010382 : Nat := 4983230072969 + 3 ^ 40 * 4010382 * 2
def baseEnd_4010382 : Nat := 2059253574139433595681595

theorem tailTrace_4010382 : CollatzResearch.WordTrace tailWord_4010382 prefixEnd_4010382 2059253574139433595681595 := by
  unfold tailWord_4010382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18283831019634800945193175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97513765438052271707696933 18283831019634800945193175)
  ·
    refine ⟨27425746529452201417789763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18283831019634800945193175 27425746529452201417789763)
    ·
      refine ⟨41138619794178302126684645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27425746529452201417789763 41138619794178302126684645)
      ·
        refine ⟨7713491211408431648753371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41138619794178302126684645 7713491211408431648753371)
        ·
          refine ⟨11570236817112647473130057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7713491211408431648753371 11570236817112647473130057)
          ·
            refine ⟨8677677612834485604847543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11570236817112647473130057 8677677612834485604847543)
            ·
              refine ⟨13016516419251728407271315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677677612834485604847543 13016516419251728407271315)
              ·
                refine ⟨19524774628877592610906973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13016516419251728407271315 19524774628877592610906973)
                ·
                  refine ⟨7321790485829097229090115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19524774628877592610906973 7321790485829097229090115)
                  ·
                    refine ⟨10982685728743645843635173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7321790485829097229090115 10982685728743645843635173)
                    ·
                      refine ⟨2059253574139433595681595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10982685728743645843635173 2059253574139433595681595)
                      ·
                        rfl

theorem cell23_4010382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4010382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010382 prefixEnd_4010382 := by exact prefixLift 4010382
  have htrace : WordTrace (prefixWord ++ tailWord_4010382) baseStart_4010382 baseEnd_4010382 := by
    simpa [prefixWord, tailWord_4010382, baseEnd_4010382] using wordTrace_append hprefix tailTrace_4010382
  have hstable : (prefixWord ++ tailWord_4010382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010382).length < 2 ^ (prefixWord ++ tailWord_4010382).sum := by decide
  have hdescent : baseEnd_4010382 < baseStart_4010382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010410 : List Nat := [3, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4010410 : Nat := 118140960795 + 4010410 * 2 ^ 59
def prefixEnd_4010410 : Nat := 4983230072969 + 3 ^ 40 * 4010410 * 2
def baseEnd_4010410 : Nat := 2059267951597759486131467

theorem tailTrace_4010410 : CollatzResearch.WordTrace tailWord_4010410 prefixEnd_4010410 2059267951597759486131467 := by
  unfold tailWord_4010410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36567917350244242085891171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97514446267317978895709789 36567917350244242085891171)
  ·
    refine ⟨54851876025366363128836757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36567917350244242085891171 54851876025366363128836757)
    ·
      refine ⟨2571181688689048271664223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54851876025366363128836757 2571181688689048271664223)
      ·
        refine ⟨3856772533033572407496335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571181688689048271664223 3856772533033572407496335)
        ·
          refine ⟨5785158799550358611244503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856772533033572407496335 5785158799550358611244503)
          ·
            refine ⟨8677738199325537916866755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785158799550358611244503 8677738199325537916866755)
            ·
              refine ⟨13016607298988306875300133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677738199325537916866755 13016607298988306875300133)
              ·
                refine ⟨2440613868560307539118775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13016607298988306875300133 2440613868560307539118775)
                ·
                  refine ⟨3660920802840461308678163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440613868560307539118775 3660920802840461308678163)
                  ·
                    refine ⟨5491381204260691963017245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3660920802840461308678163 5491381204260691963017245)
                    ·
                      refine ⟨2059267951597759486131467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5491381204260691963017245 2059267951597759486131467)
                      ·
                        rfl

theorem cell23_4010410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4010410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010410 prefixEnd_4010410 := by exact prefixLift 4010410
  have htrace : WordTrace (prefixWord ++ tailWord_4010410) baseStart_4010410 baseEnd_4010410 := by
    simpa [prefixWord, tailWord_4010410, baseEnd_4010410] using wordTrace_append hprefix tailTrace_4010410
  have hstable : (prefixWord ++ tailWord_4010410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010410).length < 2 ^ (prefixWord ++ tailWord_4010410).sum := by decide
  have hdescent : baseEnd_4010410 < baseStart_4010410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010418 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_4010418 : Nat := 118140960795 + 4010418 * 2 ^ 59
def prefixEnd_4010418 : Nat := 4983230072969 + 3 ^ 40 * 4010418 * 2
def baseEnd_4010418 : Nat := 686424019814331818277143

theorem tailTrace_4010418 : CollatzResearch.WordTrace tailWord_4010418 prefixEnd_4010418 686424019814331818277143 := by
  unfold tailWord_4010418
  simp only [CollatzResearch.WordTrace]
  refine ⟨36567990296236996427463977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97514640789965323806570605 36567990296236996427463977)
  ·
    refine ⟨27425992722177747320597983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36567990296236996427463977 27425992722177747320597983)
    ·
      refine ⟨41138989083266620980896975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27425992722177747320597983 41138989083266620980896975)
      ·
        refine ⟨61708483624899931471345463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41138989083266620980896975 61708483624899931471345463)
        ·
          refine ⟨92562725437349897207018195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61708483624899931471345463 92562725437349897207018195)
          ·
            refine ⟨138844088156024845810527293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92562725437349897207018195 138844088156024845810527293)
            ·
              refine ⟨52066533058509317178947735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138844088156024845810527293 52066533058509317178947735)
              ·
                refine ⟨78099799587763975768421603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52066533058509317178947735 78099799587763975768421603)
                ·
                  refine ⟨117149699381645963652632405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78099799587763975768421603 117149699381645963652632405)
                  ·
                    refine ⟨686424019814331818277143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 117149699381645963652632405 686424019814331818277143)
                    ·
                      rfl

theorem cell23_4010418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_4010418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010418 prefixEnd_4010418 := by exact prefixLift 4010418
  have htrace : WordTrace (prefixWord ++ tailWord_4010418) baseStart_4010418 baseEnd_4010418 := by
    simpa [prefixWord, tailWord_4010418, baseEnd_4010418] using wordTrace_append hprefix tailTrace_4010418
  have hstable : (prefixWord ++ tailWord_4010418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010418).length < 2 ^ (prefixWord ++ tailWord_4010418).sum := by decide
  have hdescent : baseEnd_4010418 < baseStart_4010418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010442 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_4010442 : Nat := 118140960795 + 4010442 * 2 ^ 59
def prefixEnd_4010442 : Nat := 4983230072969 + 3 ^ 40 * 4010442 * 2
def baseEnd_4010442 : Nat := 2059284382978703360931319

theorem tailTrace_4010442 : CollatzResearch.WordTrace tailWord_4010442 prefixEnd_4010442 2059284382978703360931319 := by
  unfold tailWord_4010442
  simp only [CollatzResearch.WordTrace]
  refine ⟨36568209134215259452182395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97515224357907358539153053 36568209134215259452182395)
  ·
    refine ⟨54852313701322889178273593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36568209134215259452182395 54852313701322889178273593)
    ·
      refine ⟨41139235275992166883705195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54852313701322889178273593 41139235275992166883705195)
      ·
        refine ⟨61708852913988250325557793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41139235275992166883705195 61708852913988250325557793)
        ·
          refine ⟨46281639685491187744168345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61708852913988250325557793 46281639685491187744168345)
          ·
            refine ⟨34711229764118390808126259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46281639685491187744168345 34711229764118390808126259)
            ·
              refine ⟨52066844646177586212189389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34711229764118390808126259 52066844646177586212189389)
              ·
                refine ⟨19525066742316594829571021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52066844646177586212189389 19525066742316594829571021)
                ·
                  refine ⟨7321900028368723061089133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19525066742316594829571021 7321900028368723061089133)
                  ·
                    refine ⟨2745712510638271147908425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7321900028368723061089133 2745712510638271147908425)
                    ·
                      refine ⟨2059284382978703360931319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745712510638271147908425 2059284382978703360931319)
                      ·
                        rfl

theorem cell23_4010442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_4010442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010442 prefixEnd_4010442 := by exact prefixLift 4010442
  have htrace : WordTrace (prefixWord ++ tailWord_4010442) baseStart_4010442 baseEnd_4010442 := by
    simpa [prefixWord, tailWord_4010442, baseEnd_4010442] using wordTrace_append hprefix tailTrace_4010442
  have hstable : (prefixWord ++ tailWord_4010442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010442).length < 2 ^ (prefixWord ++ tailWord_4010442).sum := by decide
  have hdescent : baseEnd_4010442 < baseStart_4010442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010448 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 6, 6]
def baseStart_4010448 : Nat := 118140960795 + 4010448 * 2 ^ 59
def prefixEnd_4010448 : Nat := 4983230072969 + 3 ^ 40 * 4010448 * 2
def baseEnd_4010448 : Nat := 686429154620876779152097

theorem tailTrace_4010448 : CollatzResearch.WordTrace tailWord_4010448 prefixEnd_4010448 686429154620876779152097 := by
  unfold tailWord_4010448
  simp only [CollatzResearch.WordTrace]
  refine ⟨73136527687419650416723999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97515370249892867222298665 73136527687419650416723999)
  ·
    refine ⟨109704791531129475625085999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73136527687419650416723999 109704791531129475625085999)
    ·
      refine ⟨164557187296694213437628999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109704791531129475625085999 164557187296694213437628999)
      ·
        refine ⟨246835780945041320156443499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164557187296694213437628999 246835780945041320156443499)
        ·
          refine ⟨370253671417561980234665249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246835780945041320156443499 370253671417561980234665249)
          ·
            refine ⟨277690253563171485175998937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370253671417561980234665249 277690253563171485175998937)
            ·
              refine ⟨208267690172378613881999203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277690253563171485175998937 208267690172378613881999203)
              ·
                refine ⟨312401535258567920822998805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208267690172378613881999203 312401535258567920822998805)
                ·
                  refine ⟨14643821965245371288578069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 312401535258567920822998805 14643821965245371288578069)
                  ·
                    refine ⟨686429154620876779152097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14643821965245371288578069 686429154620876779152097)
                    ·
                      rfl

theorem cell23_4010448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_4010448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010448 prefixEnd_4010448 := by exact prefixLift 4010448
  have htrace : WordTrace (prefixWord ++ tailWord_4010448) baseStart_4010448 baseEnd_4010448 := by
    simpa [prefixWord, tailWord_4010448, baseEnd_4010448] using wordTrace_append hprefix tailTrace_4010448
  have hstable : (prefixWord ++ tailWord_4010448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010448).length < 2 ^ (prefixWord ++ tailWord_4010448).sum := by decide
  have hdescent : baseEnd_4010448 < baseStart_4010448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010450 : List Nat := [3, 2, 2, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4010450 : Nat := 118140960795 + 4010450 * 2 ^ 59
def prefixEnd_4010450 : Nat := 4983230072969 + 3 ^ 40 * 4010450 * 2
def baseEnd_4010450 : Nat := 2059288490823939329631283

theorem tailTrace_4010450 : CollatzResearch.WordTrace tailWord_4010450 prefixEnd_4010450 2059288490823939329631283 := by
  unfold tailWord_4010450
  simp only [CollatzResearch.WordTrace]
  refine ⟨36568282080208013793755201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97515418880554703450013869 36568282080208013793755201)
  ·
    refine ⟨27426211560156010345316401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36568282080208013793755201 27426211560156010345316401)
    ·
      refine ⟨20569658670117007758987301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27426211560156010345316401 20569658670117007758987301)
      ·
        refine ⟨3856811000646938954810119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20569658670117007758987301 3856811000646938954810119)
        ·
          refine ⟨5785216500970408432215179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856811000646938954810119 5785216500970408432215179)
          ·
            refine ⟨8677824751455612648322769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785216500970408432215179 8677824751455612648322769)
            ·
              refine ⟨6508368563591709486242077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8677824751455612648322769 6508368563591709486242077)
              ·
                refine ⟨2440638211346891057340779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6508368563591709486242077 2440638211346891057340779)
                ·
                  refine ⟨3660957317020336586011169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440638211346891057340779 3660957317020336586011169)
                  ·
                    refine ⟨2745717987765252439508377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3660957317020336586011169 2745717987765252439508377)
                    ·
                      refine ⟨2059288490823939329631283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745717987765252439508377 2059288490823939329631283)
                      ·
                        rfl

theorem cell23_4010450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4010450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010450 prefixEnd_4010450 := by exact prefixLift 4010450
  have htrace : WordTrace (prefixWord ++ tailWord_4010450) baseStart_4010450 baseEnd_4010450 := by
    simpa [prefixWord, tailWord_4010450, baseEnd_4010450] using wordTrace_append hprefix tailTrace_4010450
  have hstable : (prefixWord ++ tailWord_4010450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010450).length < 2 ^ (prefixWord ++ tailWord_4010450).sum := by decide
  have hdescent : baseEnd_4010450 < baseStart_4010450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010489 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 2, 2, 2]
def baseStart_4010489 : Nat := 118140960795 + 4010489 * 2 ^ 59
def prefixEnd_4010489 : Nat := 4983230072969 + 3 ^ 40 * 4010489 * 2
def baseEnd_4010489 : Nat := 2059308516569464677043603

theorem tailTrace_4010489 : CollatzResearch.WordTrace tailWord_4010489 prefixEnd_4010489 2059308516569464677043603 := by
  unfold tailWord_4010489
  simp only [CollatzResearch.WordTrace]
  refine ⟨146274550767690764835690521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97516367178460509890460347 146274550767690764835690521)
  ·
    refine ⟨109705913075768073626767891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146274550767690764835690521 109705913075768073626767891)
    ·
      refine ⟨164558869613652110440151837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109705913075768073626767891 164558869613652110440151837)
      ·
        refine ⟨61709576105119541415056939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164558869613652110440151837 61709576105119541415056939)
        ·
          refine ⟨92564364157679312122585409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61709576105119541415056939 92564364157679312122585409)
          ·
            refine ⟨69423273118259484091939057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92564364157679312122585409 69423273118259484091939057)
            ·
              refine ⟨52067454838694613068954293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69423273118259484091939057 52067454838694613068954293)
              ·
                refine ⟨4881323891127619975214465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52067454838694613068954293 4881323891127619975214465)
                ·
                  refine ⟨3660992918345714981410849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4881323891127619975214465 3660992918345714981410849)
                  ·
                    refine ⟨2745744688759286236058137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3660992918345714981410849 2745744688759286236058137)
                    ·
                      refine ⟨2059308516569464677043603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745744688759286236058137 2059308516569464677043603)
                      ·
                        rfl

theorem cell23_4010489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_4010489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010489 prefixEnd_4010489 := by exact prefixLift 4010489
  have htrace : WordTrace (prefixWord ++ tailWord_4010489) baseStart_4010489 baseEnd_4010489 := by
    simpa [prefixWord, tailWord_4010489, baseEnd_4010489] using wordTrace_append hprefix tailTrace_4010489
  have hstable : (prefixWord ++ tailWord_4010489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010489).length < 2 ^ (prefixWord ++ tailWord_4010489).sum := by decide
  have hdescent : baseEnd_4010489 < baseStart_4010489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010505 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 3]
def baseStart_4010505 : Nat := 118140960795 + 4010505 * 2 ^ 59
def prefixEnd_4010505 : Nat := 4983230072969 + 3 ^ 40 * 4010505 * 2
def baseEnd_4010505 : Nat := 2059316732259936614443529

theorem tailTrace_4010505 : CollatzResearch.WordTrace tailWord_4010505 prefixEnd_4010505 2059316732259936614443529 := by
  unfold tailWord_4010505
  simp only [CollatzResearch.WordTrace]
  refine ⟨146275134335632799568272969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97516756223755199712181979 146275134335632799568272969)
  ·
    refine ⟨109706350751724599676204727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146275134335632799568272969 109706350751724599676204727)
    ·
      refine ⟨164559526127586899514307091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109706350751724599676204727 164559526127586899514307091)
      ·
        refine ⟨246839289191380349271460637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164559526127586899514307091 246839289191380349271460637)
        ·
          refine ⟨92564733446767630976797739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246839289191380349271460637 92564733446767630976797739)
          ·
            refine ⟨138847100170151446465196609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92564733446767630976797739 138847100170151446465196609)
            ·
              refine ⟨104135325127613584848897457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138847100170151446465196609 104135325127613584848897457)
              ·
                refine ⟨78101493845710188636673093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104135325127613584848897457 78101493845710188636673093)
                ·
                  refine ⟨14644030096070660369376205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78101493845710188636673093 14644030096070660369376205)
                  ·
                    refine ⟨5491511286026497638516077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14644030096070660369376205 5491511286026497638516077)
                    ·
                      refine ⟨2059316732259936614443529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5491511286026497638516077 2059316732259936614443529)
                      ·
                        rfl

theorem cell23_4010505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_4010505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010505 prefixEnd_4010505 := by exact prefixLift 4010505
  have htrace : WordTrace (prefixWord ++ tailWord_4010505) baseStart_4010505 baseEnd_4010505 := by
    simpa [prefixWord, tailWord_4010505, baseEnd_4010505] using wordTrace_append hprefix tailTrace_4010505
  have hstable : (prefixWord ++ tailWord_4010505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010505).length < 2 ^ (prefixWord ++ tailWord_4010505).sum := by decide
  have hdescent : baseEnd_4010505 < baseStart_4010505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010509 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4010509 : Nat := 118140960795 + 4010509 * 2 ^ 59
def prefixEnd_4010509 : Nat := 4983230072969 + 3 ^ 40 * 4010509 * 2
def baseEnd_4010509 : Nat := 2059318786182554598793511

theorem tailTrace_4010509 : CollatzResearch.WordTrace tailWord_4010509 prefixEnd_4010509 2059318786182554598793511 := by
  unfold tailWord_4010509
  simp only [CollatzResearch.WordTrace]
  refine ⟨146275280227618308251418581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97516853485078872167612387 146275280227618308251418581)
  ·
    refine ⟨3428326880334804099642623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 146275280227618308251418581 3428326880334804099642623)
    ·
      refine ⟨5142490320502206149463935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3428326880334804099642623 5142490320502206149463935)
      ·
        refine ⟨7713735480753309224195903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142490320502206149463935 7713735480753309224195903)
        ·
          refine ⟨11570603221129963836293855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7713735480753309224195903 11570603221129963836293855)
          ·
            refine ⟨17355904831694945754440783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11570603221129963836293855 17355904831694945754440783)
            ·
              refine ⟨26033857247542418631661175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17355904831694945754440783 26033857247542418631661175)
              ·
                refine ⟨39050785871313627947491763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26033857247542418631661175 39050785871313627947491763)
                ·
                  refine ⟨58576178806970441921237645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39050785871313627947491763 58576178806970441921237645)
                  ·
                    refine ⟨21966067052613915720464117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58576178806970441921237645 21966067052613915720464117)
                    ·
                      refine ⟨2059318786182554598793511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21966067052613915720464117 2059318786182554598793511)
                      ·
                        rfl

theorem cell23_4010509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4010509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010509 prefixEnd_4010509 := by exact prefixLift 4010509
  have htrace : WordTrace (prefixWord ++ tailWord_4010509) baseStart_4010509 baseEnd_4010509 := by
    simpa [prefixWord, tailWord_4010509, baseEnd_4010509] using wordTrace_append hprefix tailTrace_4010509
  have hstable : (prefixWord ++ tailWord_4010509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010509).length < 2 ^ (prefixWord ++ tailWord_4010509).sum := by decide
  have hdescent : baseEnd_4010509 < baseStart_4010509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010529 : List Nat := [1, 2, 3, 2, 2, 1, 5, 2, 5]
def baseStart_4010529 : Nat := 118140960795 + 4010529 * 2 ^ 59
def prefixEnd_4010529 : Nat := 4983230072969 + 3 ^ 40 * 4010529 * 2
def baseEnd_4010529 : Nat := 228814339532849391171491

theorem tailTrace_4010529 : CollatzResearch.WordTrace tailWord_4010529 prefixEnd_4010529 228814339532849391171491 := by
  unfold tailWord_4010529
  simp only [CollatzResearch.WordTrace]
  refine ⟨146276009687545851667146641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97517339791697234444764427 146276009687545851667146641)
  ·
    refine ⟨109707007265659388750359981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146276009687545851667146641 109707007265659388750359981)
    ·
      refine ⟨41140127724622270781384993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109707007265659388750359981 41140127724622270781384993)
      ·
        refine ⟨30855095793466703086038745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41140127724622270781384993 30855095793466703086038745)
        ·
          refine ⟨23141321845100027314529059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30855095793466703086038745 23141321845100027314529059)
          ·
            refine ⟨34711982767650040971793589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23141321845100027314529059 34711982767650040971793589)
            ·
              refine ⟨3254248384467191341105649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34711982767650040971793589 3254248384467191341105649)
              ·
                refine ⟨2440686288350393505829237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3254248384467191341105649 2440686288350393505829237)
                ·
                  refine ⟨228814339532849391171491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2440686288350393505829237 228814339532849391171491)
                  ·
                    rfl

theorem cell23_4010529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 5].length) (baseStart_4010529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010529 prefixEnd_4010529 := by exact prefixLift 4010529
  have htrace : WordTrace (prefixWord ++ tailWord_4010529) baseStart_4010529 baseEnd_4010529 := by
    simpa [prefixWord, tailWord_4010529, baseEnd_4010529] using wordTrace_append hprefix tailTrace_4010529
  have hstable : (prefixWord ++ tailWord_4010529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010529).length < 2 ^ (prefixWord ++ tailWord_4010529).sum := by decide
  have hdescent : baseEnd_4010529 < baseStart_4010529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010545 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_4010545 : Nat := 118140960795 + 4010545 * 2 ^ 59
def prefixEnd_4010545 : Nat := 4983230072969 + 3 ^ 40 * 4010545 * 2
def baseEnd_4010545 : Nat := 2059337271486116457943345

theorem tailTrace_4010545 : CollatzResearch.WordTrace tailWord_4010545 prefixEnd_4010545 2059337271486116457943345 := by
  unfold tailWord_4010545
  simp only [CollatzResearch.WordTrace]
  refine ⟨146276593255487886399729089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97517728836991924266486059 146276593255487886399729089)
  ·
    refine ⟨109707444941615914799796817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146276593255487886399729089 109707444941615914799796817)
    ·
      refine ⟨82280583706211936099847613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109707444941615914799796817 82280583706211936099847613)
      ·
        refine ⟨30855218889829476037442855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82280583706211936099847613 30855218889829476037442855)
        ·
          refine ⟨46282828334744214056164283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30855218889829476037442855 46282828334744214056164283)
          ·
            refine ⟨69424242502116321084246425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46282828334744214056164283 69424242502116321084246425)
            ·
              refine ⟨52068181876587240813184819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69424242502116321084246425 52068181876587240813184819)
              ·
                refine ⟨78102272814880861219777229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52068181876587240813184819 78102272814880861219777229)
                ·
                  refine ⟨29288352305580322957416461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78102272814880861219777229 29288352305580322957416461)
                  ·
                    refine ⟨10983132114592621109031173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29288352305580322957416461 10983132114592621109031173)
                    ·
                      refine ⟨2059337271486116457943345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10983132114592621109031173 2059337271486116457943345)
                      ·
                        rfl

theorem cell23_4010545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_4010545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010545 prefixEnd_4010545 := by exact prefixLift 4010545
  have htrace : WordTrace (prefixWord ++ tailWord_4010545) baseStart_4010545 baseEnd_4010545 := by
    simpa [prefixWord, tailWord_4010545, baseEnd_4010545] using wordTrace_append hprefix tailTrace_4010545
  have hstable : (prefixWord ++ tailWord_4010545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010545).length < 2 ^ (prefixWord ++ tailWord_4010545).sum := by decide
  have hdescent : baseEnd_4010545 < baseStart_4010545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010602 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 6]
def baseStart_4010602 : Nat := 118140960795 + 4010602 * 2 ^ 59
def prefixEnd_4010602 : Nat := 4983230072969 + 3 ^ 40 * 4010602 * 2
def baseEnd_4010602 : Nat := 228818504431491414992287

theorem tailTrace_4010602 : CollatzResearch.WordTrace tailWord_4010602 prefixEnd_4010602 228818504431491414992287 := by
  unfold tailWord_4010602
  simp only [CollatzResearch.WordTrace]
  refine ⟨36569668054070346283638515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97519114810854256756369373 36569668054070346283638515)
  ·
    refine ⟨54854502081105519425457773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36569668054070346283638515 54854502081105519425457773)
    ·
      refine ⟨20570438280414569784546665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54854502081105519425457773 20570438280414569784546665)
      ·
        refine ⟨15427828710310927338409999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20570438280414569784546665 15427828710310927338409999)
        ·
          refine ⟨23141743065466391007614999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15427828710310927338409999 23141743065466391007614999)
          ·
            refine ⟨34712614598199586511422499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23141743065466391007614999 34712614598199586511422499)
            ·
              refine ⟨52068921897299379767133749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34712614598199586511422499 52068921897299379767133749)
              ·
                refine ⟨4881461427871816853168789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52068921897299379767133749 4881461427871816853168789)
                ·
                  refine ⟨228818504431491414992287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4881461427871816853168789 228818504431491414992287)
                  ·
                    rfl

theorem cell23_4010602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_4010602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010602 prefixEnd_4010602 := by exact prefixLift 4010602
  have htrace : WordTrace (prefixWord ++ tailWord_4010602) baseStart_4010602 baseEnd_4010602 := by
    simpa [prefixWord, tailWord_4010602, baseEnd_4010602] using wordTrace_append hprefix tailTrace_4010602
  have hstable : (prefixWord ++ tailWord_4010602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010602).length < 2 ^ (prefixWord ++ tailWord_4010602).sum := by decide
  have hdescent : baseEnd_4010602 < baseStart_4010602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010613 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_4010613 : Nat := 118140960795 + 4010613 * 2 ^ 59
def prefixEnd_4010613 : Nat := 4983230072969 + 3 ^ 40 * 4010613 * 2
def baseEnd_4010613 : Nat := 2059372188170622191893033

theorem tailTrace_4010613 : CollatzResearch.WordTrace tailWord_4010613 prefixEnd_4010613 2059372188170622191893033 := by
  unfold tailWord_4010613
  simp only [CollatzResearch.WordTrace]
  refine ⟨146279073419241534013204493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97519382279494356008802995 146279073419241534013204493)
  ·
    refine ⟨54854652532215575254951685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146279073419241534013204493 54854652532215575254951685)
    ·
      refine ⟨10285247349790420360303441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54854652532215575254951685 10285247349790420360303441)
      ·
        refine ⟨7713935512342815270227581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10285247349790420360303441 7713935512342815270227581)
        ·
          refine ⟨2892725817128555726335343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7713935512342815270227581 2892725817128555726335343)
          ·
            refine ⟨4339088725692833589503015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892725817128555726335343 4339088725692833589503015)
            ·
              refine ⟨6508633088539250384254523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339088725692833589503015 6508633088539250384254523)
              ·
                refine ⟨9762949632808875576381785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6508633088539250384254523 9762949632808875576381785)
                ·
                  refine ⟨7322212224606656682286339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9762949632808875576381785 7322212224606656682286339)
                  ·
                    refine ⟨10983318336909985023429509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7322212224606656682286339 10983318336909985023429509)
                    ·
                      refine ⟨2059372188170622191893033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10983318336909985023429509 2059372188170622191893033)
                      ·
                        rfl

theorem cell23_4010613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_4010613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010613 prefixEnd_4010613 := by exact prefixLift 4010613
  have htrace : WordTrace (prefixWord ++ tailWord_4010613) baseStart_4010613 baseEnd_4010613 := by
    simpa [prefixWord, tailWord_4010613, baseEnd_4010613] using wordTrace_append hprefix tailTrace_4010613
  have hstable : (prefixWord ++ tailWord_4010613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010613).length < 2 ^ (prefixWord ++ tailWord_4010613).sum := by decide
  have hdescent : baseEnd_4010613 < baseStart_4010613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010645 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_4010645 : Nat := 118140960795 + 4010645 * 2 ^ 59
def prefixEnd_4010645 : Nat := 4983230072969 + 3 ^ 40 * 4010645 * 2
def baseEnd_4010645 : Nat := 686462873183855355564295

theorem tailTrace_4010645 : CollatzResearch.WordTrace tailWord_4010645 prefixEnd_4010645 686462873183855355564295 := by
  unfold tailWord_4010645
  simp only [CollatzResearch.WordTrace]
  refine ⟨146280240555125603478369389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97520160370083735652246259 146280240555125603478369389)
  ·
    refine ⟨54855090208172101304388521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146280240555125603478369389 54855090208172101304388521)
    ·
      refine ⟨41141317656129075978291391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54855090208172101304388521 41141317656129075978291391)
      ·
        refine ⟨61711976484193613967437087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41141317656129075978291391 61711976484193613967437087)
        ·
          refine ⟨92567964726290420951155631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61711976484193613967437087 92567964726290420951155631)
          ·
            refine ⟨138851947089435631426733447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92567964726290420951155631 138851947089435631426733447)
            ·
              refine ⟨208277920634153447140100171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138851947089435631426733447 208277920634153447140100171)
              ·
                refine ⟨312416880951230170710150257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208277920634153447140100171 312416880951230170710150257)
                ·
                  refine ⟨234312660713422628032612693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312416880951230170710150257 234312660713422628032612693)
                  ·
                    refine ⟨686462873183855355564295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 234312660713422628032612693 686462873183855355564295)
                    ·
                      rfl

theorem cell23_4010645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_4010645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010645 prefixEnd_4010645 := by exact prefixLift 4010645
  have htrace : WordTrace (prefixWord ++ tailWord_4010645) baseStart_4010645 baseEnd_4010645 := by
    simpa [prefixWord, tailWord_4010645, baseEnd_4010645] using wordTrace_append hprefix tailTrace_4010645
  have hstable : (prefixWord ++ tailWord_4010645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010645).length < 2 ^ (prefixWord ++ tailWord_4010645).sum := by decide
  have hdescent : baseEnd_4010645 < baseStart_4010645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010682 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_4010682 : Nat := 118140960795 + 4010682 * 2 ^ 59
def prefixEnd_4010682 : Nat := 4983230072969 + 3 ^ 40 * 4010682 * 2
def baseEnd_4010682 : Nat := 2059407618335782421930215

theorem tailTrace_4010682 : CollatzResearch.WordTrace tailWord_4010682 prefixEnd_4010682 2059407618335782421930215 := by
  unfold tailWord_4010682
  simp only [CollatzResearch.WordTrace]
  refine ⟨36570397513997889699366575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97521060037327705864977533 36570397513997889699366575)
  ·
    refine ⟨54855596270996834549049863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36570397513997889699366575 54855596270996834549049863)
    ·
      refine ⟨82283394406495251823574795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54855596270996834549049863 82283394406495251823574795)
      ·
        refine ⟨123425091609742877735362193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82283394406495251823574795 123425091609742877735362193)
        ·
          refine ⟨92568818707307158301521645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123425091609742877735362193 92568818707307158301521645)
          ·
            refine ⟨34713307015240184363070617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92568818707307158301521645 34713307015240184363070617)
            ·
              refine ⟨26034980261430138272302963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34713307015240184363070617 26034980261430138272302963)
              ·
                refine ⟨39052470392145207408454445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26034980261430138272302963 39052470392145207408454445)
                ·
                  refine ⟨14644676397054452778170417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39052470392145207408454445 14644676397054452778170417)
                  ·
                    refine ⟨10983507297790839583627813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14644676397054452778170417 10983507297790839583627813)
                    ·
                      refine ⟨2059407618335782421930215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10983507297790839583627813 2059407618335782421930215)
                      ·
                        rfl

theorem cell23_4010682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_4010682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010682 prefixEnd_4010682 := by exact prefixLift 4010682
  have htrace : WordTrace (prefixWord ++ tailWord_4010682) baseStart_4010682 baseEnd_4010682 := by
    simpa [prefixWord, tailWord_4010682, baseEnd_4010682] using wordTrace_append hprefix tailTrace_4010682
  have hstable : (prefixWord ++ tailWord_4010682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010682).length < 2 ^ (prefixWord ++ tailWord_4010682).sum := by decide
  have hdescent : baseEnd_4010682 < baseStart_4010682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010692 : List Nat := [2, 3, 3, 1, 1, 2, 11]
def baseStart_4010692 : Nat := 118140960795 + 4010692 * 2 ^ 59
def prefixEnd_4010692 : Nat := 4983230072969 + 3 ^ 40 * 4010692 * 2
def baseEnd_4010692 : Nat := 25424848804226263985249

theorem tailTrace_4010692 : CollatzResearch.WordTrace tailWord_4010692 prefixEnd_4010692 25424848804226263985249 := by
  unfold tailWord_4010692
  simp only [CollatzResearch.WordTrace]
  refine ⟨73140977392977665252665165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97521303190636887003553553 73140977392977665252665165)
  ·
    refine ⟨27427866522366624469749437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73140977392977665252665165 27427866522366624469749437)
    ·
      refine ⟨10285449945887484176156039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27427866522366624469749437 10285449945887484176156039)
      ·
        refine ⟨15428174918831226264234059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10285449945887484176156039 15428174918831226264234059)
        ·
          refine ⟨23142262378246839396351089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15428174918831226264234059 23142262378246839396351089)
          ·
            refine ⟨17356696783685129547263317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23142262378246839396351089 17356696783685129547263317)
            ·
              refine ⟨25424848804226263985249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17356696783685129547263317 25424848804226263985249)
              ·
                rfl

theorem cell23_4010692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 11].length) (baseStart_4010692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010692 prefixEnd_4010692 := by exact prefixLift 4010692
  have htrace : WordTrace (prefixWord ++ tailWord_4010692) baseStart_4010692 baseEnd_4010692 := by
    simpa [prefixWord, tailWord_4010692, baseEnd_4010692] using wordTrace_append hprefix tailTrace_4010692
  have hstable : (prefixWord ++ tailWord_4010692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010692).length < 2 ^ (prefixWord ++ tailWord_4010692).sum := by decide
  have hdescent : baseEnd_4010692 < baseStart_4010692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010723 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4010723 : Nat := 118140960795 + 4010723 * 2 ^ 59
def prefixEnd_4010723 : Nat := 4983230072969 + 3 ^ 40 * 4010723 * 2
def baseEnd_4010723 : Nat := 2059428671042616761517527

theorem tailTrace_4010723 : CollatzResearch.WordTrace tailWord_4010723 prefixEnd_4010723 2059428671042616761517527 := by
  unfold tailWord_4010723
  simp only [CollatzResearch.WordTrace]
  refine ⟨146283085448843022799708823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97522056965895348533139215 146283085448843022799708823)
  ·
    refine ⟨219424628173264534199563235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146283085448843022799708823 219424628173264534199563235)
    ·
      refine ⟨329136942259896801299344853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219424628173264534199563235 329136942259896801299344853)
      ·
        refine ⟨7714147084216331280453395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 329136942259896801299344853 7714147084216331280453395)
        ·
          refine ⟨11571220626324496920680093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7714147084216331280453395 11571220626324496920680093)
          ·
            refine ⟨4339207734871686345255035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11571220626324496920680093 4339207734871686345255035)
            ·
              refine ⟨6508811602307529517882553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339207734871686345255035 6508811602307529517882553)
              ·
                refine ⟨4881608701730647138411915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6508811602307529517882553 4881608701730647138411915)
                ·
                  refine ⟨7322413052595970707617873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881608701730647138411915 7322413052595970707617873)
                  ·
                    refine ⟨5491809789446978030713405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7322413052595970707617873 5491809789446978030713405)
                    ·
                      refine ⟨2059428671042616761517527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5491809789446978030713405 2059428671042616761517527)
                      ·
                        rfl

theorem cell23_4010723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4010723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010723 prefixEnd_4010723 := by exact prefixLift 4010723
  have htrace : WordTrace (prefixWord ++ tailWord_4010723) baseStart_4010723 baseEnd_4010723 := by
    simpa [prefixWord, tailWord_4010723, baseEnd_4010723] using wordTrace_append hprefix tailTrace_4010723
  have hstable : (prefixWord ++ tailWord_4010723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010723).length < 2 ^ (prefixWord ++ tailWord_4010723).sum := by decide
  have hdescent : baseEnd_4010723 < baseStart_4010723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010740 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4010740 : Nat := 118140960795 + 4010740 * 2 ^ 59
def prefixEnd_4010740 : Nat := 4983230072969 + 3 ^ 40 * 4010740 * 2
def baseEnd_4010740 : Nat := 2059437400213743195004949

theorem tailTrace_4010740 : CollatzResearch.WordTrace tailWord_4010740 prefixEnd_4010740 2059437400213743195004949 := by
  unfold tailWord_4010740
  simp only [CollatzResearch.WordTrace]
  refine ⟨73141852744890717351538837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97522470326520956468718449 73141852744890717351538837)
  ·
    refine ⟨3428524347416752375853383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73141852744890717351538837 3428524347416752375853383)
    ·
      refine ⟨5142786521125128563780075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3428524347416752375853383 5142786521125128563780075)
      ·
        refine ⟨7714179781687692845670113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142786521125128563780075 7714179781687692845670113)
        ·
          refine ⟨5785634836265769634252585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7714179781687692845670113 5785634836265769634252585)
          ·
            refine ⟨4339226127199327225689439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5785634836265769634252585 4339226127199327225689439)
            ·
              refine ⟨6508839190798990838534159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339226127199327225689439 6508839190798990838534159)
              ·
                refine ⟨9763258786198486257801239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6508839190798990838534159 9763258786198486257801239)
                ·
                  refine ⟨14644888179297729386701859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9763258786198486257801239 14644888179297729386701859)
                  ·
                    refine ⟨21967332268946594080052789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14644888179297729386701859 21967332268946594080052789)
                    ·
                      refine ⟨2059437400213743195004949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21967332268946594080052789 2059437400213743195004949)
                      ·
                        rfl

theorem cell23_4010740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4010740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010740 prefixEnd_4010740 := by exact prefixLift 4010740
  have htrace : WordTrace (prefixWord ++ tailWord_4010740) baseStart_4010740 baseEnd_4010740 := by
    simpa [prefixWord, tailWord_4010740, baseEnd_4010740] using wordTrace_append hprefix tailTrace_4010740
  have hstable : (prefixWord ++ tailWord_4010740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010740).length < 2 ^ (prefixWord ++ tailWord_4010740).sum := by decide
  have hdescent : baseEnd_4010740 < baseStart_4010740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010746 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2]
def baseStart_4010746 : Nat := 118140960795 + 4010746 * 2 ^ 59
def prefixEnd_4010746 : Nat := 4983230072969 + 3 ^ 40 * 4010746 * 2
def baseEnd_4010746 : Nat := 2059440481097670171529921

theorem tailTrace_4010746 : CollatzResearch.WordTrace tailWord_4010746 prefixEnd_4010746 2059440481097670171529921 := by
  unfold tailWord_4010746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36570981081939924431949023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97522616218506465151864061 36570981081939924431949023)
  ·
    refine ⟨54856471622909886647923535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36570981081939924431949023 54856471622909886647923535)
    ·
      refine ⟨82284707434364829971885303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54856471622909886647923535 82284707434364829971885303)
      ·
        refine ⟨123427061151547244957827955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82284707434364829971885303 123427061151547244957827955)
        ·
          refine ⟨185140591727320867436741933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123427061151547244957827955 185140591727320867436741933)
          ·
            refine ⟨69427721897745325288778225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185140591727320867436741933 69427721897745325288778225)
            ·
              refine ⟨52070791423308993966583669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69427721897745325288778225 52070791423308993966583669)
              ·
                refine ⟨4881636695935218184367219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52070791423308993966583669 4881636695935218184367219)
                ·
                  refine ⟨7322455043902827276550829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881636695935218184367219 7322455043902827276550829)
                  ·
                    refine ⟨2745920641463560228706561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7322455043902827276550829 2745920641463560228706561)
                    ·
                      refine ⟨2059440481097670171529921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745920641463560228706561 2059440481097670171529921)
                      ·
                        rfl

theorem cell23_4010746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_4010746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010746 prefixEnd_4010746 := by exact prefixLift 4010746
  have htrace : WordTrace (prefixWord ++ tailWord_4010746) baseStart_4010746 baseEnd_4010746 := by
    simpa [prefixWord, tailWord_4010746, baseEnd_4010746] using wordTrace_append hprefix tailTrace_4010746
  have hstable : (prefixWord ++ tailWord_4010746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010746).length < 2 ^ (prefixWord ++ tailWord_4010746).sum := by decide
  have hdescent : baseEnd_4010746 < baseStart_4010746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010754 : List Nat := [3, 4, 1, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_4010754 : Nat := 118140960795 + 4010754 * 2 ^ 59
def prefixEnd_4010754 : Nat := 4983230072969 + 3 ^ 40 * 4010754 * 2
def baseEnd_4010754 : Nat := 2059444588942906140229885

theorem tailTrace_4010754 : CollatzResearch.WordTrace tailWord_4010754 prefixEnd_4010754 2059444588942906140229885 := by
  unfold tailWord_4010754
  simp only [CollatzResearch.WordTrace]
  refine ⟨36571054027932678773521829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97522810741153810062724877 36571054027932678773521829)
  ·
    refine ⟨6857072630237377270035343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36571054027932678773521829 6857072630237377270035343)
    ·
      refine ⟨10285608945356065905053015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6857072630237377270035343 10285608945356065905053015)
      ·
        refine ⟨15428413418034098857579523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10285608945356065905053015 15428413418034098857579523)
        ·
          refine ⟨23142620127051148286369285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15428413418034098857579523 23142620127051148286369285)
          ·
            refine ⟨4339241273822090303694241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23142620127051148286369285 4339241273822090303694241)
            ·
              refine ⟨3254430955366567727770681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4339241273822090303694241 3254430955366567727770681)
              ·
                refine ⟨2440823216524925795828011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3254430955366567727770681 2440823216524925795828011)
                ·
                  refine ⟨3661234824787388693742017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440823216524925795828011 3661234824787388693742017)
                  ·
                    refine ⟨2745926118590541520306513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3661234824787388693742017 2745926118590541520306513)
                    ·
                      refine ⟨2059444588942906140229885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745926118590541520306513 2059444588942906140229885)
                      ·
                        rfl

theorem cell23_4010754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_4010754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010754 prefixEnd_4010754 := by exact prefixLift 4010754
  have htrace : WordTrace (prefixWord ++ tailWord_4010754) baseStart_4010754 baseEnd_4010754 := by
    simpa [prefixWord, tailWord_4010754, baseEnd_4010754] using wordTrace_append hprefix tailTrace_4010754
  have hstable : (prefixWord ++ tailWord_4010754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010754).length < 2 ^ (prefixWord ++ tailWord_4010754).sum := by decide
  have hdescent : baseEnd_4010754 < baseStart_4010754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010759 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4010759 : Nat := 118140960795 + 4010759 * 2 ^ 59
def prefixEnd_4010759 : Nat := 4983230072969 + 3 ^ 40 * 4010759 * 2
def baseEnd_4010759 : Nat := 2059447156346178620667361

theorem tailTrace_4010759 : CollatzResearch.WordTrace tailWord_4010759 prefixEnd_4010759 2059447156346178620667361 := by
  unfold tailWord_4010759
  simp only [CollatzResearch.WordTrace]
  refine ⟨146284398476712600948019331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97522932317808400632012887 146284398476712600948019331)
  ·
    refine ⟨219426597715068901422028997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146284398476712600948019331 219426597715068901422028997)
    ·
      refine ⟨41142487071575419016630437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219426597715068901422028997 41142487071575419016630437)
      ·
        refine ⟨7714216325920391065618207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41142487071575419016630437 7714216325920391065618207)
        ·
          refine ⟨11571324488880586598427311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7714216325920391065618207 11571324488880586598427311)
          ·
            refine ⟨17356986733320879897640967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11571324488880586598427311 17356986733320879897640967)
            ·
              refine ⟨26035480099981319846461451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17356986733320879897640967 26035480099981319846461451)
              ·
                refine ⟨39053220149971979769692177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26035480099981319846461451 39053220149971979769692177)
                ·
                  refine ⟨29289915112478984827269133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39053220149971979769692177 29289915112478984827269133)
                  ·
                    refine ⟨10983718167179619310225925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29289915112478984827269133 10983718167179619310225925)
                    ·
                      refine ⟨2059447156346178620667361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10983718167179619310225925 2059447156346178620667361)
                      ·
                        rfl

theorem cell23_4010759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4010759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010759 prefixEnd_4010759 := by exact prefixLift 4010759
  have htrace : WordTrace (prefixWord ++ tailWord_4010759) baseStart_4010759 baseEnd_4010759 := by
    simpa [prefixWord, tailWord_4010759, baseEnd_4010759] using wordTrace_append hprefix tailTrace_4010759
  have hstable : (prefixWord ++ tailWord_4010759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010759).length < 2 ^ (prefixWord ++ tailWord_4010759).sum := by decide
  have hdescent : baseEnd_4010759 < baseStart_4010759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010776 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 6, 2, 2]
def baseStart_4010776 : Nat := 118140960795 + 4010776 * 2 ^ 59
def prefixEnd_4010776 : Nat := 4983230072969 + 3 ^ 40 * 4010776 * 2
def baseEnd_4010776 : Nat := 2059455885517305054154783

theorem tailTrace_4010776 : CollatzResearch.WordTrace tailWord_4010776 prefixEnd_4010776 2059455885517305054154783 := by
  unfold tailWord_4010776
  simp only [CollatzResearch.WordTrace]
  refine ⟨73142509258825506425694091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97523345678434008567592121 73142509258825506425694091)
  ·
    refine ⟨109713763888238259638541137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73142509258825506425694091 109713763888238259638541137)
    ·
      refine ⟨82285322916178694728905853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109713763888238259638541137 82285322916178694728905853)
      ·
        refine ⟨30856996093567010523339695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82285322916178694728905853 30856996093567010523339695)
        ·
          refine ⟨46285494140350515785009543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30856996093567010523339695 46285494140350515785009543)
          ·
            refine ⟨69428241210525773677514315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46285494140350515785009543 69428241210525773677514315)
            ·
              refine ⟨104142361815788660516271473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69428241210525773677514315 104142361815788660516271473)
              ·
                refine ⟨78106771361841495387203605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104142361815788660516271473 78106771361841495387203605)
                ·
                  refine ⟨3661254907586320096275169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78106771361841495387203605 3661254907586320096275169)
                  ·
                    refine ⟨2745941180689740072206377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3661254907586320096275169 2745941180689740072206377)
                    ·
                      refine ⟨2059455885517305054154783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745941180689740072206377 2059455885517305054154783)
                      ·
                        rfl

theorem cell23_4010776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_4010776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010776 prefixEnd_4010776 := by exact prefixLift 4010776
  have htrace : WordTrace (prefixWord ++ tailWord_4010776) baseStart_4010776 baseEnd_4010776 := by
    simpa [prefixWord, tailWord_4010776, baseEnd_4010776] using wordTrace_append hprefix tailTrace_4010776
  have hstable : (prefixWord ++ tailWord_4010776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010776).length < 2 ^ (prefixWord ++ tailWord_4010776).sum := by decide
  have hdescent : baseEnd_4010776 < baseStart_4010776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010797 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4010797 : Nat := 118140960795 + 4010797 * 2 ^ 59
def prefixEnd_4010797 : Nat := 4983230072969 + 3 ^ 40 * 4010797 * 2
def baseEnd_4010797 : Nat := 2059466668611049471992187

theorem tailTrace_4010797 : CollatzResearch.WordTrace tailWord_4010797 prefixEnd_4010797 2059466668611049471992187 := by
  unfold tailWord_4010797
  simp only [CollatzResearch.WordTrace]
  refine ⟨146285784450574933437902645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97523856300383288958601763 146285784450574933437902645)
  ·
    refine ⟨13714292292241400009803373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146285784450574933437902645 13714292292241400009803373)
    ·
      refine ⟨5142859609590525003676265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13714292292241400009803373 5142859609590525003676265)
      ·
        refine ⟨3857144707192893752757199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5142859609590525003676265 3857144707192893752757199)
        ·
          refine ⟨5785717060789340629135799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857144707192893752757199 5785717060789340629135799)
          ·
            refine ⟨8678575591184010943703699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785717060789340629135799 8678575591184010943703699)
            ·
              refine ⟨13017863386776016415555549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678575591184010943703699 13017863386776016415555549)
              ·
                refine ⟨4881698770041006155833331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13017863386776016415555549 4881698770041006155833331)
                ·
                  refine ⟨7322548155061509233749997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881698770041006155833331 7322548155061509233749997)
                  ·
                    refine ⟨2745955558148065962656249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7322548155061509233749997 2745955558148065962656249)
                    ·
                      refine ⟨2059466668611049471992187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2745955558148065962656249 2059466668611049471992187)
                      ·
                        rfl

theorem cell23_4010797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4010797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010797 prefixEnd_4010797 := by exact prefixLift 4010797
  have htrace : WordTrace (prefixWord ++ tailWord_4010797) baseStart_4010797 baseEnd_4010797 := by
    simpa [prefixWord, tailWord_4010797, baseEnd_4010797] using wordTrace_append hprefix tailTrace_4010797
  have hstable : (prefixWord ++ tailWord_4010797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010797).length < 2 ^ (prefixWord ++ tailWord_4010797).sum := by decide
  have hdescent : baseEnd_4010797 < baseStart_4010797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010850 : List Nat := [3, 3, 2, 1, 3, 2, 1, 3, 5]
def baseStart_4010850 : Nat := 118140960795 + 4010850 * 2 ^ 59
def prefixEnd_4010850 : Nat := 4983230072969 + 3 ^ 40 * 4010850 * 2
def baseEnd_4010850 : Nat := 228832653676193084958827

theorem tailTrace_4010850 : CollatzResearch.WordTrace tailWord_4010850 prefixEnd_4010850 228832653676193084958827 := by
  unfold tailWord_4010850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36571929379845730872395501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97525145012921948993054669 36571929379845730872395501)
  ·
    refine ⟨13714473517442149077148313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36571929379845730872395501 13714473517442149077148313)
    ·
      refine ⟨10285855138081611807861235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13714473517442149077148313 10285855138081611807861235)
      ·
        refine ⟨15428782707122417711791853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10285855138081611807861235 15428782707122417711791853)
        ·
          refine ⟨5785793515170906641921945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15428782707122417711791853 5785793515170906641921945)
          ·
            refine ⟨4339345136378179981441459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5785793515170906641921945 4339345136378179981441459)
            ·
              refine ⟨6509017704567269972162189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339345136378179981441459 6509017704567269972162189)
              ·
                refine ⟨2440881639212726239560821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6509017704567269972162189 2440881639212726239560821)
                ·
                  refine ⟨228832653676193084958827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2440881639212726239560821 228832653676193084958827)
                  ·
                    rfl

theorem cell23_4010850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_4010850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010850 prefixEnd_4010850 := by exact prefixLift 4010850
  have htrace : WordTrace (prefixWord ++ tailWord_4010850) baseStart_4010850 baseEnd_4010850 := by
    simpa [prefixWord, tailWord_4010850, baseEnd_4010850] using wordTrace_append hprefix tailTrace_4010850
  have hstable : (prefixWord ++ tailWord_4010850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010850).length < 2 ^ (prefixWord ++ tailWord_4010850).sum := by decide
  have hdescent : baseEnd_4010850 < baseStart_4010850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010859 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 5, 4]
def baseStart_4010859 : Nat := 118140960795 + 4010859 * 2 ^ 59
def prefixEnd_4010859 : Nat := 4983230072969 + 3 ^ 40 * 4010859 * 2
def baseEnd_4010859 : Nat := 686499501470542743138967

theorem tailTrace_4010859 : CollatzResearch.WordTrace tailWord_4010859 prefixEnd_4010859 686499501470542743138967 := by
  unfold tailWord_4010859
  simp only [CollatzResearch.WordTrace]
  refine ⟨146288045776350318026659631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97525363850900212017773087 146288045776350318026659631)
  ·
    refine ⟨219432068664525477039989447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146288045776350318026659631 219432068664525477039989447)
    ·
      refine ⟨329148102996788215559984171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219432068664525477039989447 329148102996788215559984171)
      ·
        refine ⟨493722154495182323339976257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329148102996788215559984171 493722154495182323339976257)
        ·
          refine ⟨370291615871386742504982193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493722154495182323339976257 370291615871386742504982193)
          ·
            refine ⟨277718711903540056878736645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370291615871386742504982193 277718711903540056878736645)
            ·
              refine ⟨52072258481913760664763121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277718711903540056878736645 52072258481913760664763121)
              ·
                refine ⟨39054193861435320498572341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52072258481913760664763121 39054193861435320498572341)
                ·
                  refine ⟨3661330674509561296741157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39054193861435320498572341 3661330674509561296741157)
                  ·
                    refine ⟨686499501470542743138967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3661330674509561296741157 686499501470542743138967)
                    ·
                      rfl

theorem cell23_4010859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 4].length) (baseStart_4010859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010859 prefixEnd_4010859 := by exact prefixLift 4010859
  have htrace : WordTrace (prefixWord ++ tailWord_4010859) baseStart_4010859 baseEnd_4010859 := by
    simpa [prefixWord, tailWord_4010859, baseEnd_4010859] using wordTrace_append hprefix tailTrace_4010859
  have hstable : (prefixWord ++ tailWord_4010859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010859).length < 2 ^ (prefixWord ++ tailWord_4010859).sum := by decide
  have hdescent : baseEnd_4010859 < baseStart_4010859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010866 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_4010866 : Nat := 118140960795 + 4010866 * 2 ^ 59
def prefixEnd_4010866 : Nat := 4983230072969 + 3 ^ 40 * 4010866 * 2
def baseEnd_4010866 : Nat := 2059502098776209702029369

theorem tailTrace_4010866 : CollatzResearch.WordTrace tailWord_4010866 prefixEnd_4010866 2059502098776209702029369 := by
  unfold tailWord_4010866
  simp only [CollatzResearch.WordTrace]
  refine ⟨36572075271831239555541113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97525534058216638814776301 36572075271831239555541113)
  ·
    refine ⟨27429056453873429666655835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36572075271831239555541113 27429056453873429666655835)
    ·
      refine ⟨41143584680810144499983753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27429056453873429666655835 41143584680810144499983753)
      ·
        refine ⟨30857688510607608374987815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41143584680810144499983753 30857688510607608374987815)
        ·
          refine ⟨46286532765911412562481723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30857688510607608374987815 46286532765911412562481723)
          ·
            refine ⟨69429799148867118843722585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46286532765911412562481723 69429799148867118843722585)
            ·
              refine ⟨52072349361650339132791939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69429799148867118843722585 52072349361650339132791939)
              ·
                refine ⟨78108524042475508699187909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52072349361650339132791939 78108524042475508699187909)
                ·
                  refine ⟨14645348257964157881097733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78108524042475508699187909 14645348257964157881097733)
                  ·
                    refine ⟨2746002798368279602705825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14645348257964157881097733 2746002798368279602705825)
                    ·
                      refine ⟨2059502098776209702029369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746002798368279602705825 2059502098776209702029369)
                      ·
                        rfl

theorem cell23_4010866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_4010866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010866 prefixEnd_4010866 := by exact prefixLift 4010866
  have htrace : WordTrace (prefixWord ++ tailWord_4010866) baseStart_4010866 baseEnd_4010866 := by
    simpa [prefixWord, tailWord_4010866, baseEnd_4010866] using wordTrace_append hprefix tailTrace_4010866
  have hstable : (prefixWord ++ tailWord_4010866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010866).length < 2 ^ (prefixWord ++ tailWord_4010866).sum := by decide
  have hdescent : baseEnd_4010866 < baseStart_4010866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010933 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_4010933 : Nat := 118140960795 + 4010933 * 2 ^ 59
def prefixEnd_4010933 : Nat := 4983230072969 + 3 ^ 40 * 4010933 * 2
def baseEnd_4010933 : Nat := 2059536501980060939891561

theorem tailTrace_4010933 : CollatzResearch.WordTrace tailWord_4010933 prefixEnd_4010933 2059536501980060939891561 := by
  unfold tailWord_4010933
  simp only [CollatzResearch.WordTrace]
  refine ⟨146290744778082228664853453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97527163185388152443235635 146290744778082228664853453)
  ·
    refine ⟨54859029291780835749320045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146290744778082228664853453 54859029291780835749320045)
    ·
      refine ⟨20572135984417813405995017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54859029291780835749320045 20572135984417813405995017)
      ·
        refine ⟨15429101988313360054496263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20572135984417813405995017 15429101988313360054496263)
        ·
          refine ⟨23143652982470040081744395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15429101988313360054496263 23143652982470040081744395)
          ·
            refine ⟨34715479473705060122616593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23143652982470040081744395 34715479473705060122616593)
            ·
              refine ⟨26036609605278795091962445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34715479473705060122616593 26036609605278795091962445)
              ·
                refine ⟨9763728601979548159485917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26036609605278795091962445 9763728601979548159485917)
                ·
                  refine ⟨3661398225742330559807219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9763728601979548159485917 3661398225742330559807219)
                  ·
                    refine ⟨5492097338613495839710829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3661398225742330559807219 5492097338613495839710829)
                    ·
                      refine ⟨2059536501980060939891561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5492097338613495839710829 2059536501980060939891561)
                      ·
                        rfl

theorem cell23_4010933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_4010933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010933 prefixEnd_4010933 := by exact prefixLift 4010933
  have htrace : WordTrace (prefixWord ++ tailWord_4010933) baseStart_4010933 baseEnd_4010933 := by
    simpa [prefixWord, tailWord_4010933, baseEnd_4010933] using wordTrace_append hprefix tailTrace_4010933
  have hstable : (prefixWord ++ tailWord_4010933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010933).length < 2 ^ (prefixWord ++ tailWord_4010933).sum := by decide
  have hdescent : baseEnd_4010933 < baseStart_4010933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010934 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4010934 : Nat := 118140960795 + 4010934 * 2 ^ 59
def prefixEnd_4010934 : Nat := 4983230072969 + 3 ^ 40 * 4010934 * 2
def baseEnd_4010934 : Nat := 2059537015460715435979057

theorem tailTrace_4010934 : CollatzResearch.WordTrace tailWord_4010934 prefixEnd_4010934 2059537015460715435979057 := by
  unfold tailWord_4010934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143173828192412864727491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97527187500719070557093237 9143173828192412864727491)
  ·
    refine ⟨13714760742288619297091237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9143173828192412864727491 13714760742288619297091237)
    ·
      refine ⟨2571517639179116118204607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13714760742288619297091237 2571517639179116118204607)
      ·
        refine ⟨3857276458768674177306911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571517639179116118204607 3857276458768674177306911)
        ·
          refine ⟨5785914688153011265960367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857276458768674177306911 5785914688153011265960367)
          ·
            refine ⟨8678872032229516898940551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785914688153011265960367 8678872032229516898940551)
            ·
              refine ⟨13018308048344275348410827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678872032229516898940551 13018308048344275348410827)
              ·
                refine ⟨19527462072516413022616241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13018308048344275348410827 19527462072516413022616241)
                ·
                  refine ⟨14645596554387309766962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19527462072516413022616241 14645596554387309766962181)
                  ·
                    refine ⟨2746049353947620581305409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14645596554387309766962181 2746049353947620581305409)
                    ·
                      refine ⟨2059537015460715435979057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746049353947620581305409 2059537015460715435979057)
                      ·
                        rfl

theorem cell23_4010934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4010934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010934 prefixEnd_4010934 := by exact prefixLift 4010934
  have htrace : WordTrace (prefixWord ++ tailWord_4010934) baseStart_4010934 baseEnd_4010934 := by
    simpa [prefixWord, tailWord_4010934, baseEnd_4010934] using wordTrace_append hprefix tailTrace_4010934
  have hstable : (prefixWord ++ tailWord_4010934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010934).length < 2 ^ (prefixWord ++ tailWord_4010934).sum := by decide
  have hdescent : baseEnd_4010934 < baseStart_4010934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010956 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4010956 : Nat := 118140960795 + 4010956 * 2 ^ 59
def prefixEnd_4010956 : Nat := 4983230072969 + 3 ^ 40 * 4010956 * 2
def baseEnd_4010956 : Nat := 2059548312035114349903955

theorem tailTrace_4010956 : CollatzResearch.WordTrace tailWord_4010956 prefixEnd_4010956 2059548312035114349903955 := by
  unfold tailWord_4010956
  simp only [CollatzResearch.WordTrace]
  refine ⟨73145791828499451796470361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97527722437999269061960481 73145791828499451796470361)
  ·
    refine ⟨54859343871374588847352771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73145791828499451796470361 54859343871374588847352771)
    ·
      refine ⟨82289015807061883271029157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54859343871374588847352771 82289015807061883271029157)
      ·
        refine ⟨15429190463824103113317967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82289015807061883271029157 15429190463824103113317967)
        ·
          refine ⟨23143785695736154669976951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15429190463824103113317967 23143785695736154669976951)
          ·
            refine ⟨34715678543604232004965427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23143785695736154669976951 34715678543604232004965427)
            ·
              refine ⟨52073517815406348007448141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34715678543604232004965427 52073517815406348007448141)
              ·
                refine ⟨19527569180777380502793053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52073517815406348007448141 19527569180777380502793053)
                ·
                  refine ⟨7322838442791517688547395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19527569180777380502793053 7322838442791517688547395)
                  ·
                    refine ⟨10984257664187276532821093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7322838442791517688547395 10984257664187276532821093)
                    ·
                      refine ⟨2059548312035114349903955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10984257664187276532821093 2059548312035114349903955)
                      ·
                        rfl

theorem cell23_4010956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4010956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010956 prefixEnd_4010956 := by exact prefixLift 4010956
  have htrace : WordTrace (prefixWord ++ tailWord_4010956) baseStart_4010956 baseEnd_4010956 := by
    simpa [prefixWord, tailWord_4010956, baseEnd_4010956] using wordTrace_append hprefix tailTrace_4010956
  have hstable : (prefixWord ++ tailWord_4010956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010956).length < 2 ^ (prefixWord ++ tailWord_4010956).sum := by decide
  have hdescent : baseEnd_4010956 < baseStart_4010956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010970 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_4010970 : Nat := 118140960795 + 4010970 * 2 ^ 59
def prefixEnd_4010970 : Nat := 4983230072969 + 3 ^ 40 * 4010970 * 2
def baseEnd_4010970 : Nat := 686518500254759098376297

theorem tailTrace_4010970 : CollatzResearch.WordTrace tailWord_4010970 prefixEnd_4010970 686518500254759098376297 := by
  unfold tailWord_4010970
  simp only [CollatzResearch.WordTrace]
  refine ⟨36573023569737045995987591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97528062852632122655966909 36573023569737045995987591)
  ·
    refine ⟨54859535354605568993981387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36573023569737045995987591 54859535354605568993981387)
    ·
      refine ⟨82289303031908353490972081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54859535354605568993981387 82289303031908353490972081)
      ·
        refine ⟨61716977273931265118229061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82289303031908353490972081 61716977273931265118229061)
        ·
          refine ⟨11571933238862112209667949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61716977273931265118229061 11571933238862112209667949)
          ·
            refine ⟨4339474964573292078625481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11571933238862112209667949 4339474964573292078625481)
            ·
              refine ⟨3254606223429969058969111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4339474964573292078625481 3254606223429969058969111)
              ·
                refine ⟨4881909335144953588453667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254606223429969058969111 4881909335144953588453667)
                ·
                  refine ⟨7322864002717430382680501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881909335144953588453667 7322864002717430382680501)
                  ·
                    refine ⟨686518500254759098376297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7322864002717430382680501 686518500254759098376297)
                    ·
                      rfl

theorem cell23_4010970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_4010970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010970 prefixEnd_4010970 := by exact prefixLift 4010970
  have htrace : WordTrace (prefixWord ++ tailWord_4010970) baseStart_4010970 baseEnd_4010970 := by
    simpa [prefixWord, tailWord_4010970, baseEnd_4010970] using wordTrace_append hprefix tailTrace_4010970
  have hstable : (prefixWord ++ tailWord_4010970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010970).length < 2 ^ (prefixWord ++ tailWord_4010970).sum := by decide
  have hdescent : baseEnd_4010970 < baseStart_4010970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010979 : List Nat := [1, 1, 1, 6, 1, 1, 12]
def baseStart_4010979 : Nat := 118140960795 + 4010979 * 2 ^ 59
def prefixEnd_4010979 : Nat := 4983230072969 + 3 ^ 40 * 4010979 * 2
def baseEnd_4010979 : Nat := 25426668173952688394029

theorem tailTrace_4010979 : CollatzResearch.WordTrace tailWord_4010979 prefixEnd_4010979 25426668173952688394029 := by
  unfold tailWord_4010979
  simp only [CollatzResearch.WordTrace]
  refine ⟨146292422535915578521027991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97528281690610385680685327 146292422535915578521027991)
  ·
    refine ⟨219438633803873367781541987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146292422535915578521027991 219438633803873367781541987)
    ·
      refine ⟨329157950705810051672312981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219438633803873367781541987 329157950705810051672312981)
      ·
        refine ⟨15429278939334846172139671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 329157950705810051672312981 15429278939334846172139671)
        ·
          refine ⟨23143918409002269258209507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15429278939334846172139671 23143918409002269258209507)
          ·
            refine ⟨34715877613503403887314261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23143918409002269258209507 34715877613503403887314261)
            ·
              refine ⟨25426668173952688394029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34715877613503403887314261 25426668173952688394029)
              ·
                rfl

theorem cell23_4010979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 12].length) (baseStart_4010979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010979 prefixEnd_4010979 := by exact prefixLift 4010979
  have htrace : WordTrace (prefixWord ++ tailWord_4010979) baseStart_4010979 baseEnd_4010979 := by
    simpa [prefixWord, tailWord_4010979, baseEnd_4010979] using wordTrace_append hprefix tailTrace_4010979
  have hstable : (prefixWord ++ tailWord_4010979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010979).length < 2 ^ (prefixWord ++ tailWord_4010979).sum := by decide
  have hdescent : baseEnd_4010979 < baseStart_4010979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010983 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 4, 4]
def baseStart_4010983 : Nat := 118140960795 + 4010983 * 2 ^ 59
def prefixEnd_4010983 : Nat := 4983230072969 + 3 ^ 40 * 4010983 * 2
def baseEnd_4010983 : Nat := 686520725337595248088777

theorem tailTrace_4010983 : CollatzResearch.WordTrace tailWord_4010983 prefixEnd_4010983 686520725337595248088777 := by
  unfold tailWord_4010983
  simp only [CollatzResearch.WordTrace]
  refine ⟨146292568427901087204173603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97528378951934058136115735 146292568427901087204173603)
  ·
    refine ⟨219438852641851630806260405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146292568427901087204173603 219438852641851630806260405)
    ·
      refine ⟨20572392435173590388086913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219438852641851630806260405 20572392435173590388086913)
      ·
        refine ⟨15429294326380192791065185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20572392435173590388086913 15429294326380192791065185)
        ·
          refine ⟨11571970744785144593298889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15429294326380192791065185 11571970744785144593298889)
          ·
            refine ⟨8678978058588858444974167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11571970744785144593298889 8678978058588858444974167)
            ·
              refine ⟨13018467087883287667461251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678978058588858444974167 13018467087883287667461251)
              ·
                refine ⟨19527700631824931501191877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13018467087883287667461251 19527700631824931501191877)
                ·
                  refine ⟨3661443868467174656473477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19527700631824931501191877 3661443868467174656473477)
                  ·
                    refine ⟨686520725337595248088777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3661443868467174656473477 686520725337595248088777)
                    ·
                      rfl

theorem cell23_4010983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_4010983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4010983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4010983 prefixEnd_4010983 := by exact prefixLift 4010983
  have htrace : WordTrace (prefixWord ++ tailWord_4010983) baseStart_4010983 baseEnd_4010983 := by
    simpa [prefixWord, tailWord_4010983, baseEnd_4010983] using wordTrace_append hprefix tailTrace_4010983
  have hstable : (prefixWord ++ tailWord_4010983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010983).length < 2 ^ (prefixWord ++ tailWord_4010983).sum := by decide
  have hdescent : baseEnd_4010983 < baseStart_4010983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011063 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 1, 4, 2]
def baseStart_4011063 : Nat := 118140960795 + 4011063 * 2 ^ 59
def prefixEnd_4011063 : Nat := 4983230072969 + 3 ^ 40 * 4011063 * 2
def baseEnd_4011063 : Nat := 2059603254465145431265963

theorem tailTrace_4011063 : CollatzResearch.WordTrace tailWord_4011063 prefixEnd_4011063 2059603254465145431265963 := by
  unfold tailWord_4011063
  simp only [CollatzResearch.WordTrace]
  refine ⟨146295486267611260867085843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97530324178407507244723895 146295486267611260867085843)
  ·
    refine ⟨219443229401416891300628765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146295486267611260867085843 219443229401416891300628765)
    ·
      refine ⟨82291211025531334237735787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219443229401416891300628765 82291211025531334237735787)
      ·
        refine ⟨123436816538297001356603681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82291211025531334237735787 123436816538297001356603681)
        ·
          refine ⟨92577612403722751017452761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123436816538297001356603681 92577612403722751017452761)
          ·
            refine ⟨69433209302792063263089571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92577612403722751017452761 69433209302792063263089571)
            ·
              refine ⟨104149813954188094894634357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69433209302792063263089571 104149813954188094894634357)
              ·
                refine ⟨9764045058205133896371971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104149813954188094894634357 9764045058205133896371971)
                ·
                  refine ⟨14646067587307700844557957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764045058205133896371971 14646067587307700844557957)
                  ·
                    refine ⟨2746137672620193908354617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14646067587307700844557957 2746137672620193908354617)
                    ·
                      refine ⟨2059603254465145431265963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746137672620193908354617 2059603254465145431265963)
                      ·
                        rfl

theorem cell23_4011063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_4011063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011063 prefixEnd_4011063 := by exact prefixLift 4011063
  have htrace : WordTrace (prefixWord ++ tailWord_4011063) baseStart_4011063 baseEnd_4011063 := by
    simpa [prefixWord, tailWord_4011063, baseEnd_4011063] using wordTrace_append hprefix tailTrace_4011063
  have hstable : (prefixWord ++ tailWord_4011063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011063).length < 2 ^ (prefixWord ++ tailWord_4011063).sum := by decide
  have hdescent : baseEnd_4011063 < baseStart_4011063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011066 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_4011066 : Nat := 118140960795 + 4011066 * 2 ^ 59
def prefixEnd_4011066 : Nat := 4983230072969 + 3 ^ 40 * 4011066 * 2
def baseEnd_4011066 : Nat := 2059604794907108919528449

theorem tailTrace_4011066 : CollatzResearch.WordTrace tailWord_4011066 prefixEnd_4011066 2059604794907108919528449 := by
  unfold tailWord_4011066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36573898921650098094861263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97530397124400261586296701 36573898921650098094861263)
  ·
    refine ⟨54860848382475147142291895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36573898921650098094861263 54860848382475147142291895)
    ·
      refine ⟨82291272573712720713437843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54860848382475147142291895 82291272573712720713437843)
      ·
        refine ⟨123436908860569081070156765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82291272573712720713437843 123436908860569081070156765)
        ·
          refine ⟨46288840822713405401308787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123436908860569081070156765 46288840822713405401308787)
          ·
            refine ⟨69433261234070108101963181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46288840822713405401308787 69433261234070108101963181)
            ·
              refine ⟨26037472962776290538236193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69433261234070108101963181 26037472962776290538236193)
              ·
                refine ⟨19528104722082217903677145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26037472962776290538236193 19528104722082217903677145)
                ·
                  refine ⟨14646078541561663427757859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19528104722082217903677145 14646078541561663427757859)
                  ·
                    refine ⟨21969117812342495141636789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14646078541561663427757859 21969117812342495141636789)
                    ·
                      refine ⟨2059604794907108919528449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21969117812342495141636789 2059604794907108919528449)
                      ·
                        rfl

theorem cell23_4011066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_4011066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011066 prefixEnd_4011066 := by exact prefixLift 4011066
  have htrace : WordTrace (prefixWord ++ tailWord_4011066) baseStart_4011066 baseEnd_4011066 := by
    simpa [prefixWord, tailWord_4011066, baseEnd_4011066] using wordTrace_append hprefix tailTrace_4011066
  have hstable : (prefixWord ++ tailWord_4011066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011066).length < 2 ^ (prefixWord ++ tailWord_4011066).sum := by decide
  have hdescent : baseEnd_4011066 < baseStart_4011066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011103 : List Nat := [1, 1, 2, 3, 1, 1, 5, 4, 5]
def baseStart_4011103 : Nat := 118140960795 + 4011103 * 2 ^ 59
def prefixEnd_4011103 : Nat := 4983230072969 + 3 ^ 40 * 4011103 * 2
def baseEnd_4011103 : Nat := 228847088187925030529531

theorem tailTrace_4011103 : CollatzResearch.WordTrace tailWord_4011103 prefixEnd_4011103 228847088187925030529531 := by
  unfold tailWord_4011103
  simp only [CollatzResearch.WordTrace]
  refine ⟨146296945187466347698541963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97531296791644231799027975 146296945187466347698541963)
  ·
    refine ⟨219445417781199521547812945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146296945187466347698541963 219445417781199521547812945)
    ·
      refine ⟨164584063335899641160859709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219445417781199521547812945 164584063335899641160859709)
      ·
        refine ⟨61719023750962365435322391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164584063335899641160859709 61719023750962365435322391)
        ·
          refine ⟨92578535626443548152983587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61719023750962365435322391 92578535626443548152983587)
          ·
            refine ⟨138867803439665322229475381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92578535626443548152983587 138867803439665322229475381)
            ·
              refine ⟨13018856572468623959013317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138867803439665322229475381 13018856572468623959013317)
              ·
                refine ⟨2441035607337866992314997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13018856572468623959013317 2441035607337866992314997)
                ·
                  refine ⟨228847088187925030529531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2441035607337866992314997 228847088187925030529531)
                  ·
                    rfl

theorem cell23_4011103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 5].length) (baseStart_4011103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011103 prefixEnd_4011103 := by exact prefixLift 4011103
  have htrace : WordTrace (prefixWord ++ tailWord_4011103) baseStart_4011103 baseEnd_4011103 := by
    simpa [prefixWord, tailWord_4011103, baseEnd_4011103] using wordTrace_append hprefix tailTrace_4011103
  have hstable : (prefixWord ++ tailWord_4011103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011103).length < 2 ^ (prefixWord ++ tailWord_4011103).sum := by decide
  have hdescent : baseEnd_4011103 < baseStart_4011103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011113 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 3]
def baseStart_4011113 : Nat := 118140960795 + 4011113 * 2 ^ 59
def prefixEnd_4011113 : Nat := 4983230072969 + 3 ^ 40 * 4011113 * 2
def baseEnd_4011113 : Nat := 2059628928497870235640733

theorem tailTrace_4011113 : CollatzResearch.WordTrace tailWord_4011113 prefixEnd_4011113 2059628928497870235640733 := by
  unfold tailWord_4011113
  simp only [CollatzResearch.WordTrace]
  refine ⟨146297309917430119406405993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97531539944953412937603995 146297309917430119406405993)
  ·
    refine ⟨109722982438072589554804495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146297309917430119406405993 109722982438072589554804495)
    ·
      refine ⟨164584473657108884332206743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109722982438072589554804495 164584473657108884332206743)
      ·
        refine ⟨246876710485663326498310115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164584473657108884332206743 246876710485663326498310115)
        ·
          refine ⟨370315065728494989747465173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246876710485663326498310115 370315065728494989747465173)
          ·
            refine ⟨8679259353011601322206215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 370315065728494989747465173 8679259353011601322206215)
            ·
              refine ⟨13018889029517401983309323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8679259353011601322206215 13018889029517401983309323)
              ·
                refine ⟨19528333544276102974963985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13018889029517401983309323 19528333544276102974963985)
                ·
                  refine ⟨14646250158207077231222989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19528333544276102974963985 14646250158207077231222989)
                  ·
                    refine ⟨5492343809327653961708621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14646250158207077231222989 5492343809327653961708621)
                    ·
                      refine ⟨2059628928497870235640733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5492343809327653961708621 2059628928497870235640733)
                      ·
                        rfl

theorem cell23_4011113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_4011113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011113 prefixEnd_4011113 := by exact prefixLift 4011113
  have htrace : WordTrace (prefixWord ++ tailWord_4011113) baseStart_4011113 baseEnd_4011113 := by
    simpa [prefixWord, tailWord_4011113, baseEnd_4011113] using wordTrace_append hprefix tailTrace_4011113
  have hstable : (prefixWord ++ tailWord_4011113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011113).length < 2 ^ (prefixWord ++ tailWord_4011113).sum := by decide
  have hdescent : baseEnd_4011113 < baseStart_4011113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011116 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_4011116 : Nat := 118140960795 + 4011116 * 2 ^ 59
def prefixEnd_4011116 : Nat := 4983230072969 + 3 ^ 40 * 4011116 * 2
def baseEnd_4011116 : Nat := 686543489646611241301073

theorem tailTrace_4011116 : CollatzResearch.WordTrace tailWord_4011116 prefixEnd_4011116 686543489646611241301073 := by
  unfold tailWord_4011116
  simp only [CollatzResearch.WordTrace]
  refine ⟨73148709668209625459382601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97531612890946167279176801 73148709668209625459382601)
  ·
    refine ⟨54861532251157219094536951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73148709668209625459382601 54861532251157219094536951)
    ·
      refine ⟨82292298376735828641805427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54861532251157219094536951 82292298376735828641805427)
      ·
        refine ⟨123438447565103742962708141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82292298376735828641805427 123438447565103742962708141)
        ·
          refine ⟨46289417836913903611015553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123438447565103742962708141 46289417836913903611015553)
          ·
            refine ⟨34717063377685427708261665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46289417836913903611015553 34717063377685427708261665)
            ·
              refine ⟨26037797533264070781196249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34717063377685427708261665 26037797533264070781196249)
              ·
                refine ⟨19528348149948053085897187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26037797533264070781196249 19528348149948053085897187)
                ·
                  refine ⟨29292522224922079628845781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19528348149948053085897187 29292522224922079628845781)
                  ·
                    refine ⟨686543489646611241301073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29292522224922079628845781 686543489646611241301073)
                    ·
                      rfl

theorem cell23_4011116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_4011116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011116 prefixEnd_4011116 := by exact prefixLift 4011116
  have htrace : WordTrace (prefixWord ++ tailWord_4011116) baseStart_4011116 baseEnd_4011116 := by
    simpa [prefixWord, tailWord_4011116, baseEnd_4011116] using wordTrace_append hprefix tailTrace_4011116
  have hstable : (prefixWord ++ tailWord_4011116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011116).length < 2 ^ (prefixWord ++ tailWord_4011116).sum := by decide
  have hdescent : baseEnd_4011116 < baseStart_4011116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011173 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_4011173 : Nat := 118140960795 + 4011173 * 2 ^ 59
def prefixEnd_4011173 : Nat := 4983230072969 + 3 ^ 40 * 4011173 * 2
def baseEnd_4011173 : Nat := 2059659737337140000890457

theorem tailTrace_4011173 : CollatzResearch.WordTrace tailWord_4011173 prefixEnd_4011173 2059659737337140000890457 := by
  unfold tailWord_4011173
  simp only [CollatzResearch.WordTrace]
  refine ⟨146299498297212749653590173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97532998864808499769060115 146299498297212749653590173)
  ·
    refine ⟨54862311861454781120096315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146299498297212749653590173 54862311861454781120096315)
    ·
      refine ⟨82293467792182171680144473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54862311861454781120096315 82293467792182171680144473)
      ·
        refine ⟨61720100844136628760108355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82293467792182171680144473 61720100844136628760108355)
        ·
          refine ⟨92580151266204943140162533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61720100844136628760108355 92580151266204943140162533)
          ·
            refine ⟨17358778362413426838780475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92580151266204943140162533 17358778362413426838780475)
            ·
              refine ⟨26038167543620140258170713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17358778362413426838780475 26038167543620140258170713)
              ·
                refine ⟨19528625657715105193628035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26038167543620140258170713 19528625657715105193628035)
                ·
                  refine ⟨29292938486572657790442053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19528625657715105193628035 29292938486572657790442053)
                  ·
                    refine ⟨5492425966232373335707885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29292938486572657790442053 5492425966232373335707885)
                    ·
                      refine ⟨2059659737337140000890457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5492425966232373335707885 2059659737337140000890457)
                      ·
                        rfl

theorem cell23_4011173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_4011173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011173 prefixEnd_4011173 := by exact prefixLift 4011173
  have htrace : WordTrace (prefixWord ++ tailWord_4011173) baseStart_4011173 baseEnd_4011173 := by
    simpa [prefixWord, tailWord_4011173, baseEnd_4011173] using wordTrace_append hprefix tailTrace_4011173
  have hstable : (prefixWord ++ tailWord_4011173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011173).length < 2 ^ (prefixWord ++ tailWord_4011173).sum := by decide
  have hdescent : baseEnd_4011173 < baseStart_4011173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011197 : List Nat := [1, 4, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_4011197 : Nat := 118140960795 + 4011197 * 2 ^ 59
def prefixEnd_4011197 : Nat := 4983230072969 + 3 ^ 40 * 4011197 * 2
def baseEnd_4011197 : Nat := 686557353624282635663449

theorem tailTrace_4011197 : CollatzResearch.WordTrace tailWord_4011197 prefixEnd_4011197 686557353624282635663449 := by
  unfold tailWord_4011197
  simp only [CollatzResearch.WordTrace]
  refine ⟨146300373649125801752463845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97533582432750534501642563 146300373649125801752463845)
  ·
    refine ⟨27431320059211087828586971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146300373649125801752463845 27431320059211087828586971)
    ·
      refine ⟨41146980088816631742880457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27431320059211087828586971 41146980088816631742880457)
      ·
        refine ⟨30860235066612473807160343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41146980088816631742880457 30860235066612473807160343)
        ·
          refine ⟨46290352599918710710740515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30860235066612473807160343 46290352599918710710740515)
          ·
            refine ⟨69435528899878066066110773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46290352599918710710740515 69435528899878066066110773)
            ·
              refine ⟨6509580834363568693697885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69435528899878066066110773 6509580834363568693697885)
              ·
                refine ⟨2441092812886338260136707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6509580834363568693697885 2441092812886338260136707)
                ·
                  refine ⟨3661639219329507390205061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441092812886338260136707 3661639219329507390205061)
                  ·
                    refine ⟨686557353624282635663449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3661639219329507390205061 686557353624282635663449)
                    ·
                      rfl

theorem cell23_4011197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_4011197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011197 prefixEnd_4011197 := by exact prefixLift 4011197
  have htrace : WordTrace (prefixWord ++ tailWord_4011197) baseStart_4011197 baseEnd_4011197 := by
    simpa [prefixWord, tailWord_4011197, baseEnd_4011197] using wordTrace_append hprefix tailTrace_4011197
  have hstable : (prefixWord ++ tailWord_4011197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011197).length < 2 ^ (prefixWord ++ tailWord_4011197).sum := by decide
  have hdescent : baseEnd_4011197 < baseStart_4011197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011214 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_4011214 : Nat := 118140960795 + 4011214 * 2 ^ 59
def prefixEnd_4011214 : Nat := 4983230072969 + 3 ^ 40 * 4011214 * 2
def baseEnd_4011214 : Nat := 686560263347991446825923

theorem tailTrace_4011214 : CollatzResearch.WordTrace tailWord_4011214 prefixEnd_4011214 686560263347991446825923 := by
  unfold tailWord_4011214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18287624211258026706979087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97533995793376142437221797 18287624211258026706979087)
  ·
    refine ⟨27431436316887040060468631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18287624211258026706979087 27431436316887040060468631)
    ·
      refine ⟨41147154475330560090702947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27431436316887040060468631 41147154475330560090702947)
      ·
        refine ⟨61720731712995840136054421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41147154475330560090702947 61720731712995840136054421)
        ·
          refine ⟨2893159299046680006377551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61720731712995840136054421 2893159299046680006377551)
          ·
            refine ⟨4339738948570020009566327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893159299046680006377551 4339738948570020009566327)
            ·
              refine ⟨6509608422855030014349491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339738948570020009566327 6509608422855030014349491)
              ·
                refine ⟨9764412634282545021524237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6509608422855030014349491 9764412634282545021524237)
                ·
                  refine ⟨3661654737855954383071589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9764412634282545021524237 3661654737855954383071589)
                  ·
                    refine ⟨686560263347991446825923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3661654737855954383071589 686560263347991446825923)
                    ·
                      rfl

theorem cell23_4011214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_4011214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011214 prefixEnd_4011214 := by exact prefixLift 4011214
  have htrace : WordTrace (prefixWord ++ tailWord_4011214) baseStart_4011214 baseEnd_4011214 := by
    simpa [prefixWord, tailWord_4011214, baseEnd_4011214] using wordTrace_append hprefix tailTrace_4011214
  have hstable : (prefixWord ++ tailWord_4011214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011214).length < 2 ^ (prefixWord ++ tailWord_4011214).sum := by decide
  have hdescent : baseEnd_4011214 < baseStart_4011214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011254 : List Nat := [5, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_4011254 : Nat := 118140960795 + 4011254 * 2 ^ 59
def prefixEnd_4011254 : Nat := 4983230072969 + 3 ^ 40 * 4011254 * 2
def baseEnd_4011254 : Nat := 2059701329270154183977585

theorem tailTrace_4011254 : CollatzResearch.WordTrace tailWord_4011254 prefixEnd_4011254 2059701329270154183977585 := by
  unfold tailWord_4011254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143903288119956280455551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97534968406612866991525877 9143903288119956280455551)
  ·
    refine ⟨13715854932179934420683327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9143903288119956280455551 13715854932179934420683327)
    ·
      refine ⟨20573782398269901631024991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13715854932179934420683327 20573782398269901631024991)
      ·
        refine ⟨30860673597404852446537487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20573782398269901631024991 30860673597404852446537487)
        ·
          refine ⟨46291010396107278669806231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30860673597404852446537487 46291010396107278669806231)
          ·
            refine ⟨69436515594160918004709347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46291010396107278669806231 69436515594160918004709347)
            ·
              refine ⟨104154773391241377007064021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69436515594160918004709347 104154773391241377007064021)
              ·
                refine ⟨2441127501357219773603063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104154773391241377007064021 2441127501357219773603063)
                ·
                  refine ⟨3661691252035829660404595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441127501357219773603063 3661691252035829660404595)
                  ·
                    refine ⟨5492536878053744490606893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3661691252035829660404595 5492536878053744490606893)
                    ·
                      refine ⟨2059701329270154183977585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5492536878053744490606893 2059701329270154183977585)
                      ·
                        rfl

theorem cell23_4011254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_4011254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011254 prefixEnd_4011254 := by exact prefixLift 4011254
  have htrace : WordTrace (prefixWord ++ tailWord_4011254) baseStart_4011254 baseEnd_4011254 := by
    simpa [prefixWord, tailWord_4011254, baseEnd_4011254] using wordTrace_append hprefix tailTrace_4011254
  have hstable : (prefixWord ++ tailWord_4011254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011254).length < 2 ^ (prefixWord ++ tailWord_4011254).sum := by decide
  have hdescent : baseEnd_4011254 < baseStart_4011254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011273 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_4011273 : Nat := 118140960795 + 4011273 * 2 ^ 59
def prefixEnd_4011273 : Nat := 4983230072969 + 3 ^ 40 * 4011273 * 2
def baseEnd_4011273 : Nat := 2059711085402589609639997

theorem tailTrace_4011273 : CollatzResearch.WordTrace tailWord_4011273 prefixEnd_4011273 2059711085402589609639997 := by
  unfold tailWord_4011273
  simp only [CollatzResearch.WordTrace]
  refine ⟨146303145596850466732230473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97535430397900311154820315 146303145596850466732230473)
  ·
    refine ⟨109727359197637850049172855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146303145596850466732230473 109727359197637850049172855)
    ·
      refine ⟨164591038796456775073759283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109727359197637850049172855 164591038796456775073759283)
      ·
        refine ⟨246886558194685162610638925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164591038796456775073759283 246886558194685162610638925)
        ·
          refine ⟨92582459323006935978989597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246886558194685162610638925 92582459323006935978989597)
          ·
            refine ⟨34718422246127600992121099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92582459323006935978989597 34718422246127600992121099)
            ·
              refine ⟨52077633369191401488181649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34718422246127600992121099 52077633369191401488181649)
              ·
                refine ⟨39058225026893551116136237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52077633369191401488181649 39058225026893551116136237)
                ·
                  refine ⟨14646834385085081668551089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39058225026893551116136237 14646834385085081668551089)
                  ·
                    refine ⟨10985125788813811251413317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14646834385085081668551089 10985125788813811251413317)
                    ·
                      refine ⟨2059711085402589609639997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10985125788813811251413317 2059711085402589609639997)
                      ·
                        rfl

theorem cell23_4011273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_4011273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011273 prefixEnd_4011273 := by exact prefixLift 4011273
  have htrace : WordTrace (prefixWord ++ tailWord_4011273) baseStart_4011273 baseEnd_4011273 := by
    simpa [prefixWord, tailWord_4011273, baseEnd_4011273] using wordTrace_append hprefix tailTrace_4011273
  have hstable : (prefixWord ++ tailWord_4011273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011273).length < 2 ^ (prefixWord ++ tailWord_4011273).sum := by decide
  have hdescent : baseEnd_4011273 < baseStart_4011273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011290 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_4011290 : Nat := 118140960795 + 4011290 * 2 ^ 59
def prefixEnd_4011290 : Nat := 4983230072969 + 3 ^ 40 * 4011290 * 2
def baseEnd_4011290 : Nat := 2059719814573716043127419

theorem tailTrace_4011290 : CollatzResearch.WordTrace tailWord_4011290 prefixEnd_4011290 2059719814573716043127419 := by
  unfold tailWord_4011290
  simp only [CollatzResearch.WordTrace]
  refine ⟨36575941409447219658899831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97535843758525919090399549 36575941409447219658899831)
  ·
    refine ⟨54863912114170829488349747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36575941409447219658899831 54863912114170829488349747)
    ·
      refine ⟨82295868171256244232524621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54863912114170829488349747 82295868171256244232524621)
      ·
        refine ⟨30860950564221091587196733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82295868171256244232524621 30860950564221091587196733)
        ·
          refine ⟨11572856461582909345198775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30860950564221091587196733 11572856461582909345198775)
          ·
            refine ⟨17359284692374364017798163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11572856461582909345198775 17359284692374364017798163)
            ·
              refine ⟨26038927038561546026697245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17359284692374364017798163 26038927038561546026697245)
              ·
                refine ⟨9764597639460579760011467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26038927038561546026697245 9764597639460579760011467)
                ·
                  refine ⟨14646896459190869640017201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764597639460579760011467 14646896459190869640017201)
                  ·
                    refine ⟨10985172344393152230012901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14646896459190869640017201 10985172344393152230012901)
                    ·
                      refine ⟨2059719814573716043127419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10985172344393152230012901 2059719814573716043127419)
                      ·
                        rfl

theorem cell23_4011290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_4011290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011290 prefixEnd_4011290 := by exact prefixLift 4011290
  have htrace : WordTrace (prefixWord ++ tailWord_4011290) baseStart_4011290 baseEnd_4011290 := by
    simpa [prefixWord, tailWord_4011290, baseEnd_4011290] using wordTrace_append hprefix tailTrace_4011290
  have hstable : (prefixWord ++ tailWord_4011290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011290).length < 2 ^ (prefixWord ++ tailWord_4011290).sum := by decide
  have hdescent : baseEnd_4011290 < baseStart_4011290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011300 : List Nat := [2, 3, 1, 3, 1, 1, 5, 7]
def baseStart_4011300 : Nat := 118140960795 + 4011300 * 2 ^ 59
def prefixEnd_4011300 : Nat := 4983230072969 + 3 ^ 40 * 4011300 * 2
def baseEnd_4011300 : Nat := 76286109236305963111199

theorem tailTrace_4011300 : CollatzResearch.WordTrace tailWord_4011300 prefixEnd_4011300 76286109236305963111199 := by
  unfold tailWord_4011300
  simp only [CollatzResearch.WordTrace]
  refine ⟨73152065183876325171731677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97536086911835100228975569 73152065183876325171731677)
  ·
    refine ⟨27432024443953621939399379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73152065183876325171731677 27432024443953621939399379)
    ·
      refine ⟨41148036665930432909099069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27432024443953621939399379 41148036665930432909099069)
      ·
        refine ⟨15430513749723912340912151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41148036665930432909099069 15430513749723912340912151)
        ·
          refine ⟨23145770624585868511368227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15430513749723912340912151 23145770624585868511368227)
          ·
            refine ⟨34718655936878802767052341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23145770624585868511368227 34718655936878802767052341)
            ·
              refine ⟨3254873994082387759411157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34718655936878802767052341 3254873994082387759411157)
              ·
                refine ⟨76286109236305963111199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3254873994082387759411157 76286109236305963111199)
                ·
                  rfl

theorem cell23_4011300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 7].length) (baseStart_4011300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011300 prefixEnd_4011300 := by exact prefixLift 4011300
  have htrace : WordTrace (prefixWord ++ tailWord_4011300) baseStart_4011300 baseEnd_4011300 := by
    simpa [prefixWord, tailWord_4011300, baseEnd_4011300] using wordTrace_append hprefix tailTrace_4011300
  have hstable : (prefixWord ++ tailWord_4011300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011300).length < 2 ^ (prefixWord ++ tailWord_4011300).sum := by decide
  have hdescent : baseEnd_4011300 < baseStart_4011300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011314 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_4011314 : Nat := 118140960795 + 4011314 * 2 ^ 59
def prefixEnd_4011314 : Nat := 4983230072969 + 3 ^ 40 * 4011314 * 2
def baseEnd_4011314 : Nat := 2059732138109423949227309

theorem tailTrace_4011314 : CollatzResearch.WordTrace tailWord_4011314 prefixEnd_4011314 2059732138109423949227309 := by
  unfold tailWord_4011314
  simp only [CollatzResearch.WordTrace]
  refine ⟨36576160247425482683618249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97536427326467953822981997 36576160247425482683618249)
  ·
    refine ⟨27432120185569112012713687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36576160247425482683618249 27432120185569112012713687)
    ·
      refine ⟨41148180278353668019070531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27432120185569112012713687 41148180278353668019070531)
      ·
        refine ⟨61722270417530502028605797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41148180278353668019070531 61722270417530502028605797)
        ·
          refine ⟨11572925703286969130363587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61722270417530502028605797 11572925703286969130363587)
          ·
            refine ⟨17359388554930453695545381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11572925703286969130363587 17359388554930453695545381)
            ·
              refine ⟨3254885354049460067914759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17359388554930453695545381 3254885354049460067914759)
              ·
                refine ⟨4882328031074190101872139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254885354049460067914759 4882328031074190101872139)
                ·
                  refine ⟨7323492046611285152808209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882328031074190101872139 7323492046611285152808209)
                  ·
                    refine ⟨5492619034958463864606157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7323492046611285152808209 5492619034958463864606157)
                    ·
                      refine ⟨2059732138109423949227309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5492619034958463864606157 2059732138109423949227309)
                      ·
                        rfl

theorem cell23_4011314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_4011314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011314 prefixEnd_4011314 := by exact prefixLift 4011314
  have htrace : WordTrace (prefixWord ++ tailWord_4011314) baseStart_4011314 baseEnd_4011314 := by
    simpa [prefixWord, tailWord_4011314, baseEnd_4011314] using wordTrace_append hprefix tailTrace_4011314
  have hstable : (prefixWord ++ tailWord_4011314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011314).length < 2 ^ (prefixWord ++ tailWord_4011314).sum := by decide
  have hdescent : baseEnd_4011314 < baseStart_4011314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011321 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 2, 4]
def baseStart_4011321 : Nat := 118140960795 + 4011321 * 2 ^ 59
def prefixEnd_4011321 : Nat := 4983230072969 + 3 ^ 40 * 4011321 * 2
def baseEnd_4011321 : Nat := 686578577491335140613259

theorem tailTrace_4011321 : CollatzResearch.WordTrace tailWord_4011321 prefixEnd_4011321 686578577491335140613259 := by
  unfold tailWord_4011321
  simp only [CollatzResearch.WordTrace]
  refine ⟨146304896300676570929977817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97536597533784380619985211 146304896300676570929977817)
  ·
    refine ⟨109728672225507428197483363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146304896300676570929977817 109728672225507428197483363)
    ·
      refine ⟨164593008338261142296225045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109728672225507428197483363 164593008338261142296225045)
      ·
        refine ⟨7715297265855991045135549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164593008338261142296225045 7715297265855991045135549)
        ·
          refine ⟨2893236474695996641925831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7715297265855991045135549 2893236474695996641925831)
          ·
            refine ⟨4339854712043994962888747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893236474695996641925831 4339854712043994962888747)
            ·
              refine ⟨6509782068065992444333121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339854712043994962888747 6509782068065992444333121)
              ·
                refine ⟨4882336551049494333249841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6509782068065992444333121 4882336551049494333249841)
                ·
                  refine ⟨3661752413287120749937381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4882336551049494333249841 3661752413287120749937381)
                  ·
                    refine ⟨686578577491335140613259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3661752413287120749937381 686578577491335140613259)
                    ·
                      rfl

theorem cell23_4011321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 4].length) (baseStart_4011321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011321 prefixEnd_4011321 := by exact prefixLift 4011321
  have htrace : WordTrace (prefixWord ++ tailWord_4011321) baseStart_4011321 baseEnd_4011321 := by
    simpa [prefixWord, tailWord_4011321, baseEnd_4011321] using wordTrace_append hprefix tailTrace_4011321
  have hstable : (prefixWord ++ tailWord_4011321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011321).length < 2 ^ (prefixWord ++ tailWord_4011321).sum := by decide
  have hdescent : baseEnd_4011321 < baseStart_4011321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011327 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 3]
def baseStart_4011327 : Nat := 118140960795 + 4011327 * 2 ^ 59
def prefixEnd_4011327 : Nat := 4983230072969 + 3 ^ 40 * 4011327 * 2
def baseEnd_4011327 : Nat := 2059738813357932398364749

theorem tailTrace_4011327 : CollatzResearch.WordTrace tailWord_4011327 prefixEnd_4011327 2059738813357932398364749 := by
  unfold tailWord_4011327
  simp only [CollatzResearch.WordTrace]
  refine ⟨146305115138654833954696235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97536743425769889303130823 146305115138654833954696235)
  ·
    refine ⟨219457672707982250932044353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146305115138654833954696235 219457672707982250932044353)
    ·
      refine ⟨164593254530986688199033265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219457672707982250932044353 164593254530986688199033265)
      ·
        refine ⟨123444940898240016149274949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164593254530986688199033265 123444940898240016149274949)
        ·
          refine ⟨23145926418420003027989053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123444940898240016149274949 23145926418420003027989053)
          ·
            refine ⟨8679722406907501135495895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23145926418420003027989053 8679722406907501135495895)
            ·
              refine ⟨13019583610361251703243843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8679722406907501135495895 13019583610361251703243843)
              ·
                refine ⟨19529375415541877554865765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13019583610361251703243843 19529375415541877554865765)
                ·
                  refine ⟨3661757890414102041537331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19529375415541877554865765 3661757890414102041537331)
                  ·
                    refine ⟨5492636835621153062305997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3661757890414102041537331 5492636835621153062305997)
                    ·
                      refine ⟨2059738813357932398364749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5492636835621153062305997 2059738813357932398364749)
                      ·
                        rfl

theorem cell23_4011327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_4011327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011327 prefixEnd_4011327 := by exact prefixLift 4011327
  have htrace : WordTrace (prefixWord ++ tailWord_4011327) baseStart_4011327 baseEnd_4011327 := by
    simpa [prefixWord, tailWord_4011327, baseEnd_4011327] using wordTrace_append hprefix tailTrace_4011327
  have hstable : (prefixWord ++ tailWord_4011327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011327).length < 2 ^ (prefixWord ++ tailWord_4011327).sum := by decide
  have hdescent : baseEnd_4011327 < baseStart_4011327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011333 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_4011333 : Nat := 118140960795 + 4011333 * 2 ^ 59
def prefixEnd_4011333 : Nat := 4983230072969 + 3 ^ 40 * 4011333 * 2
def baseEnd_4011333 : Nat := 2059741894241859374889721

theorem tailTrace_4011333 : CollatzResearch.WordTrace tailWord_4011333 prefixEnd_4011333 2059741894241859374889721 := by
  unfold tailWord_4011333
  simp only [CollatzResearch.WordTrace]
  refine ⟨146305333976633096979414653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97536889317755397986276435 146305333976633096979414653)
  ·
    refine ⟨54864500241237411367280495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146305333976633096979414653 54864500241237411367280495)
    ·
      refine ⟨82296750361856117050920743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54864500241237411367280495 82296750361856117050920743)
      ·
        refine ⟨123445125542784175576381115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82296750361856117050920743 123445125542784175576381115)
        ·
          refine ⟨185167688314176263364571673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123445125542784175576381115 185167688314176263364571673)
          ·
            refine ⟨138875766235632197523428755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185167688314176263364571673 138875766235632197523428755)
            ·
              refine ⟨208313649353448296285143133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138875766235632197523428755 208313649353448296285143133)
              ·
                refine ⟨78117618507543111106928675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208313649353448296285143133 78117618507543111106928675)
                ·
                  refine ⟨117176427761314666660393013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78117618507543111106928675 117176427761314666660393013)
                  ·
                    refine ⟨10985290102623249999411845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117176427761314666660393013 10985290102623249999411845)
                    ·
                      refine ⟨2059741894241859374889721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10985290102623249999411845 2059741894241859374889721)
                      ·
                        rfl

theorem cell23_4011333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_4011333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011333 prefixEnd_4011333 := by exact prefixLift 4011333
  have htrace : WordTrace (prefixWord ++ tailWord_4011333) baseStart_4011333 baseEnd_4011333 := by
    simpa [prefixWord, tailWord_4011333, baseEnd_4011333] using wordTrace_append hprefix tailTrace_4011333
  have hstable : (prefixWord ++ tailWord_4011333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011333).length < 2 ^ (prefixWord ++ tailWord_4011333).sum := by decide
  have hdescent : baseEnd_4011333 < baseStart_4011333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011341 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4011341 : Nat := 118140960795 + 4011341 * 2 ^ 59
def prefixEnd_4011341 : Nat := 4983230072969 + 3 ^ 40 * 4011341 * 2
def baseEnd_4011341 : Nat := 2059746002087095343589685

theorem tailTrace_4011341 : CollatzResearch.WordTrace tailWord_4011341 prefixEnd_4011341 2059746002087095343589685 := by
  unfold tailWord_4011341
  simp only [CollatzResearch.WordTrace]
  refine ⟨146305625760604114345705877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97537083840402742897137251 146305625760604114345705877)
  ·
    refine ⟨6858076207528317859954963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146305625760604114345705877 6858076207528317859954963)
    ·
      refine ⟨10287114311292476789932445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6858076207528317859954963 10287114311292476789932445)
      ·
        refine ⟨3857667866734678796224667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10287114311292476789932445 3857667866734678796224667)
        ·
          refine ⟨5786501800102018194337001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857667866734678796224667 5786501800102018194337001)
          ·
            refine ⟨4339876350076513645752751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5786501800102018194337001 4339876350076513645752751)
            ·
              refine ⟨6509814525114770468629127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339876350076513645752751 6509814525114770468629127)
              ·
                refine ⟨9764721787672155702943691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6509814525114770468629127 9764721787672155702943691)
                ·
                  refine ⟨14647082681508233554415537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764721787672155702943691 14647082681508233554415537)
                  ·
                    refine ⟨10985312011131175165811653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14647082681508233554415537 10985312011131175165811653)
                    ·
                      refine ⟨2059746002087095343589685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10985312011131175165811653 2059746002087095343589685)
                      ·
                        rfl

theorem cell23_4011341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4011341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011341 prefixEnd_4011341 := by exact prefixLift 4011341
  have htrace : WordTrace (prefixWord ++ tailWord_4011341) baseStart_4011341 baseEnd_4011341 := by
    simpa [prefixWord, tailWord_4011341, baseEnd_4011341] using wordTrace_append hprefix tailTrace_4011341
  have hstable : (prefixWord ++ tailWord_4011341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011341).length < 2 ^ (prefixWord ++ tailWord_4011341).sum := by decide
  have hdescent : baseEnd_4011341 < baseStart_4011341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011344 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 2, 1, 3]
def baseStart_4011344 : Nat := 118140960795 + 4011344 * 2 ^ 59
def prefixEnd_4011344 : Nat := 4983230072969 + 3 ^ 40 * 4011344 * 2
def baseEnd_4011344 : Nat := 2059747542529058831852171

theorem tailTrace_4011344 : CollatzResearch.WordTrace tailWord_4011344 prefixEnd_4011344 2059747542529058831852171 := by
  unfold tailWord_4011344
  simp only [CollatzResearch.WordTrace]
  refine ⟨73152867589796622929032543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97537156786395497238710057 73152867589796622929032543)
  ·
    refine ⟨109729301384694934393548815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73152867589796622929032543 109729301384694934393548815)
    ·
      refine ⟨164593952077042401590323223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109729301384694934393548815 164593952077042401590323223)
      ·
        refine ⟨246890928115563602385484835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164593952077042401590323223 246890928115563602385484835)
        ·
          refine ⟨370336392173345403578227253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246890928115563602385484835 370336392173345403578227253)
          ·
            refine ⟨34719036766251131585458805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370336392173345403578227253 34719036766251131585458805)
            ·
              refine ⟨3254909696836043586136763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34719036766251131585458805 3254909696836043586136763)
              ·
                refine ⟨4882364545254065379205145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254909696836043586136763 4882364545254065379205145)
                ·
                  refine ⟨3661773408940549034403859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4882364545254065379205145 3661773408940549034403859)
                  ·
                    refine ⟨5492660113410823551605789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3661773408940549034403859 5492660113410823551605789)
                    ·
                      refine ⟨2059747542529058831852171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5492660113410823551605789 2059747542529058831852171)
                      ·
                        rfl

theorem cell23_4011344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 1, 3].length) (baseStart_4011344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011344 prefixEnd_4011344 := by exact prefixLift 4011344
  have htrace : WordTrace (prefixWord ++ tailWord_4011344) baseStart_4011344 baseEnd_4011344 := by
    simpa [prefixWord, tailWord_4011344, baseEnd_4011344] using wordTrace_append hprefix tailTrace_4011344
  have hstable : (prefixWord ++ tailWord_4011344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011344).length < 2 ^ (prefixWord ++ tailWord_4011344).sum := by decide
  have hdescent : baseEnd_4011344 < baseStart_4011344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011383 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_4011383 : Nat := 118140960795 + 4011383 * 2 ^ 59
def prefixEnd_4011383 : Nat := 4983230072969 + 3 ^ 40 * 4011383 * 2
def baseEnd_4011383 : Nat := 2059767568274584179264491

theorem tailTrace_4011383 : CollatzResearch.WordTrace tailWord_4011383 prefixEnd_4011383 2059767568274584179264491 := by
  unfold tailWord_4011383
  simp only [CollatzResearch.WordTrace]
  refine ⟨146307157626451955518734803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97538105084301303679156535 146307157626451955518734803)
  ·
    refine ⟨219460736439677933278102205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146307157626451955518734803 219460736439677933278102205)
    ·
      refine ⟨82297776164879224979288327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219460736439677933278102205 82297776164879224979288327)
      ·
        refine ⟨123446664247318837468932491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82297776164879224979288327 123446664247318837468932491)
        ·
          refine ⟨185169996370978256203398737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123446664247318837468932491 185169996370978256203398737)
          ·
            refine ⟨138877497278233692152549053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185169996370978256203398737 138877497278233692152549053)
            ·
              refine ⟨52079061479337634557205895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138877497278233692152549053 52079061479337634557205895)
              ·
                refine ⟨78118592219006451835808843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52079061479337634557205895 78118592219006451835808843)
                ·
                  refine ⟨117177888328509677753713265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78118592219006451835808843 117177888328509677753713265)
                  ·
                    refine ⟨87883416246382258315284949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117177888328509677753713265 87883416246382258315284949)
                    ·
                      refine ⟨2059767568274584179264491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87883416246382258315284949 2059767568274584179264491)
                      ·
                        rfl

theorem cell23_4011383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_4011383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011383 prefixEnd_4011383 := by exact prefixLift 4011383
  have htrace : WordTrace (prefixWord ++ tailWord_4011383) baseStart_4011383 baseEnd_4011383 := by
    simpa [prefixWord, tailWord_4011383, baseEnd_4011383] using wordTrace_append hprefix tailTrace_4011383
  have hstable : (prefixWord ++ tailWord_4011383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011383).length < 2 ^ (prefixWord ++ tailWord_4011383).sum := by decide
  have hdescent : baseEnd_4011383 < baseStart_4011383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011401 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 2, 2, 2]
def baseStart_4011401 : Nat := 118140960795 + 4011401 * 2 ^ 59
def prefixEnd_4011401 : Nat := 4983230072969 + 3 ^ 40 * 4011401 * 2
def baseEnd_4011401 : Nat := 2059776810926365108839409

theorem tailTrace_4011401 : CollatzResearch.WordTrace tailWord_4011401 prefixEnd_4011401 2059776810926365108839409 := by
  unfold tailWord_4011401
  simp only [CollatzResearch.WordTrace]
  refine ⟨146307814140386744592890057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97538542760257829728593371 146307814140386744592890057)
  ·
    refine ⟨109730860605290058444667543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146307814140386744592890057 109730860605290058444667543)
    ·
      refine ⟨164596290907935087667001315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109730860605290058444667543 164596290907935087667001315)
      ·
        refine ⟨246894436361902631500501973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164596290907935087667001315 246894436361902631500501973)
        ·
          refine ⟨5786588352232092925793015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 246894436361902631500501973 5786588352232092925793015)
          ·
            refine ⟨8679882528348139388689523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786588352232092925793015 8679882528348139388689523)
            ·
              refine ⟨13019823792522209083034285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8679882528348139388689523 13019823792522209083034285)
              ·
                refine ⟨4882433922195828406137857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13019823792522209083034285 4882433922195828406137857)
                ·
                  refine ⟨3661825441646871304603393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4882433922195828406137857 3661825441646871304603393)
                  ·
                    refine ⟨2746369081235153478452545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3661825441646871304603393 2746369081235153478452545)
                    ·
                      refine ⟨2059776810926365108839409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746369081235153478452545 2059776810926365108839409)
                      ·
                        rfl

theorem cell23_4011401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 2, 2].length) (baseStart_4011401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011401 prefixEnd_4011401 := by exact prefixLift 4011401
  have htrace : WordTrace (prefixWord ++ tailWord_4011401) baseStart_4011401 baseEnd_4011401 := by
    simpa [prefixWord, tailWord_4011401, baseEnd_4011401] using wordTrace_append hprefix tailTrace_4011401
  have hstable : (prefixWord ++ tailWord_4011401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011401).length < 2 ^ (prefixWord ++ tailWord_4011401).sum := by decide
  have hdescent : baseEnd_4011401 < baseStart_4011401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011440 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_4011440 : Nat := 118140960795 + 4011440 * 2 ^ 59
def prefixEnd_4011440 : Nat := 4983230072969 + 3 ^ 40 * 4011440 * 2
def baseEnd_4011440 : Nat := 2059796836671890456251729

theorem tailTrace_4011440 : CollatzResearch.WordTrace tailWord_4011440 prefixEnd_4011440 2059796836671890456251729 := by
  unfold tailWord_4011440
  simp only [CollatzResearch.WordTrace]
  refine ⟨73154618293622727126779887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97539491058163636169039849 73154618293622727126779887)
  ·
    refine ⟨109731927440434090690169831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73154618293622727126779887 109731927440434090690169831)
    ·
      refine ⟨164597891160651136035254747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109731927440434090690169831 164597891160651136035254747)
      ·
        refine ⟨246896836740976704052882121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164597891160651136035254747 246896836740976704052882121)
        ·
          refine ⟨185172627555732528039661591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246896836740976704052882121 185172627555732528039661591)
          ·
            refine ⟨277758941333598792059492387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185172627555732528039661591 277758941333598792059492387)
            ·
              refine ⟨416638412000398188089238581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277758941333598792059492387 416638412000398188089238581)
              ·
                refine ⟨39059851125037330133366117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 416638412000398188089238581 39059851125037330133366117)
                ·
                  refine ⟨7323722085944499400006147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39059851125037330133366117 7323722085944499400006147)
                  ·
                    refine ⟨10985583128916749100009221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7323722085944499400006147 10985583128916749100009221)
                    ·
                      refine ⟨2059796836671890456251729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10985583128916749100009221 2059796836671890456251729)
                      ·
                        rfl

theorem cell23_4011440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_4011440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011440 prefixEnd_4011440 := by exact prefixLift 4011440
  have htrace : WordTrace (prefixWord ++ tailWord_4011440) baseStart_4011440 baseEnd_4011440 := by
    simpa [prefixWord, tailWord_4011440, baseEnd_4011440] using wordTrace_append hprefix tailTrace_4011440
  have hstable : (prefixWord ++ tailWord_4011440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011440).length < 2 ^ (prefixWord ++ tailWord_4011440).sum := by decide
  have hdescent : baseEnd_4011440 < baseStart_4011440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011458 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 7]
def baseStart_4011458 : Nat := 118140960795 + 4011458 * 2 ^ 59
def prefixEnd_4011458 : Nat := 4983230072969 + 3 ^ 40 * 4011458 * 2
def baseEnd_4011458 : Nat := 228867342147074598425183

theorem tailTrace_4011458 : CollatzResearch.WordTrace tailWord_4011458 prefixEnd_4011458 228867342147074598425183 := by
  unfold tailWord_4011458
  simp only [CollatzResearch.WordTrace]
  refine ⟨36577473275295060831928757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97539928734120162218476685 36577473275295060831928757)
  ·
    refine ⟨3429138119558911952993321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36577473275295060831928757 3429138119558911952993321)
    ·
      refine ⟨2571853589669183964744991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3429138119558911952993321 2571853589669183964744991)
      ·
        refine ⟨3857780384503775947117487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571853589669183964744991 3857780384503775947117487)
        ·
          refine ⟨5786670576755663920676231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857780384503775947117487 5786670576755663920676231)
          ·
            refine ⟨8680005865133495881014347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786670576755663920676231 8680005865133495881014347)
            ·
              refine ⟨13020008797700243821521521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8680005865133495881014347 13020008797700243821521521)
              ·
                refine ⟨9765006598275182866141141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13020008797700243821521521 9765006598275182866141141)
                ·
                  refine ⟨228867342147074598425183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9765006598275182866141141 228867342147074598425183)
                  ·
                    rfl

theorem cell23_4011458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_4011458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011458 prefixEnd_4011458 := by exact prefixLift 4011458
  have htrace : WordTrace (prefixWord ++ tailWord_4011458) baseStart_4011458 baseEnd_4011458 := by
    simpa [prefixWord, tailWord_4011458, baseEnd_4011458] using wordTrace_append hprefix tailTrace_4011458
  have hstable : (prefixWord ++ tailWord_4011458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011458).length < 2 ^ (prefixWord ++ tailWord_4011458).sum := by decide
  have hdescent : baseEnd_4011458 < baseStart_4011458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011477 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_4011477 : Nat := 118140960795 + 4011477 * 2 ^ 59
def prefixEnd_4011477 : Nat := 4983230072969 + 3 ^ 40 * 4011477 * 2
def baseEnd_4011477 : Nat := 2059815835456106811489059

theorem tailTrace_4011477 : CollatzResearch.WordTrace tailWord_4011477 prefixEnd_4011477 2059815835456106811489059 := by
  unfold tailWord_4011477
  simp only [CollatzResearch.WordTrace]
  refine ⟨146310586088111409572656685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97540390725407606381771123 146310586088111409572656685)
  ·
    refine ⟨54866469783041778589746257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146310586088111409572656685 54866469783041778589746257)
    ·
      refine ⟨41149852337281333942309693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54866469783041778589746257 41149852337281333942309693)
      ·
        refine ⟨15431194626480500228366135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41149852337281333942309693 15431194626480500228366135)
        ·
          refine ⟨23146791939720750342549203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15431194626480500228366135 23146791939720750342549203)
          ·
            refine ⟨34720187909581125513823805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23146791939720750342549203 34720187909581125513823805)
            ·
              refine ⟨13020070466092922067683927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34720187909581125513823805 13020070466092922067683927)
              ·
                refine ⟨19530105699139383101525891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13020070466092922067683927 19530105699139383101525891)
                ·
                  refine ⟨29295158548709074652288837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19530105699139383101525891 29295158548709074652288837)
                  ·
                    refine ⟨5492842227882951497304157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29295158548709074652288837 5492842227882951497304157)
                    ·
                      refine ⟨2059815835456106811489059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5492842227882951497304157 2059815835456106811489059)
                      ·
                        rfl

theorem cell23_4011477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_4011477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011477 prefixEnd_4011477 := by exact prefixLift 4011477
  have htrace : WordTrace (prefixWord ++ tailWord_4011477) baseStart_4011477 baseEnd_4011477 := by
    simpa [prefixWord, tailWord_4011477, baseEnd_4011477] using wordTrace_append hprefix tailTrace_4011477
  have hstable : (prefixWord ++ tailWord_4011477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011477).length < 2 ^ (prefixWord ++ tailWord_4011477).sum := by decide
  have hdescent : baseEnd_4011477 < baseStart_4011477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011501 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_4011501 : Nat := 118140960795 + 4011501 * 2 ^ 59
def prefixEnd_4011501 : Nat := 4983230072969 + 3 ^ 40 * 4011501 * 2
def baseEnd_4011501 : Nat := 686609386330604905862983

theorem tailTrace_4011501 : CollatzResearch.WordTrace tailWord_4011501 prefixEnd_4011501 686609386330604905862983 := by
  unfold tailWord_4011501
  simp only [CollatzResearch.WordTrace]
  refine ⟨146311461440024461671530357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97540974293349641114353571 146311461440024461671530357)
  ·
    refine ⟨13716699510002293281705971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146311461440024461671530357 13716699510002293281705971)
    ·
      refine ⟨20575049265003439922558957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13716699510002293281705971 20575049265003439922558957)
      ·
        refine ⟨7715643474376289970959609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20575049265003439922558957 7715643474376289970959609)
        ·
          refine ⟨5786732605782217478219707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7715643474376289970959609 5786732605782217478219707)
          ·
            refine ⟨8680098908673326217329561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786732605782217478219707 8680098908673326217329561)
            ·
              refine ⟨6510074181504994662997171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8680098908673326217329561 6510074181504994662997171)
              ·
                refine ⟨9765111272257491994495757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510074181504994662997171 9765111272257491994495757)
                ·
                  refine ⟨3661916727096559497935909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9765111272257491994495757 3661916727096559497935909)
                  ·
                    refine ⟨686609386330604905862983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3661916727096559497935909 686609386330604905862983)
                    ·
                      rfl

theorem cell23_4011501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_4011501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011501 prefixEnd_4011501 := by exact prefixLift 4011501
  have htrace : WordTrace (prefixWord ++ tailWord_4011501) baseStart_4011501 baseEnd_4011501 := by
    simpa [prefixWord, tailWord_4011501, baseEnd_4011501] using wordTrace_append hprefix tailTrace_4011501
  have hstable : (prefixWord ++ tailWord_4011501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011501).length < 2 ^ (prefixWord ++ tailWord_4011501).sum := by decide
  have hdescent : baseEnd_4011501 < baseStart_4011501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011577 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4011577 : Nat := 118140960795 + 4011577 * 2 ^ 59
def prefixEnd_4011577 : Nat := 4983230072969 + 3 ^ 40 * 4011577 * 2
def baseEnd_4011577 : Nat := 2059867183521556420238599

theorem tailTrace_4011577 : CollatzResearch.WordTrace tailWord_4011577 prefixEnd_4011577 2059867183521556420238599 := by
  unfold tailWord_4011577
  simp only [CollatzResearch.WordTrace]
  refine ⟨146314233387749126651296985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97542822258499417767531323 146314233387749126651296985)
  ·
    refine ⟨109735675040811844988472739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146314233387749126651296985 109735675040811844988472739)
    ·
      refine ⟨164603512561217767482709109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109735675040811844988472739 164603512561217767482709109)
      ·
        refine ⟨15431579302614165701503979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164603512561217767482709109 15431579302614165701503979)
        ·
          refine ⟨23147368953921248552255969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15431579302614165701503979 23147368953921248552255969)
          ·
            refine ⟨17360526715440936414191977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23147368953921248552255969 17360526715440936414191977)
            ·
              refine ⟨13020395036580702310643983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17360526715440936414191977 13020395036580702310643983)
              ·
                refine ⟨19530592554871053465965975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13020395036580702310643983 19530592554871053465965975)
                ·
                  refine ⟨29295888832306580198948963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19530592554871053465965975 29295888832306580198948963)
                  ·
                    refine ⟨43943833248459870298423445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29295888832306580198948963 43943833248459870298423445)
                    ·
                      refine ⟨2059867183521556420238599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43943833248459870298423445 2059867183521556420238599)
                      ·
                        rfl

theorem cell23_4011577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4011577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011577 prefixEnd_4011577 := by exact prefixLift 4011577
  have htrace : WordTrace (prefixWord ++ tailWord_4011577) baseStart_4011577 baseEnd_4011577 := by
    simpa [prefixWord, tailWord_4011577, baseEnd_4011577] using wordTrace_append hprefix tailTrace_4011577
  have hstable : (prefixWord ++ tailWord_4011577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011577).length < 2 ^ (prefixWord ++ tailWord_4011577).sum := by decide
  have hdescent : baseEnd_4011577 < baseStart_4011577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011598 : List Nat := [4, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2]
def baseStart_4011598 : Nat := 118140960795 + 4011598 * 2 ^ 59
def prefixEnd_4011598 : Nat := 4983230072969 + 3 ^ 40 * 4011598 * 2
def baseEnd_4011598 : Nat := 2059877966615300838076003

theorem tailTrace_4011598 : CollatzResearch.WordTrace tailWord_4011598 prefixEnd_4011598 2059877966615300838076003 := by
  unfold tailWord_4011598
  simp only [CollatzResearch.WordTrace]
  refine ⟨18289374915084130904726431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97543332880448698158540965 18289374915084130904726431)
  ·
    refine ⟨27434062372626196357089647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18289374915084130904726431 27434062372626196357089647)
    ·
      refine ⟨41151093558939294535634471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27434062372626196357089647 41151093558939294535634471)
      ·
        refine ⟨61726640338408941803451707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41151093558939294535634471 61726640338408941803451707)
        ·
          refine ⟨92589960507613412705177561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61726640338408941803451707 92589960507613412705177561)
          ·
            refine ⟨69442470380710059528883171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92589960507613412705177561 69442470380710059528883171)
            ·
              refine ⟨104163705571065089293324757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69442470380710059528883171 104163705571065089293324757)
              ·
                refine ⟨2441336849321838030312299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104163705571065089293324757 2441336849321838030312299)
                ·
                  refine ⟨3662005273982757045468449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441336849321838030312299 3662005273982757045468449)
                  ·
                    refine ⟨2746503955487067784101337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3662005273982757045468449 2746503955487067784101337)
                    ·
                      refine ⟨2059877966615300838076003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746503955487067784101337 2059877966615300838076003)
                      ·
                        rfl

theorem cell23_4011598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_4011598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011598 prefixEnd_4011598 := by exact prefixLift 4011598
  have htrace : WordTrace (prefixWord ++ tailWord_4011598) baseStart_4011598 baseEnd_4011598 := by
    simpa [prefixWord, tailWord_4011598, baseEnd_4011598] using wordTrace_append hprefix tailTrace_4011598
  have hstable : (prefixWord ++ tailWord_4011598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011598).length < 2 ^ (prefixWord ++ tailWord_4011598).sum := by decide
  have hdescent : baseEnd_4011598 < baseStart_4011598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011601 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 1, 2, 3]
def baseStart_4011601 : Nat := 118140960795 + 4011601 * 2 ^ 59
def prefixEnd_4011601 : Nat := 4983230072969 + 3 ^ 40 * 4011601 * 2
def baseEnd_4011601 : Nat := 2059879507057264326338489

theorem tailTrace_4011601 : CollatzResearch.WordTrace tailWord_4011601 prefixEnd_4011601 2059879507057264326338489 := by
  unfold tailWord_4011601
  simp only [CollatzResearch.WordTrace]
  refine ⟨146315108739662178750170657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97543405826441452500113771 146315108739662178750170657)
  ·
    refine ⟨109736331554746634062627993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146315108739662178750170657 109736331554746634062627993)
    ·
      refine ⟨82302248666059975546970995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109736331554746634062627993 82302248666059975546970995)
      ·
        refine ⟨123453372999089963320456493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82302248666059975546970995 123453372999089963320456493)
        ·
          refine ⟨46295014874658736245171185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123453372999089963320456493 46295014874658736245171185)
          ·
            refine ⟨34721261155994052183878389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46295014874658736245171185 34721261155994052183878389)
            ·
              refine ⟨3255118233374442392238599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34721261155994052183878389 3255118233374442392238599)
              ·
                refine ⟨4882677350061663588357899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255118233374442392238599 4882677350061663588357899)
                ·
                  refine ⟨7324016025092495382536849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882677350061663588357899 7324016025092495382536849)
                  ·
                    refine ⟨5493012018819371536902637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7324016025092495382536849 5493012018819371536902637)
                    ·
                      refine ⟨2059879507057264326338489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5493012018819371536902637 2059879507057264326338489)
                      ·
                        rfl

theorem cell23_4011601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_4011601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011601 prefixEnd_4011601 := by exact prefixLift 4011601
  have htrace : WordTrace (prefixWord ++ tailWord_4011601) baseStart_4011601 baseEnd_4011601 := by
    simpa [prefixWord, tailWord_4011601, baseEnd_4011601] using wordTrace_append hprefix tailTrace_4011601
  have hstable : (prefixWord ++ tailWord_4011601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011601).length < 2 ^ (prefixWord ++ tailWord_4011601).sum := by decide
  have hdescent : baseEnd_4011601 < baseStart_4011601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011641 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 1, 3, 2]
def baseStart_4011641 : Nat := 118140960795 + 4011641 * 2 ^ 59
def prefixEnd_4011641 : Nat := 4983230072969 + 3 ^ 40 * 4011641 * 2
def baseEnd_4011641 : Nat := 2059900046283444169838305

theorem tailTrace_4011641 : CollatzResearch.WordTrace tailWord_4011641 prefixEnd_4011641 2059900046283444169838305 := by
  unfold tailWord_4011641
  simp only [CollatzResearch.WordTrace]
  refine ⟨146316567659517265581626777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97544378439678177054417851 146316567659517265581626777)
  ·
    refine ⟨109737425744637949186220083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146316567659517265581626777 109737425744637949186220083)
    ·
      refine ⟨164606138616956923779330125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109737425744637949186220083 164606138616956923779330125)
      ·
        refine ⟨61727301981358846417248797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164606138616956923779330125 61727301981358846417248797)
        ·
          refine ⟨23147738243009567406468299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61727301981358846417248797 23147738243009567406468299)
          ·
            refine ⟨34721607364514351109702449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23147738243009567406468299 34721607364514351109702449)
            ·
              refine ⟨26041205523385763332276837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34721607364514351109702449 26041205523385763332276837)
              ·
                refine ⟨4882726035634830624801907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26041205523385763332276837 4882726035634830624801907)
                ·
                  refine ⟨7324089053452245937202861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882726035634830624801907 7324089053452245937202861)
                  ·
                    refine ⟨2746533395044592226451073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7324089053452245937202861 2746533395044592226451073)
                    ·
                      refine ⟨2059900046283444169838305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746533395044592226451073 2059900046283444169838305)
                      ·
                        rfl

theorem cell23_4011641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_4011641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011641 prefixEnd_4011641 := by exact prefixLift 4011641
  have htrace : WordTrace (prefixWord ++ tailWord_4011641) baseStart_4011641 baseEnd_4011641 := by
    simpa [prefixWord, tailWord_4011641, baseEnd_4011641] using wordTrace_append hprefix tailTrace_4011641
  have hstable : (prefixWord ++ tailWord_4011641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011641).length < 2 ^ (prefixWord ++ tailWord_4011641).sum := by decide
  have hdescent : baseEnd_4011641 < baseStart_4011641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011657 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_4011657 : Nat := 118140960795 + 4011657 * 2 ^ 59
def prefixEnd_4011657 : Nat := 4983230072969 + 3 ^ 40 * 4011657 * 2
def baseEnd_4011657 : Nat := 2059908261973916107238231

theorem tailTrace_4011657 : CollatzResearch.WordTrace tailWord_4011657 prefixEnd_4011657 2059908261973916107238231 := by
  unfold tailWord_4011657
  simp only [CollatzResearch.WordTrace]
  refine ⟨146317151227459300314209225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97544767484972866876139483 146317151227459300314209225)
  ·
    refine ⟨109737863420594475235656919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146317151227459300314209225 109737863420594475235656919)
    ·
      refine ⟨164606795130891712853485379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109737863420594475235656919 164606795130891712853485379)
      ·
        refine ⟨246910192696337569280228069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164606795130891712853485379 246910192696337569280228069)
        ·
          refine ⟨46295661130563294240042763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246910192696337569280228069 46295661130563294240042763)
          ·
            refine ⟨69443491695844941360064145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46295661130563294240042763 69443491695844941360064145)
            ·
              refine ⟨52082618771883706020048109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69443491695844941360064145 52082618771883706020048109)
              ·
                refine ⟨19530982039456389757518041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52082618771883706020048109 19530982039456389757518041)
                ·
                  refine ⟨14648236529592292318138531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19530982039456389757518041 14648236529592292318138531)
                  ·
                    refine ⟨21972354794388438477207797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14648236529592292318138531 21972354794388438477207797)
                    ·
                      refine ⟨2059908261973916107238231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21972354794388438477207797 2059908261973916107238231)
                      ·
                        rfl

theorem cell23_4011657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_4011657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011657 prefixEnd_4011657 := by exact prefixLift 4011657
  have htrace : WordTrace (prefixWord ++ tailWord_4011657) baseStart_4011657 baseEnd_4011657 := by
    simpa [prefixWord, tailWord_4011657, baseEnd_4011657] using wordTrace_append hprefix tailTrace_4011657
  have hstable : (prefixWord ++ tailWord_4011657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011657).length < 2 ^ (prefixWord ++ tailWord_4011657).sum := by decide
  have hdescent : baseEnd_4011657 < baseStart_4011657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011658 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_4011658 : Nat := 118140960795 + 4011658 * 2 ^ 59
def prefixEnd_4011658 : Nat := 4983230072969 + 3 ^ 40 * 4011658 * 2
def baseEnd_4011658 : Nat := 2059908775454570603325727

theorem tailTrace_4011658 : CollatzResearch.WordTrace tailWord_4011658 prefixEnd_4011658 2059908775454570603325727 := by
  unfold tailWord_4011658
  simp only [CollatzResearch.WordTrace]
  refine ⟨36579296925113919371248907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97544791800303784989997085 36579296925113919371248907)
  ·
    refine ⟨54868945387670879056873361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36579296925113919371248907 54868945387670879056873361)
    ·
      refine ⟨41151709040753159292655021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54868945387670879056873361 41151709040753159292655021)
      ·
        refine ⟨15431890890282434734745633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41151709040753159292655021 15431890890282434734745633)
        ·
          refine ⟨11573918167711826051059225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15431890890282434734745633 11573918167711826051059225)
          ·
            refine ⟨8680438625783869538294419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11573918167711826051059225 8680438625783869538294419)
            ·
              refine ⟨13020657938675804307441629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8680438625783869538294419 13020657938675804307441629)
              ·
                refine ⟨4882746727003426615290611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13020657938675804307441629 4882746727003426615290611)
                ·
                  refine ⟨7324120090505139922935917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882746727003426615290611 7324120090505139922935917)
                  ·
                    refine ⟨2746545033939427471100969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7324120090505139922935917 2746545033939427471100969)
                    ·
                      refine ⟨2059908775454570603325727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746545033939427471100969 2059908775454570603325727)
                      ·
                        rfl

theorem cell23_4011658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_4011658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011658 prefixEnd_4011658 := by exact prefixLift 4011658
  have htrace : WordTrace (prefixWord ++ tailWord_4011658) baseStart_4011658 baseEnd_4011658 := by
    simpa [prefixWord, tailWord_4011658, baseEnd_4011658] using wordTrace_append hprefix tailTrace_4011658
  have hstable : (prefixWord ++ tailWord_4011658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011658).length < 2 ^ (prefixWord ++ tailWord_4011658).sum := by decide
  have hdescent : baseEnd_4011658 < baseStart_4011658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011682 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4011682 : Nat := 118140960795 + 4011682 * 2 ^ 59
def prefixEnd_4011682 : Nat := 4983230072969 + 3 ^ 40 * 4011682 * 2
def baseEnd_4011682 : Nat := 2059921098990278509425617

theorem tailTrace_4011682 : CollatzResearch.WordTrace tailWord_4011682 prefixEnd_4011682 2059921098990278509425617 := by
  unfold tailWord_4011682
  simp only [CollatzResearch.WordTrace]
  refine ⟨36579515763092182395967325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97545375368245819722579533 36579515763092182395967325)
  ·
    refine ⟨13717318411159568398487747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36579515763092182395967325 13717318411159568398487747)
    ·
      refine ⟨20575977616739352597731621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13717318411159568398487747 20575977616739352597731621)
      ·
        refine ⟨3857995803138628612074679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20575977616739352597731621 3857995803138628612074679)
        ·
          refine ⟨5786993704707942918112019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857995803138628612074679 5786993704707942918112019)
          ·
            refine ⟨8680490557061914377168029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786993704707942918112019 8680490557061914377168029)
            ·
              refine ⟨3255183958898217891438011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8680490557061914377168029 3255183958898217891438011)
              ·
                refine ⟨4882775938347326837157017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255183958898217891438011 4882775938347326837157017)
                ·
                  refine ⟨3662081953760495127867763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4882775938347326837157017 3662081953760495127867763)
                  ·
                    refine ⟨5493122930640742691801645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3662081953760495127867763 5493122930640742691801645)
                    ·
                      refine ⟨2059921098990278509425617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5493122930640742691801645 2059921098990278509425617)
                      ·
                        rfl

theorem cell23_4011682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4011682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011682 prefixEnd_4011682 := by exact prefixLift 4011682
  have htrace : WordTrace (prefixWord ++ tailWord_4011682) baseStart_4011682 baseEnd_4011682 := by
    simpa [prefixWord, tailWord_4011682, baseEnd_4011682] using wordTrace_append hprefix tailTrace_4011682
  have hstable : (prefixWord ++ tailWord_4011682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011682).length < 2 ^ (prefixWord ++ tailWord_4011682).sum := by decide
  have hdescent : baseEnd_4011682 < baseStart_4011682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011684 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_4011684 : Nat := 118140960795 + 4011684 * 2 ^ 59
def prefixEnd_4011684 : Nat := 4983230072969 + 3 ^ 40 * 4011684 * 2
def baseEnd_4011684 : Nat := 2059922125951587501600607

theorem tailTrace_4011684 : CollatzResearch.WordTrace tailWord_4011684 prefixEnd_4011684 2059922125951587501600607 := by
  unfold tailWord_4011684
  simp only [CollatzResearch.WordTrace]
  refine ⟨73159067999180741962721053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97545423998907655950294737 73159067999180741962721053)
  ·
    refine ⟨27434650499692778236020395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73159067999180741962721053 27434650499692778236020395)
    ·
      refine ⟨41151975749539167354030593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27434650499692778236020395 41151975749539167354030593)
      ·
        refine ⟨30863981812154375515522945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41151975749539167354030593 30863981812154375515522945)
        ·
          refine ⟨23147986359115781636642209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30863981812154375515522945 23147986359115781636642209)
          ·
            refine ⟨17360989769336836227481657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23147986359115781636642209 17360989769336836227481657)
            ·
              refine ⟨13020742327002627170611243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17360989769336836227481657 13020742327002627170611243)
              ·
                refine ⟨19531113490503940755916865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13020742327002627170611243 19531113490503940755916865)
                ·
                  refine ⟨14648335117877955566937649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19531113490503940755916865 14648335117877955566937649)
                  ·
                    refine ⟨10986251338408466675203237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14648335117877955566937649 10986251338408466675203237)
                    ·
                      refine ⟨2059922125951587501600607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10986251338408466675203237 2059922125951587501600607)
                      ·
                        rfl

theorem cell23_4011684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_4011684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011684 prefixEnd_4011684 := by exact prefixLift 4011684
  have htrace : WordTrace (prefixWord ++ tailWord_4011684) baseStart_4011684 baseEnd_4011684 := by
    simpa [prefixWord, tailWord_4011684, baseEnd_4011684] using wordTrace_append hprefix tailTrace_4011684
  have hstable : (prefixWord ++ tailWord_4011684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011684).length < 2 ^ (prefixWord ++ tailWord_4011684).sum := by decide
  have hdescent : baseEnd_4011684 < baseStart_4011684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011707 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 6, 5]
def baseStart_4011707 : Nat := 118140960795 + 4011707 * 2 ^ 59
def prefixEnd_4011707 : Nat := 4983230072969 + 3 ^ 40 * 4011707 * 2
def baseEnd_4011707 : Nat := 686644645335546970537667

theorem tailTrace_4011707 : CollatzResearch.WordTrace tailWord_4011707 prefixEnd_4011707 686644645335546970537667 := by
  unfold tailWord_4011707
  simp only [CollatzResearch.WordTrace]
  refine ⟨146318974877278158853529375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97545983251518772569019583 146318974877278158853529375)
  ·
    refine ⟨219478462315917238280294063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146318974877278158853529375 219478462315917238280294063)
    ·
      refine ⟨329217693473875857420441095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219478462315917238280294063 329217693473875857420441095)
      ·
        refine ⟨493826540210813786130661643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329217693473875857420441095 493826540210813786130661643)
        ·
          refine ⟨740739810316220679195992465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493826540210813786130661643 740739810316220679195992465)
          ·
            refine ⟨555554857737165509396994349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740739810316220679195992465 555554857737165509396994349)
            ·
              refine ⟨208333071651437066023872881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555554857737165509396994349 208333071651437066023872881)
              ·
                refine ⟨156249803738577799517904661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208333071651437066023872881 156249803738577799517904661)
                ·
                  refine ⟨7324209550245834352401781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156249803738577799517904661 7324209550245834352401781)
                  ·
                    refine ⟨686644645335546970537667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7324209550245834352401781 686644645335546970537667)
                    ·
                      rfl

theorem cell23_4011707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 5].length) (baseStart_4011707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011707 prefixEnd_4011707 := by exact prefixLift 4011707
  have htrace : WordTrace (prefixWord ++ tailWord_4011707) baseStart_4011707 baseEnd_4011707 := by
    simpa [prefixWord, tailWord_4011707, baseEnd_4011707] using wordTrace_append hprefix tailTrace_4011707
  have hstable : (prefixWord ++ tailWord_4011707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011707).length < 2 ^ (prefixWord ++ tailWord_4011707).sum := by decide
  have hdescent : baseEnd_4011707 < baseStart_4011707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011717 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_4011717 : Nat := 118140960795 + 4011717 * 2 ^ 59
def prefixEnd_4011717 : Nat := 4983230072969 + 3 ^ 40 * 4011717 * 2
def baseEnd_4011717 : Nat := 2059939070813185872487955

theorem tailTrace_4011717 : CollatzResearch.WordTrace tailWord_4011717 prefixEnd_4011717 2059939070813185872487955 := by
  unfold tailWord_4011717
  simp only [CollatzResearch.WordTrace]
  refine ⟨146319339607241930561393405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97546226404827953707595603 146319339607241930561393405)
  ·
    refine ⟨54869752352715723960522527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146319339607241930561393405 54869752352715723960522527)
    ·
      refine ⟨82304628529073585940783791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54869752352715723960522527 82304628529073585940783791)
      ·
        refine ⟨123456942793610378911175687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82304628529073585940783791 123456942793610378911175687)
        ·
          refine ⟨185185414190415568366763531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123456942793610378911175687 185185414190415568366763531)
          ·
            refine ⟨277778121285623352550145297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185185414190415568366763531 277778121285623352550145297)
            ·
              refine ⟨208333590964217514412608973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277778121285623352550145297 208333590964217514412608973)
              ·
                refine ⟨78125096611581567904728365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208333590964217514412608973 78125096611581567904728365)
                ·
                  refine ⟨29296911229343087964273137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78125096611581567904728365 29296911229343087964273137)
                  ·
                    refine ⟨21972683422007315973204853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29296911229343087964273137 21972683422007315973204853)
                    ·
                      refine ⟨2059939070813185872487955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21972683422007315973204853 2059939070813185872487955)
                      ·
                        rfl

theorem cell23_4011717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_4011717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011717 prefixEnd_4011717 := by exact prefixLift 4011717
  have htrace : WordTrace (prefixWord ++ tailWord_4011717) baseStart_4011717 baseEnd_4011717 := by
    simpa [prefixWord, tailWord_4011717, baseEnd_4011717] using wordTrace_append hprefix tailTrace_4011717
  have hstable : (prefixWord ++ tailWord_4011717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011717).length < 2 ^ (prefixWord ++ tailWord_4011717).sum := by decide
  have hdescent : baseEnd_4011717 < baseStart_4011717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011761 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_4011761 : Nat := 118140960795 + 4011761 * 2 ^ 59
def prefixEnd_4011761 : Nat := 4983230072969 + 3 ^ 40 * 4011761 * 2
def baseEnd_4011761 : Nat := 2059961663961983700337753

theorem tailTrace_4011761 : CollatzResearch.WordTrace tailWord_4011761 prefixEnd_4011761 2059961663961983700337753 := by
  unfold tailWord_4011761
  simp only [CollatzResearch.WordTrace]
  refine ⟨146320944419082526075995137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97547296279388350717330091 146320944419082526075995137)
  ·
    refine ⟨109740708314311894556996353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146320944419082526075995137 109740708314311894556996353)
    ·
      refine ⟨82305531235733920917747265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109740708314311894556996353 82305531235733920917747265)
      ·
        refine ⟨61729148426800440688310449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82305531235733920917747265 61729148426800440688310449)
        ·
          refine ⟨46296861320100330516232837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61729148426800440688310449 46296861320100330516232837)
          ·
            refine ⟨8680661497518811971793657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46296861320100330516232837 8680661497518811971793657)
            ·
              refine ⟨6510496123139108978845243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8680661497518811971793657 6510496123139108978845243)
              ·
                refine ⟨9765744184708663468267865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510496123139108978845243 9765744184708663468267865)
                ·
                  refine ⟨7324308138531497601200899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9765744184708663468267865 7324308138531497601200899)
                  ·
                    refine ⟨10986462207797246401801349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7324308138531497601200899 10986462207797246401801349)
                    ·
                      refine ⟨2059961663961983700337753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10986462207797246401801349 2059961663961983700337753)
                      ·
                        rfl

theorem cell23_4011761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_4011761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011761 prefixEnd_4011761 := by exact prefixLift 4011761
  have htrace : WordTrace (prefixWord ++ tailWord_4011761) baseStart_4011761 baseEnd_4011761 := by
    simpa [prefixWord, tailWord_4011761, baseEnd_4011761] using wordTrace_append hprefix tailTrace_4011761
  have hstable : (prefixWord ++ tailWord_4011761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011761).length < 2 ^ (prefixWord ++ tailWord_4011761).sum := by decide
  have hdescent : baseEnd_4011761 < baseStart_4011761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011767 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 10]
def baseStart_4011767 : Nat := 118140960795 + 4011767 * 2 ^ 59
def prefixEnd_4011767 : Nat := 4983230072969 + 3 ^ 40 * 4011767 * 2
def baseEnd_4011767 : Nat := 228884971649545630762525

theorem tailTrace_4011767 : CollatzResearch.WordTrace tailWord_4011767 prefixEnd_4011767 228884971649545630762525 := by
  unfold tailWord_4011767
  simp only [CollatzResearch.WordTrace]
  refine ⟨146321163257060789100713555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97547442171373859400475703 146321163257060789100713555)
  ·
    refine ⟨219481744885591183651070333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146321163257060789100713555 219481744885591183651070333)
    ·
      refine ⟨82305654332096693869151375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219481744885591183651070333 82305654332096693869151375)
      ·
        refine ⟨123458481498145040803727063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82305654332096693869151375 123458481498145040803727063)
        ·
          refine ⟨185187722247217561205590595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123458481498145040803727063 185187722247217561205590595)
          ·
            refine ⟨277781583370826341808385893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185187722247217561205590595 277781583370826341808385893)
            ·
              refine ⟨52084046882029939089072355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277781583370826341808385893 52084046882029939089072355)
              ·
                refine ⟨78126070323044908633608533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52084046882029939089072355 78126070323044908633608533)
                ·
                  refine ⟨228884971649545630762525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 78126070323044908633608533 228884971649545630762525)
                  ·
                    rfl

theorem cell23_4011767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 10].length) (baseStart_4011767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011767 prefixEnd_4011767 := by exact prefixLift 4011767
  have htrace : WordTrace (prefixWord ++ tailWord_4011767) baseStart_4011767 baseEnd_4011767 := by
    simpa [prefixWord, tailWord_4011767, baseEnd_4011767] using wordTrace_append hprefix tailTrace_4011767
  have hstable : (prefixWord ++ tailWord_4011767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011767).length < 2 ^ (prefixWord ++ tailWord_4011767).sum := by decide
  have hdescent : baseEnd_4011767 < baseStart_4011767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011778 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_4011778 : Nat := 118140960795 + 4011778 * 2 ^ 59
def prefixEnd_4011778 : Nat := 4983230072969 + 3 ^ 40 * 4011778 * 2
def baseEnd_4011778 : Nat := 2059970393133110133825175

theorem tailTrace_4011778 : CollatzResearch.WordTrace tailWord_4011778 prefixEnd_4011778 2059970393133110133825175 := by
  unfold tailWord_4011778
  simp only [CollatzResearch.WordTrace]
  refine ⟨36580391115005234494840997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97547709640013958652909325 36580391115005234494840997)
  ·
    refine ⟨6858823334063481467782687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36580391115005234494840997 6858823334063481467782687)
    ·
      refine ⟨10288235001095222201674031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6858823334063481467782687 10288235001095222201674031)
      ·
        refine ⟨15432352501642833302511047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10288235001095222201674031 15432352501642833302511047)
        ·
          refine ⟨23148528752464249953766571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15432352501642833302511047 23148528752464249953766571)
          ·
            refine ⟨34722793128696374930649857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23148528752464249953766571 34722793128696374930649857)
            ·
              refine ⟨26042094846522281197987393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34722793128696374930649857 26042094846522281197987393)
              ·
                refine ⟨19531571134891710898490545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26042094846522281197987393 19531571134891710898490545)
                ·
                  refine ⟨14648678351168783173867909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19531571134891710898490545 14648678351168783173867909)
                  ·
                    refine ⟨2746627190844146845100233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14648678351168783173867909 2746627190844146845100233)
                    ·
                      refine ⟨2059970393133110133825175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746627190844146845100233 2059970393133110133825175)
                      ·
                        rfl

theorem cell23_4011778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_4011778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011778 prefixEnd_4011778 := by exact prefixLift 4011778
  have htrace : WordTrace (prefixWord ++ tailWord_4011778) baseStart_4011778 baseEnd_4011778 := by
    simpa [prefixWord, tailWord_4011778, baseEnd_4011778] using wordTrace_append hprefix tailTrace_4011778
  have hstable : (prefixWord ++ tailWord_4011778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011778).length < 2 ^ (prefixWord ++ tailWord_4011778).sum := by decide
  have hdescent : baseEnd_4011778 < baseStart_4011778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011811 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 3]
def baseStart_4011811 : Nat := 118140960795 + 4011811 * 2 ^ 59
def prefixEnd_4011811 : Nat := 4983230072969 + 3 ^ 40 * 4011811 * 2
def baseEnd_4011811 : Nat := 2059987337994708504712523

theorem tailTrace_4011811 : CollatzResearch.WordTrace tailWord_4011811 prefixEnd_4011811 2059987337994708504712523 := by
  unfold tailWord_4011811
  simp only [CollatzResearch.WordTrace]
  refine ⟨146322768068901384615315287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97548512045934256410210191 146322768068901384615315287)
  ·
    refine ⟨219484152103352076922972931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146322768068901384615315287 219484152103352076922972931)
    ·
      refine ⟨329226228155028115384459397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219484152103352076922972931 329226228155028115384459397)
      ·
        refine ⟨61729917779067771634586137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329226228155028115384459397 61729917779067771634586137)
        ·
          refine ⟨46297438334300828725939603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61729917779067771634586137 46297438334300828725939603)
          ·
            refine ⟨69446157501451243088909405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46297438334300828725939603 69446157501451243088909405)
            ·
              refine ⟨26042309063044216158341027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69446157501451243088909405 26042309063044216158341027)
              ·
                refine ⟨39063463594566324237511541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26042309063044216158341027 39063463594566324237511541)
                ·
                  refine ⟨3662199711990592897266707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39063463594566324237511541 3662199711990592897266707)
                  ·
                    refine ⟨5493299567985889345900061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3662199711990592897266707 5493299567985889345900061)
                    ·
                      refine ⟨2059987337994708504712523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5493299567985889345900061 2059987337994708504712523)
                      ·
                        rfl

theorem cell23_4011811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_4011811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011811 prefixEnd_4011811 := by exact prefixLift 4011811
  have htrace : WordTrace (prefixWord ++ tailWord_4011811) baseStart_4011811 baseEnd_4011811 := by
    simpa [prefixWord, tailWord_4011811, baseEnd_4011811] using wordTrace_append hprefix tailTrace_4011811
  have hstable : (prefixWord ++ tailWord_4011811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011811).length < 2 ^ (prefixWord ++ tailWord_4011811).sum := by decide
  have hdescent : baseEnd_4011811 < baseStart_4011811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011822 : List Nat := [4, 1, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4011822 : Nat := 118140960795 + 4011822 * 2 ^ 59
def prefixEnd_4011822 : Nat := 4983230072969 + 3 ^ 40 * 4011822 * 2
def baseEnd_4011822 : Nat := 686664328760635987224991

theorem tailTrace_4011822 : CollatzResearch.WordTrace tailWord_4011822 prefixEnd_4011822 686664328760635987224991 := by
  unfold tailWord_4011822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18290396158982691686745715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97548779514574355662643813 18290396158982691686745715)
  ·
    refine ⟨27435594238474037530118573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18290396158982691686745715 27435594238474037530118573)
    ·
      refine ⟨10288347839427764073794465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27435594238474037530118573 10288347839427764073794465)
      ·
        refine ⟨7716260879570823055345849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10288347839427764073794465 7716260879570823055345849)
        ·
          refine ⟨5787195659678117291509387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7716260879570823055345849 5787195659678117291509387)
          ·
            refine ⟨8680793489517175937264081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787195659678117291509387 8680793489517175937264081)
            ·
              refine ⟨6510595117137881952948061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8680793489517175937264081 6510595117137881952948061)
              ·
                refine ⟨2441473168926705732355523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6510595117137881952948061 2441473168926705732355523)
                ·
                  refine ⟨3662209753390058598533285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441473168926705732355523 3662209753390058598533285)
                  ·
                    refine ⟨686664328760635987224991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3662209753390058598533285 686664328760635987224991)
                    ·
                      rfl

theorem cell23_4011822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4011822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011822 prefixEnd_4011822 := by exact prefixLift 4011822
  have htrace : WordTrace (prefixWord ++ tailWord_4011822) baseStart_4011822 baseEnd_4011822 := by
    simpa [prefixWord, tailWord_4011822, baseEnd_4011822] using wordTrace_append hprefix tailTrace_4011822
  have hstable : (prefixWord ++ tailWord_4011822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011822).length < 2 ^ (prefixWord ++ tailWord_4011822).sum := by decide
  have hdescent : baseEnd_4011822 < baseStart_4011822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011861 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_4011861 : Nat := 118140960795 + 4011861 * 2 ^ 59
def prefixEnd_4011861 : Nat := 4983230072969 + 3 ^ 40 * 4011861 * 2
def baseEnd_4011861 : Nat := 686671004009144436362431

theorem tailTrace_4011861 : CollatzResearch.WordTrace tailWord_4011861 prefixEnd_4011861 686671004009144436362431 := by
  unfold tailWord_4011861
  simp only [CollatzResearch.WordTrace]
  refine ⟨146324591718720243154635437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97549727812480162103090291 146324591718720243154635437)
  ·
    refine ⟨54871721894520091182988289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146324591718720243154635437 54871721894520091182988289)
    ·
      refine ⟨41153791420890068387241217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54871721894520091182988289 41153791420890068387241217)
      ·
        refine ⟨30865343565667551290430913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41153791420890068387241217 30865343565667551290430913)
        ·
          refine ⟨23149007674250663467823185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30865343565667551290430913 23149007674250663467823185)
          ·
            refine ⟨17361755755687997600867389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23149007674250663467823185 17361755755687997600867389)
            ·
              refine ⟨6510658408382999100325271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17361755755687997600867389 6510658408382999100325271)
              ·
                refine ⟨9765987612574498650487907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510658408382999100325271 9765987612574498650487907)
                ·
                  refine ⟨14648981418861747975731861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9765987612574498650487907 14648981418861747975731861)
                  ·
                    refine ⟨686671004009144436362431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14648981418861747975731861 686671004009144436362431)
                    ·
                      rfl

theorem cell23_4011861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_4011861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011861 prefixEnd_4011861 := by exact prefixLift 4011861
  have htrace : WordTrace (prefixWord ++ tailWord_4011861) baseStart_4011861 baseEnd_4011861 := by
    simpa [prefixWord, tailWord_4011861, baseEnd_4011861] using wordTrace_append hprefix tailTrace_4011861
  have hstable : (prefixWord ++ tailWord_4011861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011861).length < 2 ^ (prefixWord ++ tailWord_4011861).sum := by decide
  have hdescent : baseEnd_4011861 < baseStart_4011861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011904 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 2, 7]
def baseStart_4011904 : Nat := 118140960795 + 4011904 * 2 ^ 59
def prefixEnd_4011904 : Nat := 4983230072969 + 3 ^ 40 * 4011904 * 2
def baseEnd_4011904 : Nat := 686678363898525546949865

theorem tailTrace_4011904 : CollatzResearch.WordTrace tailWord_4011904 prefixEnd_4011904 686678363898525546949865 := by
  unfold tailWord_4011904
  simp only [CollatzResearch.WordTrace]
  refine ⟨73163080028782230749225383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97550773371709640998967177 73163080028782230749225383)
  ·
    refine ⟨109744620043173346123838075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73163080028782230749225383 109744620043173346123838075)
    ·
      refine ⟨164616930064760019185757113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109744620043173346123838075 164616930064760019185757113)
      ·
        refine ⟨123462697548570014389317835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164616930064760019185757113 123462697548570014389317835)
        ·
          refine ⟨185194046322855021583976753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123462697548570014389317835 185194046322855021583976753)
          ·
            refine ⟨138895534742141266187982565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185194046322855021583976753 138895534742141266187982565)
            ·
              refine ⟨26042912764151487410246731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138895534742141266187982565 26042912764151487410246731)
              ·
                refine ⟨39064369146227231115370097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26042912764151487410246731 39064369146227231115370097)
                ·
                  refine ⟨29298276859670423336527573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39064369146227231115370097 29298276859670423336527573)
                  ·
                    refine ⟨686678363898525546949865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29298276859670423336527573 686678363898525546949865)
                    ·
                      rfl

theorem cell23_4011904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_4011904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011904 prefixEnd_4011904 := by exact prefixLift 4011904
  have htrace : WordTrace (prefixWord ++ tailWord_4011904) baseStart_4011904 baseEnd_4011904 := by
    simpa [prefixWord, tailWord_4011904, baseEnd_4011904] using wordTrace_append hprefix tailTrace_4011904
  have hstable : (prefixWord ++ tailWord_4011904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011904).length < 2 ^ (prefixWord ++ tailWord_4011904).sum := by decide
  have hdescent : baseEnd_4011904 < baseStart_4011904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011912 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 2, 4]
def baseStart_4011912 : Nat := 118140960795 + 4011912 * 2 ^ 59
def prefixEnd_4011912 : Nat := 4983230072969 + 3 ^ 40 * 4011912 * 2
def baseEnd_4011912 : Nat := 686679733180270869849853

theorem tailTrace_4011912 : CollatzResearch.WordTrace tailWord_4011912 prefixEnd_4011912 686679733180270869849853 := by
  unfold tailWord_4011912
  simp only [CollatzResearch.WordTrace]
  refine ⟨73163225920767739432370995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97550967894356985909827993 73163225920767739432370995)
  ·
    refine ⟨109744838881151609148556493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73163225920767739432370995 109744838881151609148556493)
    ·
      refine ⟨41154314580431853430708685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109744838881151609148556493 41154314580431853430708685)
      ·
        refine ⟨15432867967661945036515757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41154314580431853430708685 15432867967661945036515757)
        ·
          refine ⟨5787325487873229388693409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15432867967661945036515757 5787325487873229388693409)
          ·
            refine ⟨4340494115904922041520057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5787325487873229388693409 4340494115904922041520057)
            ·
              refine ⟨3255370586928691531140043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340494115904922041520057 3255370586928691531140043)
              ·
                refine ⟨4883055880393037296710065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255370586928691531140043 4883055880393037296710065)
                ·
                  refine ⟨3662291910294777972532549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4883055880393037296710065 3662291910294777972532549)
                  ·
                    refine ⟨686679733180270869849853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3662291910294777972532549 686679733180270869849853)
                    ·
                      rfl

theorem cell23_4011912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_4011912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011912 prefixEnd_4011912 := by exact prefixLift 4011912
  have htrace : WordTrace (prefixWord ++ tailWord_4011912) baseStart_4011912 baseEnd_4011912 := by
    simpa [prefixWord, tailWord_4011912, baseEnd_4011912] using wordTrace_append hprefix tailTrace_4011912
  have hstable : (prefixWord ++ tailWord_4011912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011912).length < 2 ^ (prefixWord ++ tailWord_4011912).sum := by decide
  have hdescent : baseEnd_4011912 < baseStart_4011912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011922 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4011922 : Nat := 118140960795 + 4011922 * 2 ^ 59
def prefixEnd_4011922 : Nat := 4983230072969 + 3 ^ 40 * 4011922 * 2
def baseEnd_4011922 : Nat := 2060044334347357570424513

theorem tailTrace_4011922 : CollatzResearch.WordTrace tailWord_4011922 prefixEnd_4011922 2060044334347357570424513 := by
  unfold tailWord_4011922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36581704142874812643151505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97551211047666167048404013 36581704142874812643151505)
  ·
    refine ⟨27436278107156109482363629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36581704142874812643151505 27436278107156109482363629)
    ·
      refine ⟨10288604290183541055886361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27436278107156109482363629 10288604290183541055886361)
      ·
        refine ⟨7716453217637655791914771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10288604290183541055886361 7716453217637655791914771)
        ·
          refine ⟨11574679826456483687872157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716453217637655791914771 11574679826456483687872157)
          ·
            refine ⟨4340504934921181382952059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11574679826456483687872157 4340504934921181382952059)
            ·
              refine ⟨6510757402381772074428089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340504934921181382952059 6510757402381772074428089)
              ·
                refine ⟨4883068051786329055821067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6510757402381772074428089 4883068051786329055821067)
                ·
                  refine ⟨7324602077679493583731601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883068051786329055821067 7324602077679493583731601)
                  ·
                    refine ⟨5493451558259620187798701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7324602077679493583731601 5493451558259620187798701)
                    ·
                      refine ⟨2060044334347357570424513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5493451558259620187798701 2060044334347357570424513)
                      ·
                        rfl

theorem cell23_4011922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4011922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011922 prefixEnd_4011922 := by exact prefixLift 4011922
  have htrace : WordTrace (prefixWord ++ tailWord_4011922) baseStart_4011922 baseEnd_4011922 := by
    simpa [prefixWord, tailWord_4011922, baseEnd_4011922] using wordTrace_append hprefix tailTrace_4011922
  have hstable : (prefixWord ++ tailWord_4011922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011922).length < 2 ^ (prefixWord ++ tailWord_4011922).sum := by decide
  have hdescent : baseEnd_4011922 < baseStart_4011922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011961 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 3]
def baseStart_4011961 : Nat := 118140960795 + 4011961 * 2 ^ 59
def prefixEnd_4011961 : Nat := 4983230072969 + 3 ^ 40 * 4011961 * 2
def baseEnd_4011961 : Nat := 2060064360092882917836833

theorem tailTrace_4011961 : CollatzResearch.WordTrace tailWord_4011961 prefixEnd_4011961 2060064360092882917836833 := by
  unfold tailWord_4011961
  simp only [CollatzResearch.WordTrace]
  refine ⟨146328239018357960233275737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97552159345571973488850491 146328239018357960233275737)
  ·
    refine ⟨109746179263768470174956803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146328239018357960233275737 109746179263768470174956803)
    ·
      refine ⟨164619268895652705262435205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109746179263768470174956803 164619268895652705262435205)
      ·
        refine ⟨30866112917934882236706601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164619268895652705262435205 30866112917934882236706601)
        ·
          refine ⟨23149584688451161677529951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30866112917934882236706601 23149584688451161677529951)
          ·
            refine ⟨34724377032676742516294927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23149584688451161677529951 34724377032676742516294927)
            ·
              refine ⟨52086565549015113774442391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34724377032676742516294927 52086565549015113774442391)
              ·
                refine ⟨78129848323522670661663587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52086565549015113774442391 78129848323522670661663587)
                ·
                  refine ⟨117194772485284005992495381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78129848323522670661663587 117194772485284005992495381)
                  ·
                    refine ⟨5493504960247687780898221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117194772485284005992495381 5493504960247687780898221)
                    ·
                      refine ⟨2060064360092882917836833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5493504960247687780898221 2060064360092882917836833)
                      ·
                        rfl

theorem cell23_4011961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_4011961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011961 prefixEnd_4011961 := by exact prefixLift 4011961
  have htrace : WordTrace (prefixWord ++ tailWord_4011961) baseStart_4011961 baseEnd_4011961 := by
    simpa [prefixWord, tailWord_4011961, baseEnd_4011961] using wordTrace_append hprefix tailTrace_4011961
  have hstable : (prefixWord ++ tailWord_4011961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011961).length < 2 ^ (prefixWord ++ tailWord_4011961).sum := by decide
  have hdescent : baseEnd_4011961 < baseStart_4011961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011991 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_4011991 : Nat := 118140960795 + 4011991 * 2 ^ 59
def prefixEnd_4011991 : Nat := 4983230072969 + 3 ^ 40 * 4011991 * 2
def baseEnd_4011991 : Nat := 2060079764512517800461695

theorem tailTrace_4011991 : CollatzResearch.WordTrace tailWord_4011991 prefixEnd_4011991 2060079764512517800461695 := by
  unfold tailWord_4011991
  simp only [CollatzResearch.WordTrace]
  refine ⟨146329333208249275356867827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97552888805499516904578551 146329333208249275356867827)
  ·
    refine ⟨219493999812373913035301741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146329333208249275356867827 219493999812373913035301741)
    ·
      refine ⟨82310249929640217388238153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219493999812373913035301741 82310249929640217388238153)
      ·
        refine ⟨61732687447230163041178615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82310249929640217388238153 61732687447230163041178615)
        ·
          refine ⟨92599031170845244561767923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61732687447230163041178615 92599031170845244561767923)
          ·
            refine ⟨138898546756267866842651885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92599031170845244561767923 138898546756267866842651885)
            ·
              refine ⟨52086955033600450065994457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138898546756267866842651885 52086955033600450065994457)
              ·
                refine ⟨39065216275200337549495843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52086955033600450065994457 39065216275200337549495843)
                ·
                  refine ⟨58597824412800506324243765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39065216275200337549495843 58597824412800506324243765)
                  ·
                    refine ⟨5493546038700047467897853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58597824412800506324243765 5493546038700047467897853)
                    ·
                      refine ⟨2060079764512517800461695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5493546038700047467897853 2060079764512517800461695)
                      ·
                        rfl

theorem cell23_4011991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_4011991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011991 prefixEnd_4011991 := by exact prefixLift 4011991
  have htrace : WordTrace (prefixWord ++ tailWord_4011991) baseStart_4011991 baseEnd_4011991 := by
    simpa [prefixWord, tailWord_4011991, baseEnd_4011991] using wordTrace_append hprefix tailTrace_4011991
  have hstable : (prefixWord ++ tailWord_4011991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011991).length < 2 ^ (prefixWord ++ tailWord_4011991).sum := by decide
  have hdescent : baseEnd_4011991 < baseStart_4011991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4011996 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4011996 : Nat := 118140960795 + 4011996 * 2 ^ 59
def prefixEnd_4011996 : Nat := 4983230072969 + 3 ^ 40 * 4011996 * 2
def baseEnd_4011996 : Nat := 2060082331915790280899173

theorem tailTrace_4011996 : CollatzResearch.WordTrace tailWord_4011996 prefixEnd_4011996 2060082331915790280899173 := by
  unfold tailWord_4011996
  simp only [CollatzResearch.WordTrace]
  refine ⟨73164757786615580605399921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97553010382154107473866561 73164757786615580605399921)
  ·
    refine ⟨54873568339961685454049941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73164757786615580605399921 54873568339961685454049941)
    ·
      refine ⟨2572198515935704005658591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54873568339961685454049941 2572198515935704005658591)
      ·
        refine ⟨3858297773903556008487887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2572198515935704005658591 3858297773903556008487887)
        ·
          refine ⟨5787446660855334012731831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858297773903556008487887 5787446660855334012731831)
          ·
            refine ⟨8681169991283001019097747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787446660855334012731831 8681169991283001019097747)
            ·
              refine ⟨13021754986924501528646621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681169991283001019097747 13021754986924501528646621)
              ·
                refine ⟨4883158120096688073242483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13021754986924501528646621 4883158120096688073242483)
                ·
                  refine ⟨7324737180145032109863725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883158120096688073242483 7324737180145032109863725)
                  ·
                    refine ⟨2746776442554387041198897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7324737180145032109863725 2746776442554387041198897)
                    ·
                      refine ⟨2060082331915790280899173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746776442554387041198897 2060082331915790280899173)
                      ·
                        rfl

theorem cell23_4011996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4011996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4011996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4011996 prefixEnd_4011996 := by exact prefixLift 4011996
  have htrace : WordTrace (prefixWord ++ tailWord_4011996) baseStart_4011996 baseEnd_4011996 := by
    simpa [prefixWord, tailWord_4011996, baseEnd_4011996] using wordTrace_append hprefix tailTrace_4011996
  have hstable : (prefixWord ++ tailWord_4011996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4011996).length < 2 ^ (prefixWord ++ tailWord_4011996).sum := by decide
  have hdescent : baseEnd_4011996 < baseStart_4011996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4011996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012011 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 2, 5]
def baseStart_4012011 : Nat := 118140960795 + 4012011 * 2 ^ 59
def prefixEnd_4012011 : Nat := 4983230072969 + 3 ^ 40 * 4012011 * 2
def baseEnd_4012011 : Nat := 686696678041869240737201

theorem tailTrace_4012011 : CollatzResearch.WordTrace tailWord_4012011 prefixEnd_4012011 686696678041869240737201 := by
  unfold tailWord_4012011
  simp only [CollatzResearch.WordTrace]
  refine ⟨146330062668176818772595887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97553375112117879181730591 146330062668176818772595887)
  ·
    refine ⟨219495094002265228158893831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146330062668176818772595887 219495094002265228158893831)
    ·
      refine ⟨329242641003397842238340747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219495094002265228158893831 329242641003397842238340747)
      ·
        refine ⟨493863961505096763357511121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329242641003397842238340747 493863961505096763357511121)
        ·
          refine ⟨370397971128822572518133341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493863961505096763357511121 370397971128822572518133341)
          ·
            refine ⟨138899239173308464694300003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370397971128822572518133341 138899239173308464694300003)
            ·
              refine ⟨208348858759962697041450005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138899239173308464694300003 208348858759962697041450005)
              ·
                refine ⟨9766352754373251423817969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208348858759962697041450005 9766352754373251423817969)
                ·
                  refine ⟨7324764565779938567863477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766352754373251423817969 7324764565779938567863477)
                  ·
                    refine ⟨686696678041869240737201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7324764565779938567863477 686696678041869240737201)
                    ·
                      rfl

theorem cell23_4012011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 5].length) (baseStart_4012011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012011 prefixEnd_4012011 := by exact prefixLift 4012011
  have htrace : WordTrace (prefixWord ++ tailWord_4012011) baseStart_4012011 baseEnd_4012011 := by
    simpa [prefixWord, tailWord_4012011, baseEnd_4012011] using wordTrace_append hprefix tailTrace_4012011
  have hstable : (prefixWord ++ tailWord_4012011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012011).length < 2 ^ (prefixWord ++ tailWord_4012011).sum := by decide
  have hdescent : baseEnd_4012011 < baseStart_4012011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012065 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_4012065 : Nat := 118140960795 + 4012065 * 2 ^ 59
def prefixEnd_4012065 : Nat := 4983230072969 + 3 ^ 40 * 4012065 * 2
def baseEnd_4012065 : Nat := 2060117762080950510936355

theorem tailTrace_4012065 : CollatzResearch.WordTrace tailWord_4012065 prefixEnd_4012065 2060117762080950510936355 := by
  unfold tailWord_4012065
  simp only [CollatzResearch.WordTrace]
  refine ⟨146332032209981185995061649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97554688139987457330041099 146332032209981185995061649)
  ·
    refine ⟨109749024157485889496296237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146332032209981185995061649 109749024157485889496296237)
    ·
      refine ⟨41155884059057208561111089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109749024157485889496296237 41155884059057208561111089)
      ·
        refine ⟨30866913044292906420833317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41155884059057208561111089 30866913044292906420833317)
        ·
          refine ⟨5787546195804919953906247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30866913044292906420833317 5787546195804919953906247)
          ·
            refine ⟨8681319293707379930859371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787546195804919953906247 8681319293707379930859371)
            ·
              refine ⟨13021978940561069896289057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681319293707379930859371 13021978940561069896289057)
              ·
                refine ⟨9766484205420802422216793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13021978940561069896289057 9766484205420802422216793)
                ·
                  refine ⟨7324863154065601816662595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766484205420802422216793 7324863154065601816662595)
                  ·
                    refine ⟨10987294731098402724993893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7324863154065601816662595 10987294731098402724993893)
                    ·
                      refine ⟨2060117762080950510936355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10987294731098402724993893 2060117762080950510936355)
                      ·
                        rfl

theorem cell23_4012065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_4012065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012065 prefixEnd_4012065 := by exact prefixLift 4012065
  have htrace : WordTrace (prefixWord ++ tailWord_4012065) baseStart_4012065 baseEnd_4012065 := by
    simpa [prefixWord, tailWord_4012065, baseEnd_4012065] using wordTrace_append hprefix tailTrace_4012065
  have hstable : (prefixWord ++ tailWord_4012065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012065).length < 2 ^ (prefixWord ++ tailWord_4012065).sum := by decide
  have hdescent : baseEnd_4012065 < baseStart_4012065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012178 : List Nat := [3, 2, 3, 1, 1, 1, 12]
def baseStart_4012178 : Nat := 118140960795 + 4012178 * 2 ^ 59
def prefixEnd_4012178 : Nat := 4983230072969 + 3 ^ 40 * 4012178 * 2
def baseEnd_4012178 : Nat := 25434268955492698380535

theorem tailTrace_4012178 : CollatzResearch.WordTrace tailWord_4012178 prefixEnd_4012178 25434268955492698380535 := by
  unfold tailWord_4012178
  simp only [CollatzResearch.WordTrace]
  refine ⟨36584038414642951573481297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97557435772381204195950125 36584038414642951573481297)
  ·
    refine ⟨27438028810982213680110973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36584038414642951573481297 27438028810982213680110973)
    ·
      refine ⟨10289260804118330130041615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27438028810982213680110973 10289260804118330130041615)
      ·
        refine ⟨15433891206177495195062423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10289260804118330130041615 15433891206177495195062423)
        ·
          refine ⟨23150836809266242792593635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15433891206177495195062423 23150836809266242792593635)
          ·
            refine ⟨34726255213899364188890453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23150836809266242792593635 34726255213899364188890453)
            ·
              refine ⟨25434268955492698380535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34726255213899364188890453 25434268955492698380535)
              ·
                rfl

theorem cell23_4012178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 12].length) (baseStart_4012178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012178 prefixEnd_4012178 := by exact prefixLift 4012178
  have htrace : WordTrace (prefixWord ++ tailWord_4012178) baseStart_4012178 baseEnd_4012178 := by
    simpa [prefixWord, tailWord_4012178, baseEnd_4012178] using wordTrace_append hprefix tailTrace_4012178
  have hstable : (prefixWord ++ tailWord_4012178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012178).length < 2 ^ (prefixWord ++ tailWord_4012178).sum := by decide
  have hdescent : baseEnd_4012178 < baseStart_4012178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012189 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_4012189 : Nat := 118140960795 + 4012189 * 2 ^ 59
def prefixEnd_4012189 : Nat := 4983230072969 + 3 ^ 40 * 4012189 * 2
def baseEnd_4012189 : Nat := 2060181433682108025785785

theorem tailTrace_4012189 : CollatzResearch.WordTrace tailWord_4012189 prefixEnd_4012189 2060181433682108025785785 := by
  unfold tailWord_4012189
  simp only [CollatzResearch.WordTrace]
  refine ⟨146336554861531955172575621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97557703241021303448383747 146336554861531955172575621)
  ·
    refine ⟨27438104036537241594857929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146336554861531955172575621 27438104036537241594857929)
    ·
      refine ⟨20578578027402931196143447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27438104036537241594857929 20578578027402931196143447)
      ·
        refine ⟨30867867041104396794215171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20578578027402931196143447 30867867041104396794215171)
        ·
          refine ⟨46301800561656595191322757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30867867041104396794215171 46301800561656595191322757)
          ·
            refine ⟨8681587605310611598373017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46301800561656595191322757 8681587605310611598373017)
            ·
              refine ⟨6511190703982958698779763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8681587605310611598373017 6511190703982958698779763)
              ·
                refine ⟨9766786055974438048169645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511190703982958698779763 9766786055974438048169645)
                ·
                  refine ⟨3662544770990414268063617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9766786055974438048169645 3662544770990414268063617)
                  ·
                    refine ⟨2746908578242810701047713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3662544770990414268063617 2746908578242810701047713)
                    ·
                      refine ⟨2060181433682108025785785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746908578242810701047713 2060181433682108025785785)
                      ·
                        rfl

theorem cell23_4012189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_4012189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012189 prefixEnd_4012189 := by exact prefixLift 4012189
  have htrace : WordTrace (prefixWord ++ tailWord_4012189) baseStart_4012189 baseEnd_4012189 := by
    simpa [prefixWord, tailWord_4012189, baseEnd_4012189] using wordTrace_append hprefix tailTrace_4012189
  have hstable : (prefixWord ++ tailWord_4012189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012189).length < 2 ^ (prefixWord ++ tailWord_4012189).sum := by decide
  have hdescent : baseEnd_4012189 < baseStart_4012189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012199 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 1, 6]
def baseStart_4012199 : Nat := 118140960795 + 4012199 * 2 ^ 59
def prefixEnd_4012199 : Nat := 4983230072969 + 3 ^ 40 * 4012199 * 2
def baseEnd_4012199 : Nat := 686728856162884328886913

theorem tailTrace_4012199 : CollatzResearch.WordTrace tailWord_4012199 prefixEnd_4012199 686728856162884328886913 := by
  unfold tailWord_4012199
  simp only [CollatzResearch.WordTrace]
  refine ⟨146336919591495726880439651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97557946394330484586959767 146336919591495726880439651)
  ·
    refine ⟨219505379387243590320659477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146336919591495726880439651 219505379387243590320659477)
    ·
      refine ⟨10289314658777043296280913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219505379387243590320659477 10289314658777043296280913)
      ·
        refine ⟨7716985994082782472210685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10289314658777043296280913 7716985994082782472210685)
        ·
          refine ⟨2893869747781043427079007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7716985994082782472210685 2893869747781043427079007)
          ·
            refine ⟨4340804621671565140618511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893869747781043427079007 4340804621671565140618511)
            ·
              refine ⟨6511206932507347710927767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340804621671565140618511 6511206932507347710927767)
              ·
                refine ⟨9766810398761021566391651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511206932507347710927767 9766810398761021566391651)
                ·
                  refine ⟨14650215598141532349587477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9766810398761021566391651 14650215598141532349587477)
                  ·
                    refine ⟨686728856162884328886913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14650215598141532349587477 686728856162884328886913)
                    ·
                      rfl

theorem cell23_4012199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_4012199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012199 prefixEnd_4012199 := by exact prefixLift 4012199
  have htrace : WordTrace (prefixWord ++ tailWord_4012199) baseStart_4012199 baseEnd_4012199 := by
    simpa [prefixWord, tailWord_4012199, baseEnd_4012199] using wordTrace_append hprefix tailTrace_4012199
  have hstable : (prefixWord ++ tailWord_4012199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012199).length < 2 ^ (prefixWord ++ tailWord_4012199).sum := by decide
  have hdescent : baseEnd_4012199 < baseStart_4012199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012202 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4012202 : Nat := 118140960795 + 4012202 * 2 ^ 59
def prefixEnd_4012202 : Nat := 4983230072969 + 3 ^ 40 * 4012202 * 2
def baseEnd_4012202 : Nat := 2060188108930616474923225

theorem tailTrace_4012202 : CollatzResearch.WordTrace tailWord_4012202 prefixEnd_4012202 2060188108930616474923225 := by
  unfold tailWord_4012202
  simp only [CollatzResearch.WordTrace]
  refine ⟨36584257252621214598199715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97558019340323238928532573 36584257252621214598199715)
  ·
    refine ⟨54876385878931821897299573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36584257252621214598199715 54876385878931821897299573)
    ·
      refine ⟨5144661176149858302871835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54876385878931821897299573 5144661176149858302871835)
      ·
        refine ⟨7716991764224787454307753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144661176149858302871835 7716991764224787454307753)
        ·
          refine ⟨5787743823168590590730815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7716991764224787454307753 5787743823168590590730815)
          ·
            refine ⟨8681615734752885886096223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787743823168590590730815 8681615734752885886096223)
            ·
              refine ⟨13022423602129328829144335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681615734752885886096223 13022423602129328829144335)
              ·
                refine ⟨19533635403193993243716503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13022423602129328829144335 19533635403193993243716503)
                ·
                  refine ⟨29300453104790989865574755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19533635403193993243716503 29300453104790989865574755)
                  ·
                    refine ⟨43950679657186484798362133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29300453104790989865574755 43950679657186484798362133)
                    ·
                      refine ⟨2060188108930616474923225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43950679657186484798362133 2060188108930616474923225)
                      ·
                        rfl

theorem cell23_4012202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4012202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012202 prefixEnd_4012202 := by exact prefixLift 4012202
  have htrace : WordTrace (prefixWord ++ tailWord_4012202) baseStart_4012202 baseEnd_4012202 := by
    simpa [prefixWord, tailWord_4012202, baseEnd_4012202] using wordTrace_append hprefix tailTrace_4012202
  have hstable : (prefixWord ++ tailWord_4012202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012202).length < 2 ^ (prefixWord ++ tailWord_4012202).sum := by decide
  have hdescent : baseEnd_4012202 < baseStart_4012202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012206 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4012206 : Nat := 118140960795 + 4012206 * 2 ^ 59
def prefixEnd_4012206 : Nat := 4983230072969 + 3 ^ 40 * 4012206 * 2
def baseEnd_4012206 : Nat := 2060190162853234459273207

theorem tailTrace_4012206 : CollatzResearch.WordTrace tailWord_4012206 prefixEnd_4012206 2060190162853234459273207 := by
  unfold tailWord_4012206
  simp only [CollatzResearch.WordTrace]
  refine ⟨18292146862808795884493059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97558116601646911383962981 18292146862808795884493059)
  ·
    refine ⟨27438220294213193826739589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18292146862808795884493059 27438220294213193826739589)
    ·
      refine ⟨5144666305164973842513673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27438220294213193826739589 5144666305164973842513673)
      ·
        refine ⟨3858499728873730381885255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5144666305164973842513673 3858499728873730381885255)
        ·
          refine ⟨5787749593310595572827883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858499728873730381885255 5787749593310595572827883)
          ·
            refine ⟨8681624389965893359241825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787749593310595572827883 8681624389965893359241825)
            ·
              refine ⟨6511218292474420019431369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8681624389965893359241825 6511218292474420019431369)
              ·
                refine ⟨4883413719355815014573527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6511218292474420019431369 4883413719355815014573527)
                ·
                  refine ⟨7325120579033722521860291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883413719355815014573527 7325120579033722521860291)
                  ·
                    refine ⟨10987680868550583782790437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7325120579033722521860291 10987680868550583782790437)
                    ·
                      refine ⟨2060190162853234459273207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10987680868550583782790437 2060190162853234459273207)
                      ·
                        rfl

theorem cell23_4012206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4012206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012206 prefixEnd_4012206 := by exact prefixLift 4012206
  have htrace : WordTrace (prefixWord ++ tailWord_4012206) baseStart_4012206 baseEnd_4012206 := by
    simpa [prefixWord, tailWord_4012206, baseEnd_4012206] using wordTrace_append hprefix tailTrace_4012206
  have hstable : (prefixWord ++ tailWord_4012206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012206).length < 2 ^ (prefixWord ++ tailWord_4012206).sum := by decide
  have hdescent : baseEnd_4012206 < baseStart_4012206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012209 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4012209 : Nat := 118140960795 + 4012209 * 2 ^ 59
def prefixEnd_4012209 : Nat := 4983230072969 + 3 ^ 40 * 4012209 * 2
def baseEnd_4012209 : Nat := 2060191703295197947535693

theorem tailTrace_4012209 : CollatzResearch.WordTrace tailWord_4012209 prefixEnd_4012209 2060191703295197947535693 := by
  unfold tailWord_4012209
  simp only [CollatzResearch.WordTrace]
  refine ⟨146337284321459498588303681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97558189547639665725535787 146337284321459498588303681)
  ·
    refine ⟨109752963241094623941227761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146337284321459498588303681 109752963241094623941227761)
    ·
      refine ⟨82314722430820967955920821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109752963241094623941227761 82314722430820967955920821)
      ·
        refine ⟨7717005227889465745867577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82314722430820967955920821 7717005227889465745867577)
        ·
          refine ⟨5787753920917099309400683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7717005227889465745867577 5787753920917099309400683)
          ·
            refine ⟨8681630881375648964101025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787753920917099309400683 8681630881375648964101025)
            ·
              refine ⟨6511223161031736723075769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8681630881375648964101025 6511223161031736723075769)
              ·
                refine ⟨4883417370773802542306827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6511223161031736723075769 4883417370773802542306827)
                ·
                  refine ⟨7325126056160703813460241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883417370773802542306827 7325126056160703813460241)
                  ·
                    refine ⟨5493844542120527860095181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7325126056160703813460241 5493844542120527860095181)
                    ·
                      refine ⟨2060191703295197947535693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5493844542120527860095181 2060191703295197947535693)
                      ·
                        rfl

theorem cell23_4012209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4012209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012209 prefixEnd_4012209 := by exact prefixLift 4012209
  have htrace : WordTrace (prefixWord ++ tailWord_4012209) baseStart_4012209 baseEnd_4012209 := by
    simpa [prefixWord, tailWord_4012209, baseEnd_4012209] using wordTrace_append hprefix tailTrace_4012209
  have hstable : (prefixWord ++ tailWord_4012209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012209).length < 2 ^ (prefixWord ++ tailWord_4012209).sum := by decide
  have hdescent : baseEnd_4012209 < baseStart_4012209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012218 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_4012218 : Nat := 118140960795 + 4012218 * 2 ^ 59
def prefixEnd_4012218 : Nat := 4983230072969 + 3 ^ 40 * 4012218 * 2
def baseEnd_4012218 : Nat := 2060196324621088412323151

theorem tailTrace_4012218 : CollatzResearch.WordTrace tailWord_4012218 prefixEnd_4012218 2060196324621088412323151 := by
  unfold tailWord_4012218
  simp only [CollatzResearch.WordTrace]
  refine ⟨36584403144606723281345327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97558408385617928750254205 36584403144606723281345327)
  ·
    refine ⟨54876604716910084922017991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36584403144606723281345327 54876604716910084922017991)
    ·
      refine ⟨82314907075365127383026987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54876604716910084922017991 82314907075365127383026987)
      ·
        refine ⟨123472360613047691074540481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82314907075365127383026987 123472360613047691074540481)
        ·
          refine ⟨92604270459785768305905361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123472360613047691074540481 92604270459785768305905361)
          ·
            refine ⟨69453202844839326229429021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92604270459785768305905361 69453202844839326229429021)
            ·
              refine ⟨26044951066814747336035883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69453202844839326229429021 26044951066814747336035883)
              ·
                refine ⟨39067426600222121004053825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26044951066814747336035883 39067426600222121004053825)
                ·
                  refine ⟨29300569950166590753040369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39067426600222121004053825 29300569950166590753040369)
                  ·
                    refine ⟨21975427462624943064780277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29300569950166590753040369 21975427462624943064780277)
                    ·
                      refine ⟨2060196324621088412323151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21975427462624943064780277 2060196324621088412323151)
                      ·
                        rfl

theorem cell23_4012218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_4012218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012218 prefixEnd_4012218 := by exact prefixLift 4012218
  have htrace : WordTrace (prefixWord ++ tailWord_4012218) baseStart_4012218 baseEnd_4012218 := by
    simpa [prefixWord, tailWord_4012218, baseEnd_4012218] using wordTrace_append hprefix tailTrace_4012218
  have hstable : (prefixWord ++ tailWord_4012218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012218).length < 2 ^ (prefixWord ++ tailWord_4012218).sum := by decide
  have hdescent : baseEnd_4012218 < baseStart_4012218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012226 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4012226 : Nat := 118140960795 + 4012226 * 2 ^ 59
def prefixEnd_4012226 : Nat := 4983230072969 + 3 ^ 40 * 4012226 * 2
def baseEnd_4012226 : Nat := 2060200432466324381023115

theorem tailTrace_4012226 : CollatzResearch.WordTrace tailWord_4012226 prefixEnd_4012226 2060200432466324381023115 := by
  unfold tailWord_4012226
  simp only [CollatzResearch.WordTrace]
  refine ⟨36584476090599477622918133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97558602908265273661115021 36584476090599477622918133)
  ·
    refine ⟨3429794633493701027148575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36584476090599477622918133 3429794633493701027148575)
    ·
      refine ⟨5144691950240551540722863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3429794633493701027148575 5144691950240551540722863)
      ·
        refine ⟨7717037925360827311084295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144691950240551540722863 7717037925360827311084295)
        ·
          refine ⟨11575556888041240966626443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717037925360827311084295 11575556888041240966626443)
          ·
            refine ⟨17363335332061861449939665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11575556888041240966626443 17363335332061861449939665)
            ·
              refine ⟨13022501499046396087454749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17363335332061861449939665 13022501499046396087454749)
              ·
                refine ⟨4883438062142398532795531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13022501499046396087454749 4883438062142398532795531)
                ·
                  refine ⟨7325157093213597799193297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883438062142398532795531 7325157093213597799193297)
                  ·
                    refine ⟨5493867819910198349394973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7325157093213597799193297 5493867819910198349394973)
                    ·
                      refine ⟨2060200432466324381023115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5493867819910198349394973 2060200432466324381023115)
                      ·
                        rfl

theorem cell23_4012226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4012226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012226 prefixEnd_4012226 := by exact prefixLift 4012226
  have htrace : WordTrace (prefixWord ++ tailWord_4012226) baseStart_4012226 baseEnd_4012226 := by
    simpa [prefixWord, tailWord_4012226, baseEnd_4012226] using wordTrace_append hprefix tailTrace_4012226
  have hstable : (prefixWord ++ tailWord_4012226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012226).length < 2 ^ (prefixWord ++ tailWord_4012226).sum := by decide
  have hdescent : baseEnd_4012226 < baseStart_4012226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012268 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 9]
def baseStart_4012268 : Nat := 118140960795 + 4012268 * 2 ^ 59
def prefixEnd_4012268 : Nat := 4983230072969 + 3 ^ 40 * 4012268 * 2
def baseEnd_4012268 : Nat := 228913555405979246299769

theorem tailTrace_4012268 : CollatzResearch.WordTrace tailWord_4012268 prefixEnd_4012268 228913555405979246299769 := by
  unfold tailWord_4012268
  simp only [CollatzResearch.WordTrace]
  refine ⟨73169718114122875832350729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97559624152163834443134305 73169718114122875832350729)
  ·
    refine ⟨54877288585592156874263047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73169718114122875832350729 54877288585592156874263047)
    ·
      refine ⟨82315932878388235311394571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54877288585592156874263047 82315932878388235311394571)
      ·
        refine ⟨123473899317582352967091857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82315932878388235311394571 123473899317582352967091857)
        ·
          refine ⟨92605424488186764725318893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123473899317582352967091857 92605424488186764725318893)
          ·
            refine ⟨34727034183070036771994585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92605424488186764725318893 34727034183070036771994585)
            ·
              refine ⟨26045275637302527578995939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34727034183070036771994585 26045275637302527578995939)
              ·
                refine ⟨39067913455953791368493909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26045275637302527578995939 39067913455953791368493909)
                ·
                  refine ⟨228913555405979246299769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39067913455953791368493909 228913555405979246299769)
                  ·
                    rfl

theorem cell23_4012268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_4012268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012268 prefixEnd_4012268 := by exact prefixLift 4012268
  have htrace : WordTrace (prefixWord ++ tailWord_4012268) baseStart_4012268 baseEnd_4012268 := by
    simpa [prefixWord, tailWord_4012268, baseEnd_4012268] using wordTrace_append hprefix tailTrace_4012268
  have hstable : (prefixWord ++ tailWord_4012268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012268).length < 2 ^ (prefixWord ++ tailWord_4012268).sum := by decide
  have hdescent : baseEnd_4012268 < baseStart_4012268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012296 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_4012296 : Nat := 118140960795 + 4012296 * 2 ^ 59
def prefixEnd_4012296 : Nat := 4983230072969 + 3 ^ 40 * 4012296 * 2
def baseEnd_4012296 : Nat := 2060236376112139107147793

theorem tailTrace_4012296 : CollatzResearch.WordTrace tailWord_4012296 prefixEnd_4012296 2060236376112139107147793 := by
  unfold tailWord_4012296
  simp only [CollatzResearch.WordTrace]
  refine ⟨73170228736072156223360371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97560304981429541631147161 73170228736072156223360371)
  ·
    refine ⟨109755343104108234335040557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73170228736072156223360371 109755343104108234335040557)
    ·
      refine ⟨41158253664040587875640209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109755343104108234335040557 41158253664040587875640209)
      ·
        refine ⟨30868690248030440906730157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41158253664040587875640209 30868690248030440906730157)
        ·
          refine ⟨11575758843011415340023809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30868690248030440906730157 11575758843011415340023809)
          ·
            refine ⟨8681819132258561505017857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11575758843011415340023809 8681819132258561505017857)
            ·
              refine ⟨6511364349193921128763393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8681819132258561505017857 6511364349193921128763393)
              ·
                refine ⟨4883523261895440846572545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6511364349193921128763393 4883523261895440846572545)
                ·
                  refine ⟨3662642446421580634929409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4883523261895440846572545 3662642446421580634929409)
                  ·
                    refine ⟨2746981834816185476197057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3662642446421580634929409 2746981834816185476197057)
                    ·
                      refine ⟨2060236376112139107147793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2746981834816185476197057 2060236376112139107147793)
                      ·
                        rfl

theorem cell23_4012296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_4012296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012296 prefixEnd_4012296 := by exact prefixLift 4012296
  have htrace : WordTrace (prefixWord ++ tailWord_4012296) baseStart_4012296 baseEnd_4012296 := by
    simpa [prefixWord, tailWord_4012296, baseEnd_4012296] using wordTrace_append hprefix tailTrace_4012296
  have hstable : (prefixWord ++ tailWord_4012296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012296).length < 2 ^ (prefixWord ++ tailWord_4012296).sum := by decide
  have hdescent : baseEnd_4012296 < baseStart_4012296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012302 : List Nat := [4, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_4012302 : Nat := 118140960795 + 4012302 * 2 ^ 59
def prefixEnd_4012302 : Nat := 4983230072969 + 3 ^ 40 * 4012302 * 2
def baseEnd_4012302 : Nat := 228915495221785120408085

theorem tailTrace_4012302 : CollatzResearch.WordTrace tailWord_4012302 prefixEnd_4012302 228915495221785120408085 := by
  unfold tailWord_4012302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18292584538765321933929895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97560450873415050314292773 18292584538765321933929895)
  ·
    refine ⟨27438876808147982900894843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18292584538765321933929895 27438876808147982900894843)
    ·
      refine ⟨41158315212221974351342265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27438876808147982900894843 41158315212221974351342265)
      ·
        refine ⟨30868736409166480763506699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41158315212221974351342265 30868736409166480763506699)
        ·
          refine ⟨46303104613749721145260049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30868736409166480763506699 46303104613749721145260049)
          ·
            refine ⟨34727328460312290858945037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46303104613749721145260049 34727328460312290858945037)
            ·
              refine ⟨13022748172617109072104389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34727328460312290858945037 13022748172617109072104389)
              ·
                refine ⟨2441765282365707951019573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13022748172617109072104389 2441765282365707951019573)
                ·
                  refine ⟨228915495221785120408085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2441765282365707951019573 228915495221785120408085)
                  ·
                    rfl

theorem cell23_4012302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_4012302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012302 prefixEnd_4012302 := by exact prefixLift 4012302
  have htrace : WordTrace (prefixWord ++ tailWord_4012302) baseStart_4012302 baseEnd_4012302 := by
    simpa [prefixWord, tailWord_4012302, baseEnd_4012302] using wordTrace_append hprefix tailTrace_4012302
  have hstable : (prefixWord ++ tailWord_4012302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012302).length < 2 ^ (prefixWord ++ tailWord_4012302).sum := by decide
  have hdescent : baseEnd_4012302 < baseStart_4012302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012372 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_4012372 : Nat := 118140960795 + 4012372 * 2 ^ 59
def prefixEnd_4012372 : Nat := 4983230072969 + 3 ^ 40 * 4012372 * 2
def baseEnd_4012372 : Nat := 2060275400641880809797443

theorem tailTrace_4012372 : CollatzResearch.WordTrace tailWord_4012372 prefixEnd_4012372 2060275400641880809797443 := by
  unfold tailWord_4012372
  simp only [CollatzResearch.WordTrace]
  refine ⟨73171614709934488713243685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97562152946579318284324913 73171614709934488713243685)
  ·
    refine ⟨13719677758112716633733191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73171614709934488713243685 13719677758112716633733191)
    ·
      refine ⟨20579516637169074950599787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13719677758112716633733191 20579516637169074950599787)
      ·
        refine ⟨30869274955753612425899681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20579516637169074950599787 30869274955753612425899681)
        ·
          refine ⟨23151956216815209319424761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30869274955753612425899681 23151956216815209319424761)
          ·
            refine ⟨17363967162611406989568571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23151956216815209319424761 17363967162611406989568571)
            ·
              refine ⟨26045950743917110484352857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17363967162611406989568571 26045950743917110484352857)
              ·
                refine ⟨19534463057937832863264643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26045950743917110484352857 19534463057937832863264643)
                ·
                  refine ⟨29301694586906749294896965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19534463057937832863264643 29301694586906749294896965)
                  ·
                    refine ⟨5494067735045015492793181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29301694586906749294896965 5494067735045015492793181)
                    ·
                      refine ⟨2060275400641880809797443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5494067735045015492793181 2060275400641880809797443)
                      ·
                        rfl

theorem cell23_4012372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_4012372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012372 prefixEnd_4012372 := by exact prefixLift 4012372
  have htrace : WordTrace (prefixWord ++ tailWord_4012372) baseStart_4012372 baseEnd_4012372 := by
    simpa [prefixWord, tailWord_4012372, baseEnd_4012372] using wordTrace_append hprefix tailTrace_4012372
  have hstable : (prefixWord ++ tailWord_4012372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012372).length < 2 ^ (prefixWord ++ tailWord_4012372).sum := by decide
  have hdescent : baseEnd_4012372 < baseStart_4012372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012412 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_4012412 : Nat := 118140960795 + 4012412 * 2 ^ 59
def prefixEnd_4012412 : Nat := 4983230072969 + 3 ^ 40 * 4012412 * 2
def baseEnd_4012412 : Nat := 2060295939868060653297259

theorem tailTrace_4012412 : CollatzResearch.WordTrace tailWord_4012412 prefixEnd_4012412 2060295939868060653297259 := by
  unfold tailWord_4012412
  simp only [CollatzResearch.WordTrace]
  refine ⟨73172344169862032128971745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97563125559816042838628993 73172344169862032128971745)
  ·
    refine ⟨54879258127396524096728809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73172344169862032128971745 54879258127396524096728809)
    ·
      refine ⟨41159443595547393072546607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54879258127396524096728809 41159443595547393072546607)
      ·
        refine ⟨61739165393321089608819911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41159443595547393072546607 61739165393321089608819911)
        ·
          refine ⟨92608748089981634413229867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61739165393321089608819911 92608748089981634413229867)
          ·
            refine ⟨138913122134972451619844801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92608748089981634413229867 138913122134972451619844801)
            ·
              refine ⟨104184841601229338714883601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138913122134972451619844801 104184841601229338714883601)
              ·
                refine ⟨78138631200922004036162701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104184841601229338714883601 78138631200922004036162701)
                ·
                  refine ⟨29301986700345751513561013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78138631200922004036162701 29301986700345751513561013)
                  ·
                    refine ⟨2747061253157414204396345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29301986700345751513561013 2747061253157414204396345)
                    ·
                      refine ⟨2060295939868060653297259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747061253157414204396345 2060295939868060653297259)
                      ·
                        rfl

theorem cell23_4012412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_4012412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012412 prefixEnd_4012412 := by exact prefixLift 4012412
  have htrace : WordTrace (prefixWord ++ tailWord_4012412) baseStart_4012412 baseEnd_4012412 := by
    simpa [prefixWord, tailWord_4012412, baseEnd_4012412] using wordTrace_append hprefix tailTrace_4012412
  have hstable : (prefixWord ++ tailWord_4012412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012412).length < 2 ^ (prefixWord ++ tailWord_4012412).sum := by decide
  have hdescent : baseEnd_4012412 < baseStart_4012412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012452 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_4012452 : Nat := 118140960795 + 4012452 * 2 ^ 59
def prefixEnd_4012452 : Nat := 4983230072969 + 3 ^ 40 * 4012452 * 2
def baseEnd_4012452 : Nat := 686772159698080165599025

theorem tailTrace_4012452 : CollatzResearch.WordTrace tailWord_4012452 prefixEnd_4012452 686772159698080165599025 := by
  unfold tailWord_4012452
  simp only [CollatzResearch.WordTrace]
  refine ⟨73173073629789575544699805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97564098173052767392933073 73173073629789575544699805)
  ·
    refine ⟨27439902611171090829262427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73173073629789575544699805 27439902611171090829262427)
    ·
      refine ⟨41159853916756636243893641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27439902611171090829262427 41159853916756636243893641)
      ·
        refine ⟨30869890437567477182920231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41159853916756636243893641 30869890437567477182920231)
        ·
          refine ⟨46304835656351215774380347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30869890437567477182920231 46304835656351215774380347)
          ·
            refine ⟨69457253484526823661570521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46304835656351215774380347 69457253484526823661570521)
            ·
              refine ⟨52092940113395117746177891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69457253484526823661570521 52092940113395117746177891)
              ·
                refine ⟨78139410170092676619266837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52092940113395117746177891 78139410170092676619266837)
                ·
                  refine ⟨3662784851723094216528133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78139410170092676619266837 3662784851723094216528133)
                  ·
                    refine ⟨686772159698080165599025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3662784851723094216528133 686772159698080165599025)
                    ·
                      rfl

theorem cell23_4012452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_4012452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012452 prefixEnd_4012452 := by exact prefixLift 4012452
  have htrace : WordTrace (prefixWord ++ tailWord_4012452) baseStart_4012452 baseEnd_4012452 := by
    simpa [prefixWord, tailWord_4012452, baseEnd_4012452] using wordTrace_append hprefix tailTrace_4012452
  have hstable : (prefixWord ++ tailWord_4012452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012452).length < 2 ^ (prefixWord ++ tailWord_4012452).sum := by decide
  have hdescent : baseEnd_4012452 < baseStart_4012452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012465 : List Nat := [1, 2, 2, 4, 1, 13]
def baseStart_4012465 : Nat := 118140960795 + 4012465 * 2 ^ 59
def prefixEnd_4012465 : Nat := 4983230072969 + 3 ^ 40 * 4012465 * 2
def baseEnd_4012465 : Nat := 8478696108406374263105

theorem tailTrace_4012465 : CollatzResearch.WordTrace tailWord_4012465 prefixEnd_4012465 8478696108406374263105 := by
  unfold tailWord_4012465
  simp only [CollatzResearch.WordTrace]
  refine ⟨146346621408532054309622849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97564414272354702873081899 146346621408532054309622849)
  ·
    refine ⟨109759966056399040732217137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146346621408532054309622849 109759966056399040732217137)
    ·
      refine ⟨82319974542299280549162853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109759966056399040732217137 82319974542299280549162853)
      ·
        refine ⟨15434995226681115102968035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82319974542299280549162853 15434995226681115102968035)
        ·
          refine ⟨23152492840021672654452053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15434995226681115102968035 23152492840021672654452053)
          ·
            refine ⟨8478696108406374263105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 23152492840021672654452053 8478696108406374263105)
            ·
              rfl

theorem cell23_4012465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 13].length) (baseStart_4012465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012465 prefixEnd_4012465 := by exact prefixLift 4012465
  have htrace : WordTrace (prefixWord ++ tailWord_4012465) baseStart_4012465 baseEnd_4012465 := by
    simpa [prefixWord, tailWord_4012465, baseEnd_4012465] using wordTrace_append hprefix tailTrace_4012465
  have hstable : (prefixWord ++ tailWord_4012465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012465).length < 2 ^ (prefixWord ++ tailWord_4012465).sum := by decide
  have hdescent : baseEnd_4012465 < baseStart_4012465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012495 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 4, 7]
def baseStart_4012495 : Nat := 118140960795 + 4012495 * 2 ^ 59
def prefixEnd_4012495 : Nat := 4983230072969 + 3 ^ 40 * 4012495 * 2
def baseEnd_4012495 : Nat := 686779519587461276186459

theorem tailTrace_4012495 : CollatzResearch.WordTrace tailWord_4012495 prefixEnd_4012495 686779519587461276186459 := by
  unfold tailWord_4012495
  simp only [CollatzResearch.WordTrace]
  refine ⟨146347715598423369433214939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97565143732282246288809959 146347715598423369433214939)
  ·
    refine ⟨219521573397635054149822409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146347715598423369433214939 219521573397635054149822409)
    ·
      refine ⟨164641180048226290612366807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219521573397635054149822409 164641180048226290612366807)
      ·
        refine ⟨246961770072339435918550211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164641180048226290612366807 246961770072339435918550211)
        ·
          refine ⟨370442655108509153877825317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246961770072339435918550211 370442655108509153877825317)
          ·
            refine ⟨69457997832845466352092247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370442655108509153877825317 69457997832845466352092247)
            ·
              refine ⟨104186996749268199528138371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69457997832845466352092247 104186996749268199528138371)
              ·
                refine ⟨156280495123902299292207557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104186996749268199528138371 156280495123902299292207557)
                ·
                  refine ⟨29302592835731681117288917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156280495123902299292207557 29302592835731681117288917)
                  ·
                    refine ⟨686779519587461276186459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29302592835731681117288917 686779519587461276186459)
                    ·
                      rfl

theorem cell23_4012495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_4012495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012495 prefixEnd_4012495 := by exact prefixLift 4012495
  have htrace : WordTrace (prefixWord ++ tailWord_4012495) baseStart_4012495 baseEnd_4012495 := by
    simpa [prefixWord, tailWord_4012495, baseEnd_4012495] using wordTrace_append hprefix tailTrace_4012495
  have hstable : (prefixWord ++ tailWord_4012495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012495).length < 2 ^ (prefixWord ++ tailWord_4012495).sum := by decide
  have hdescent : baseEnd_4012495 < baseStart_4012495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012509 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_4012509 : Nat := 118140960795 + 4012509 * 2 ^ 59
def prefixEnd_4012509 : Nat := 4983230072969 + 3 ^ 40 * 4012509 * 2
def baseEnd_4012509 : Nat := 2060345747491546773784313

theorem tailTrace_4012509 : CollatzResearch.WordTrace tailWord_4012509 prefixEnd_4012509 2060345747491546773784313 := by
  unfold tailWord_4012509
  simp only [CollatzResearch.WordTrace]
  refine ⟨146348226220372649824224581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97565484146915099882816387 146348226220372649824224581)
  ·
    refine ⟨27440292416319871842042109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146348226220372649824224581 27440292416319871842042109)
    ·
      refine ⟨10290109656119951940765791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27440292416319871842042109 10290109656119951940765791)
      ·
        refine ⟨15435164484179927911148687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10290109656119951940765791 15435164484179927911148687)
        ·
          refine ⟨23152746726269891866723031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15435164484179927911148687 23152746726269891866723031)
          ·
            refine ⟨34729120089404837800084547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23152746726269891866723031 34729120089404837800084547)
            ·
              refine ⟨52093680134107256700126821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34729120089404837800084547 52093680134107256700126821)
              ·
                refine ⟨9767565025145110631273779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52093680134107256700126821 9767565025145110631273779)
                ·
                  refine ⟨14651347537717665946910669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9767565025145110631273779 14651347537717665946910669)
                  ·
                    refine ⟨5494255326644124730091501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14651347537717665946910669 5494255326644124730091501)
                    ·
                      refine ⟨2060345747491546773784313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5494255326644124730091501 2060345747491546773784313)
                      ·
                        rfl

theorem cell23_4012509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_4012509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012509 prefixEnd_4012509 := by exact prefixLift 4012509
  have htrace : WordTrace (prefixWord ++ tailWord_4012509) baseStart_4012509 baseEnd_4012509 := by
    simpa [prefixWord, tailWord_4012509, baseEnd_4012509] using wordTrace_append hprefix tailTrace_4012509
  have hstable : (prefixWord ++ tailWord_4012509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012509).length < 2 ^ (prefixWord ++ tailWord_4012509).sum := by decide
  have hdescent : baseEnd_4012509 < baseStart_4012509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012526 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_4012526 : Nat := 118140960795 + 4012526 * 2 ^ 59
def prefixEnd_4012526 : Nat := 4983230072969 + 3 ^ 40 * 4012526 * 2
def baseEnd_4012526 : Nat := 2060354476662673207271735

theorem tailTrace_4012526 : CollatzResearch.WordTrace tailWord_4012526 prefixEnd_4012526 2060354476662673207271735 := by
  unfold tailWord_4012526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293605782663882715949179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97565897507540707818395621 18293605782663882715949179)
  ·
    refine ⟨27440408673995824073923769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18293605782663882715949179 27440408673995824073923769)
    ·
      refine ⟨20580306505496868055442827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27440408673995824073923769 20580306505496868055442827)
      ·
        refine ⟨30870459758245302083164241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20580306505496868055442827 30870459758245302083164241)
        ·
          refine ⟨23152844818683976562373181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30870459758245302083164241 23152844818683976562373181)
          ·
            refine ⟨8682316807006491210889943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23152844818683976562373181 8682316807006491210889943)
            ·
              refine ⟨13023475210509736816334915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682316807006491210889943 13023475210509736816334915)
              ·
                refine ⟨19535212815764605224502373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13023475210509736816334915 19535212815764605224502373)
                ·
                  refine ⟨3662852402955863479594195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19535212815764605224502373 3662852402955863479594195)
                  ·
                    refine ⟨5494278604433795219391293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3662852402955863479594195 5494278604433795219391293)
                    ·
                      refine ⟨2060354476662673207271735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5494278604433795219391293 2060354476662673207271735)
                      ·
                        rfl

theorem cell23_4012526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_4012526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012526 prefixEnd_4012526 := by exact prefixLift 4012526
  have htrace : WordTrace (prefixWord ++ tailWord_4012526) baseStart_4012526 baseEnd_4012526 := by
    simpa [prefixWord, tailWord_4012526, baseEnd_4012526] using wordTrace_append hprefix tailTrace_4012526
  have hstable : (prefixWord ++ tailWord_4012526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012526).length < 2 ^ (prefixWord ++ tailWord_4012526).sum := by decide
  have hdescent : baseEnd_4012526 < baseStart_4012526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012550 : List Nat := [6, 2, 1, 1, 1, 3, 2, 7]
def baseStart_4012550 : Nat := 118140960795 + 4012550 * 2 ^ 59
def prefixEnd_4012550 : Nat := 4983230072969 + 3 ^ 40 * 4012550 * 2
def baseEnd_4012550 : Nat := 76309881488828930124875

theorem tailTrace_4012550 : CollatzResearch.WordTrace tailWord_4012550 prefixEnd_4012550 76309881488828930124875 := by
  unfold tailWord_4012550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4573428800413253557077097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97566481075482742550978069 4573428800413253557077097)
  ·
    refine ⟨3430071600309940167807823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4573428800413253557077097 3430071600309940167807823)
    ·
      refine ⟨5145107400464910251711735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3430071600309940167807823 5145107400464910251711735)
      ·
        refine ⟨7717661100697365377567603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5145107400464910251711735 7717661100697365377567603)
        ·
          refine ⟨11576491651046048066351405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717661100697365377567603 11576491651046048066351405)
          ·
            refine ⟨4341184369142268024881777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11576491651046048066351405 4341184369142268024881777)
            ·
              refine ⟨3255888276856701018661333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4341184369142268024881777 3255888276856701018661333)
              ·
                refine ⟨76309881488828930124875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3255888276856701018661333 76309881488828930124875)
                ·
                  rfl

theorem cell23_4012550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_4012550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012550 prefixEnd_4012550 := by exact prefixLift 4012550
  have htrace : WordTrace (prefixWord ++ tailWord_4012550) baseStart_4012550 baseEnd_4012550 := by
    simpa [prefixWord, tailWord_4012550, baseEnd_4012550] using wordTrace_append hprefix tailTrace_4012550
  have hstable : (prefixWord ++ tailWord_4012550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012550).length < 2 ^ (prefixWord ++ tailWord_4012550).sum := by decide
  have hdescent : baseEnd_4012550 < baseStart_4012550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012552 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_4012552 : Nat := 118140960795 + 4012552 * 2 ^ 59
def prefixEnd_4012552 : Nat := 4983230072969 + 3 ^ 40 * 4012552 * 2
def baseEnd_4012552 : Nat := 2060367827159690105546615

theorem tailTrace_4012552 : CollatzResearch.WordTrace tailWord_4012552 prefixEnd_4012552 2060367827159690105546615 := by
  unfold tailWord_4012552
  simp only [CollatzResearch.WordTrace]
  refine ⟨73174897279608434084019955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97566529706144578778693273 73174897279608434084019955)
  ·
    refine ⟨109762345919412651126029933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73174897279608434084019955 109762345919412651126029933)
    ·
      refine ⟨41160879719779744172261225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109762345919412651126029933 41160879719779744172261225)
      ·
        refine ⟨30870659789834808129195919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41160879719779744172261225 30870659789834808129195919)
        ·
          refine ⟨46305989684752212193793879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30870659789834808129195919 46305989684752212193793879)
          ·
            refine ⟨69458984527128318290690819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46305989684752212193793879 69458984527128318290690819)
            ·
              refine ⟨104188476790692477436036229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69458984527128318290690819 104188476790692477436036229)
              ·
                refine ⟨19535339398254839519256793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104188476790692477436036229 19535339398254839519256793)
                ·
                  refine ⟨14651504548691129639442595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19535339398254839519256793 14651504548691129639442595)
                  ·
                    refine ⟨21977256823036694459163893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14651504548691129639442595 21977256823036694459163893)
                    ·
                      refine ⟨2060367827159690105546615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21977256823036694459163893 2060367827159690105546615)
                      ·
                        rfl

theorem cell23_4012552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_4012552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012552 prefixEnd_4012552 := by exact prefixLift 4012552
  have htrace : WordTrace (prefixWord ++ tailWord_4012552) baseStart_4012552 baseEnd_4012552 := by
    simpa [prefixWord, tailWord_4012552, baseEnd_4012552] using wordTrace_append hprefix tailTrace_4012552
  have hstable : (prefixWord ++ tailWord_4012552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012552).length < 2 ^ (prefixWord ++ tailWord_4012552).sum := by decide
  have hdescent : baseEnd_4012552 < baseStart_4012552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012639 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 3, 6, 2]
def baseStart_4012639 : Nat := 118140960795 + 4012639 * 2 ^ 59
def prefixEnd_4012639 : Nat := 4983230072969 + 3 ^ 40 * 4012639 * 2
def baseEnd_4012639 : Nat := 2060412499976631265158715

theorem tailTrace_4012639 : CollatzResearch.WordTrace tailWord_4012639 prefixEnd_4012639 2060412499976631265158715 := by
  unfold tailWord_4012639
  simp only [CollatzResearch.WordTrace]
  refine ⟨146352967709901682026456971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97568645139934454684304647 146352967709901682026456971)
  ·
    refine ⟨219529451564852523039685457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146352967709901682026456971 219529451564852523039685457)
    ·
      refine ⟨164647088673639392279764093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219529451564852523039685457 164647088673639392279764093)
      ·
        refine ⟨61742658252614772104911535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164647088673639392279764093 61742658252614772104911535)
        ·
          refine ⟨92613987378922158157367303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61742658252614772104911535 92613987378922158157367303)
          ·
            refine ⟨138920981068383237236050955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92613987378922158157367303 138920981068383237236050955)
            ·
              refine ⟨208381471602574855854076433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138920981068383237236050955 208381471602574855854076433)
              ·
                refine ⟨156286103701931141890557325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208381471602574855854076433 156286103701931141890557325)
                ·
                  refine ⟨58607288888224178208958997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156286103701931141890557325 58607288888224178208958997)
                  ·
                    refine ⟨2747216666635508353544953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58607288888224178208958997 2747216666635508353544953)
                    ·
                      refine ⟨2060412499976631265158715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747216666635508353544953 2060412499976631265158715)
                      ·
                        rfl

theorem cell23_4012639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_4012639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012639 prefixEnd_4012639 := by exact prefixLift 4012639
  have htrace : WordTrace (prefixWord ++ tailWord_4012639) baseStart_4012639 baseEnd_4012639 := by
    simpa [prefixWord, tailWord_4012639, baseEnd_4012639] using wordTrace_append hprefix tailTrace_4012639
  have hstable : (prefixWord ++ tailWord_4012639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012639).length < 2 ^ (prefixWord ++ tailWord_4012639).sum := by decide
  have hdescent : baseEnd_4012639 < baseStart_4012639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012649 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 3, 4]
def baseStart_4012649 : Nat := 118140960795 + 4012649 * 2 ^ 59
def prefixEnd_4012649 : Nat := 4983230072969 + 3 ^ 40 * 4012649 * 2
def baseEnd_4012649 : Nat := 686805878261058742011223

theorem tailTrace_4012649 : CollatzResearch.WordTrace tailWord_4012649 prefixEnd_4012649 686805878261058742011223 := by
  unfold tailWord_4012649
  simp only [CollatzResearch.WordTrace]
  refine ⟨146353332439865453734321001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97568888293243635822880667 146353332439865453734321001)
  ·
    refine ⟨109764999329899090300740751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146353332439865453734321001 109764999329899090300740751)
    ·
      refine ⟨164647498994848635451111127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109764999329899090300740751 164647498994848635451111127)
      ·
        refine ⟨246971248492272953176666691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164647498994848635451111127 246971248492272953176666691)
        ·
          refine ⟨370456872738409429765000037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246971248492272953176666691 370456872738409429765000037)
          ·
            refine ⟨69460663638451768080937507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370456872738409429765000037 69460663638451768080937507)
            ·
              refine ⟨104190995457677652121406261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69460663638451768080937507 104190995457677652121406261)
              ·
                refine ⟨9767905824157279886381837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104190995457677652121406261 9767905824157279886381837)
                ·
                  refine ⟨3662964684058979957393189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9767905824157279886381837 3662964684058979957393189)
                  ·
                    refine ⟨686805878261058742011223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3662964684058979957393189 686805878261058742011223)
                    ·
                      rfl

theorem cell23_4012649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 4].length) (baseStart_4012649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012649 prefixEnd_4012649 := by exact prefixLift 4012649
  have htrace : WordTrace (prefixWord ++ tailWord_4012649) baseStart_4012649 baseEnd_4012649 := by
    simpa [prefixWord, tailWord_4012649, baseEnd_4012649] using wordTrace_append hprefix tailTrace_4012649
  have hstable : (prefixWord ++ tailWord_4012649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012649).length < 2 ^ (prefixWord ++ tailWord_4012649).sum := by decide
  have hdescent : baseEnd_4012649 < baseStart_4012649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012676 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_4012676 : Nat := 118140960795 + 4012676 * 2 ^ 59
def prefixEnd_4012676 : Nat := 4983230072969 + 3 ^ 40 * 4012676 * 2
def baseEnd_4012676 : Nat := 2060431498760847620396045

theorem tailTrace_4012676 : CollatzResearch.WordTrace tailWord_4012676 prefixEnd_4012676 2060431498760847620396045 := by
  unfold tailWord_4012676
  simp only [CollatzResearch.WordTrace]
  refine ⟨73177158605383818672776941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97569544807178424897035921 73177158605383818672776941)
  ·
    refine ⟨27441434477018932002291353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73177158605383818672776941 27441434477018932002291353)
    ·
      refine ⟨20581075857764199001718515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27441434477018932002291353 20581075857764199001718515)
      ·
        refine ⟨30871613786646298502577773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20581075857764199001718515 30871613786646298502577773)
        ·
          refine ⟨11576855169992361938466665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30871613786646298502577773 11576855169992361938466665)
          ·
            refine ⟨8682641377494271453849999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11576855169992361938466665 8682641377494271453849999)
            ·
              refine ⟨13023962066241407180774999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682641377494271453849999 13023962066241407180774999)
              ·
                refine ⟨19535943099362110771162499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13023962066241407180774999 19535943099362110771162499)
                ·
                  refine ⟨29303914649043166156743749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19535943099362110771162499 29303914649043166156743749)
                  ·
                    refine ⟨5494483996695593654389453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29303914649043166156743749 5494483996695593654389453)
                    ·
                      refine ⟨2060431498760847620396045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5494483996695593654389453 2060431498760847620396045)
                      ·
                        rfl

theorem cell23_4012676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_4012676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012676 prefixEnd_4012676 := by exact prefixLift 4012676
  have htrace : WordTrace (prefixWord ++ tailWord_4012676) baseStart_4012676 baseEnd_4012676 := by
    simpa [prefixWord, tailWord_4012676, baseEnd_4012676] using wordTrace_append hprefix tailTrace_4012676
  have hstable : (prefixWord ++ tailWord_4012676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012676).length < 2 ^ (prefixWord ++ tailWord_4012676).sum := by decide
  have hdescent : baseEnd_4012676 < baseStart_4012676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012757 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4012757 : Nat := 118140960795 + 4012757 * 2 ^ 59
def prefixEnd_4012757 : Nat := 4983230072969 + 3 ^ 40 * 4012757 * 2
def baseEnd_4012757 : Nat := 2060473090693861803483173

theorem tailTrace_4012757 : CollatzResearch.WordTrace tailWord_4012757 prefixEnd_4012757 2060473090693861803483173 := by
  unfold tailWord_4012757
  simp only [CollatzResearch.WordTrace]
  refine ⟨146357271523474188179252525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97571514348982792119501683 146357271523474188179252525)
  ·
    refine ⟨54883976821302820567219697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146357271523474188179252525 54883976821302820567219697)
    ·
      refine ⟨41162982615977115425414773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54883976821302820567219697 41162982615977115425414773)
      ·
        refine ⟨3859029620247854571132635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41162982615977115425414773 3859029620247854571132635)
        ·
          refine ⟨5788544430371781856698953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859029620247854571132635 5788544430371781856698953)
          ·
            refine ⟨4341408322778836392524215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5788544430371781856698953 4341408322778836392524215)
            ·
              refine ⟨6512112484168254588786323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341408322778836392524215 6512112484168254588786323)
              ·
                refine ⟨9768168726252381883179485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6512112484168254588786323 9768168726252381883179485)
                ·
                  refine ⟨3663063272344643206192307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9768168726252381883179485 3663063272344643206192307)
                  ·
                    refine ⟨5494594908516964809288461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3663063272344643206192307 5494594908516964809288461)
                    ·
                      refine ⟨2060473090693861803483173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5494594908516964809288461 2060473090693861803483173)
                      ·
                        rfl

theorem cell23_4012757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4012757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012757 prefixEnd_4012757 := by exact prefixLift 4012757
  have htrace : WordTrace (prefixWord ++ tailWord_4012757) baseStart_4012757 baseEnd_4012757 := by
    simpa [prefixWord, tailWord_4012757, baseEnd_4012757] using wordTrace_append hprefix tailTrace_4012757
  have hstable : (prefixWord ++ tailWord_4012757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012757).length < 2 ^ (prefixWord ++ tailWord_4012757).sum := by decide
  have hdescent : baseEnd_4012757 < baseStart_4012757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012759 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_4012759 : Nat := 118140960795 + 4012759 * 2 ^ 59
def prefixEnd_4012759 : Nat := 4983230072969 + 3 ^ 40 * 4012759 * 2
def baseEnd_4012759 : Nat := 2060474117655170795658163

theorem tailTrace_4012759 : CollatzResearch.WordTrace tailWord_4012759 prefixEnd_4012759 2060474117655170795658163 := by
  unfold tailWord_4012759
  simp only [CollatzResearch.WordTrace]
  refine ⟨146357344469466942520825331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97571562979644628347216887 146357344469466942520825331)
  ·
    refine ⟨219536016704200413781237997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146357344469466942520825331 219536016704200413781237997)
    ·
      refine ⟨82326006264075155167964249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219536016704200413781237997 82326006264075155167964249)
      ·
        refine ⟨61744504698056366375973187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82326006264075155167964249 61744504698056366375973187)
        ·
          refine ⟨92616757047084549563959781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61744504698056366375973187 92616757047084549563959781)
          ·
            refine ⟨17365641946328353043242459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92616757047084549563959781 17365641946328353043242459)
            ·
              refine ⟨26048462919492529564863689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17365641946328353043242459 26048462919492529564863689)
              ·
                refine ⟨19536347189619397173647767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26048462919492529564863689 19536347189619397173647767)
                ·
                  refine ⟨29304520784429095760471651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19536347189619397173647767 29304520784429095760471651)
                  ·
                    refine ⟨43956781176643643640707477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29304520784429095760471651 43956781176643643640707477)
                    ·
                      refine ⟨2060474117655170795658163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43956781176643643640707477 2060474117655170795658163)
                      ·
                        rfl

theorem cell23_4012759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_4012759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012759 prefixEnd_4012759 := by exact prefixLift 4012759
  have htrace : WordTrace (prefixWord ++ tailWord_4012759) baseStart_4012759 baseEnd_4012759 := by
    simpa [prefixWord, tailWord_4012759, baseEnd_4012759] using wordTrace_append hprefix tailTrace_4012759
  have hstable : (prefixWord ++ tailWord_4012759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012759).length < 2 ^ (prefixWord ++ tailWord_4012759).sum := by decide
  have hdescent : baseEnd_4012759 < baseStart_4012759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012769 : List Nat := [1, 2, 3, 1, 4, 1, 1, 10]
def baseStart_4012769 : Nat := 118140960795 + 4012769 * 2 ^ 59
def prefixEnd_4012769 : Nat := 4983230072969 + 3 ^ 40 * 4012769 * 2
def baseEnd_4012769 : Nat := 76314046387470953945671

theorem tailTrace_4012769 : CollatzResearch.WordTrace tailWord_4012769 prefixEnd_4012769 76314046387470953945671 := by
  unfold tailWord_4012769
  simp only [CollatzResearch.WordTrace]
  refine ⟨146357709199430714228689361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97571806132953809485792907 146357709199430714228689361)
  ·
    refine ⟨109768281899573035671517021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146357709199430714228689361 109768281899573035671517021)
    ·
      refine ⟨41163105712339888376818883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109768281899573035671517021 41163105712339888376818883)
      ·
        refine ⟨61744658568509832565228325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41163105712339888376818883 61744658568509832565228325)
        ·
          refine ⟨11577123481595593605980311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61744658568509832565228325 11577123481595593605980311)
          ·
            refine ⟨17365685222393390408970467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11577123481595593605980311 17365685222393390408970467)
            ·
              refine ⟨26048527833590085613455701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17365685222393390408970467 26048527833590085613455701)
              ·
                refine ⟨76314046387470953945671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26048527833590085613455701 76314046387470953945671)
                ·
                  rfl

theorem cell23_4012769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 10].length) (baseStart_4012769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012769 prefixEnd_4012769 := by exact prefixLift 4012769
  have htrace : WordTrace (prefixWord ++ tailWord_4012769) baseStart_4012769 baseEnd_4012769 := by
    simpa [prefixWord, tailWord_4012769, baseEnd_4012769] using wordTrace_append hprefix tailTrace_4012769
  have hstable : (prefixWord ++ tailWord_4012769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012769).length < 2 ^ (prefixWord ++ tailWord_4012769).sum := by decide
  have hdescent : baseEnd_4012769 < baseStart_4012769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012773 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_4012773 : Nat := 118140960795 + 4012773 * 2 ^ 59
def prefixEnd_4012773 : Nat := 4983230072969 + 3 ^ 40 * 4012773 * 2
def baseEnd_4012773 : Nat := 686827102128111246961033

theorem tailTrace_4012773 : CollatzResearch.WordTrace tailWord_4012773 prefixEnd_4012773 686827102128111246961033 := by
  unfold tailWord_4012773
  simp only [CollatzResearch.WordTrace]
  refine ⟨146357855091416222911834973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97571903394277481941223315 146357855091416222911834973)
  ·
    refine ⟨54884195659281083591938115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146357855091416222911834973 54884195659281083591938115)
    ·
      refine ⟨82326293488921625387907173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54884195659281083591938115 82326293488921625387907173)
      ·
        refine ⟨15436180029172804760232595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82326293488921625387907173 15436180029172804760232595)
        ·
          refine ⟨23154270043759207140348893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15436180029172804760232595 23154270043759207140348893)
          ·
            refine ⟨8682851266409702677630835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23154270043759207140348893 8682851266409702677630835)
            ·
              refine ⟨13024276899614554016446253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682851266409702677630835 13024276899614554016446253)
              ·
                refine ⟨4884103837355457756167345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13024276899614554016446253 4884103837355457756167345)
                ·
                  refine ⟨3663077878016593317125509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4884103837355457756167345 3663077878016593317125509)
                  ·
                    refine ⟨686827102128111246961033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3663077878016593317125509 686827102128111246961033)
                    ·
                      rfl

theorem cell23_4012773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_4012773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012773 prefixEnd_4012773 := by exact prefixLift 4012773
  have htrace : WordTrace (prefixWord ++ tailWord_4012773) baseStart_4012773 baseEnd_4012773 := by
    simpa [prefixWord, tailWord_4012773, baseEnd_4012773] using wordTrace_append hprefix tailTrace_4012773
  have hstable : (prefixWord ++ tailWord_4012773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012773).length < 2 ^ (prefixWord ++ tailWord_4012773).sum := by decide
  have hdescent : baseEnd_4012773 < baseStart_4012773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012783 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 3]
def baseStart_4012783 : Nat := 118140960795 + 4012783 * 2 ^ 59
def prefixEnd_4012783 : Nat := 4983230072969 + 3 ^ 40 * 4012783 * 2
def baseEnd_4012783 : Nat := 2060486441190878701758053

theorem tailTrace_4012783 : CollatzResearch.WordTrace tailWord_4012783 prefixEnd_4012783 2060486441190878701758053 := by
  unfold tailWord_4012783
  simp only [CollatzResearch.WordTrace]
  refine ⟨146358219821379994619699003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97572146547586663079799335 146358219821379994619699003)
  ·
    refine ⟨219537329732069991929548505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146358219821379994619699003 219537329732069991929548505)
    ·
      refine ⟨164652997299052493947161379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219537329732069991929548505 164652997299052493947161379)
      ·
        refine ⟨246979495948578740920742069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164652997299052493947161379 246979495948578740920742069)
        ·
          refine ⟨23154327745179256961319569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246979495948578740920742069 23154327745179256961319569)
          ·
            refine ⟨17365745808884442720989677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23154327745179256961319569 17365745808884442720989677)
            ·
              refine ⟨6512154678331666020371129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17365745808884442720989677 6512154678331666020371129)
              ·
                refine ⟨4884116008748749515278347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6512154678331666020371129 4884116008748749515278347)
                ·
                  refine ⟨7326174013123124272917521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884116008748749515278347 7326174013123124272917521)
                  ·
                    refine ⟨5494630509842343204688141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7326174013123124272917521 5494630509842343204688141)
                    ·
                      refine ⟨2060486441190878701758053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5494630509842343204688141 2060486441190878701758053)
                      ·
                        rfl

theorem cell23_4012783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 3].length) (baseStart_4012783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012783 prefixEnd_4012783 := by exact prefixLift 4012783
  have htrace : WordTrace (prefixWord ++ tailWord_4012783) baseStart_4012783 baseEnd_4012783 := by
    simpa [prefixWord, tailWord_4012783, baseEnd_4012783] using wordTrace_append hprefix tailTrace_4012783
  have hstable : (prefixWord ++ tailWord_4012783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012783).length < 2 ^ (prefixWord ++ tailWord_4012783).sum := by decide
  have hdescent : baseEnd_4012783 < baseStart_4012783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012796 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_4012796 : Nat := 118140960795 + 4012796 * 2 ^ 59
def prefixEnd_4012796 : Nat := 4983230072969 + 3 ^ 40 * 4012796 * 2
def baseEnd_4012796 : Nat := 2060493116439387150895493

theorem tailTrace_4012796 : CollatzResearch.WordTrace tailWord_4012796 prefixEnd_4012796 2060493116439387150895493 := by
  unfold tailWord_4012796
  simp only [CollatzResearch.WordTrace]
  refine ⟨73179346985166448919961121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97572462646888598559948161 73179346985166448919961121)
  ·
    refine ⟨54884510238874836689970841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73179346985166448919961121 54884510238874836689970841)
    ·
      refine ⟨41163382679156127517478131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54884510238874836689970841 41163382679156127517478131)
      ·
        refine ⟨61745074018734191276217197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41163382679156127517478131 61745074018734191276217197)
        ·
          refine ⟨23154402757025321728581449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61745074018734191276217197 23154402757025321728581449)
          ·
            refine ⟨17365802067768991296436087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23154402757025321728581449 17365802067768991296436087)
            ·
              refine ⟨26048703101653486944654131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17365802067768991296436087 26048703101653486944654131)
              ·
                refine ⟨39073054652480230416981197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26048703101653486944654131 39073054652480230416981197)
                ·
                  refine ⟨14652395494680086406367949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39073054652480230416981197 14652395494680086406367949)
                  ·
                    refine ⟨5494648310505032402387981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14652395494680086406367949 5494648310505032402387981)
                    ·
                      refine ⟨2060493116439387150895493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5494648310505032402387981 2060493116439387150895493)
                      ·
                        rfl

theorem cell23_4012796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_4012796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012796 prefixEnd_4012796 := by exact prefixLift 4012796
  have htrace : WordTrace (prefixWord ++ tailWord_4012796) baseStart_4012796 baseEnd_4012796 := by
    simpa [prefixWord, tailWord_4012796, baseEnd_4012796] using wordTrace_append hprefix tailTrace_4012796
  have hstable : (prefixWord ++ tailWord_4012796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012796).length < 2 ^ (prefixWord ++ tailWord_4012796).sum := by decide
  have hdescent : baseEnd_4012796 < baseStart_4012796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012809 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_4012809 : Nat := 118140960795 + 4012809 * 2 ^ 59
def prefixEnd_4012809 : Nat := 4983230072969 + 3 ^ 40 * 4012809 * 2
def baseEnd_4012809 : Nat := 2060499791687895600032933

theorem tailTrace_4012809 : CollatzResearch.WordTrace tailWord_4012809 prefixEnd_4012809 2060499791687895600032933 := by
  unfold tailWord_4012809
  simp only [CollatzResearch.WordTrace]
  refine ⟨146359168119285801060145481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97572778746190534040096987 146359168119285801060145481)
  ·
    refine ⟨109769376089464350795109111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146359168119285801060145481 109769376089464350795109111)
    ·
      refine ⟨164654064134196526192663667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109769376089464350795109111 164654064134196526192663667)
      ·
        refine ⟨246981096201294789288995501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164654064134196526192663667 246981096201294789288995501)
        ·
          refine ⟨92617911075485545983373313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246981096201294789288995501 92617911075485545983373313)
          ·
            refine ⟨69463433306614159487529985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92617911075485545983373313 69463433306614159487529985)
            ·
              refine ⟨52097574979960619615647489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69463433306614159487529985 52097574979960619615647489)
              ·
                refine ⟨39073181234970464711735617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52097574979960619615647489 39073181234970464711735617)
                ·
                  refine ⟨29304885926227848533801713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39073181234970464711735617 29304885926227848533801713)
                  ·
                    refine ⟨21978664444670886400351285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29304885926227848533801713 21978664444670886400351285)
                    ·
                      refine ⟨2060499791687895600032933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21978664444670886400351285 2060499791687895600032933)
                      ·
                        rfl

theorem cell23_4012809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_4012809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012809 prefixEnd_4012809 := by exact prefixLift 4012809
  have htrace : WordTrace (prefixWord ++ tailWord_4012809) baseStart_4012809 baseEnd_4012809 := by
    simpa [prefixWord, tailWord_4012809, baseEnd_4012809] using wordTrace_append hprefix tailTrace_4012809
  have hstable : (prefixWord ++ tailWord_4012809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012809).length < 2 ^ (prefixWord ++ tailWord_4012809).sum := by decide
  have hdescent : baseEnd_4012809 < baseStart_4012809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012819 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 4]
def baseStart_4012819 : Nat := 118140960795 + 4012819 * 2 ^ 59
def prefixEnd_4012819 : Nat := 4983230072969 + 3 ^ 40 * 4012819 * 2
def baseEnd_4012819 : Nat := 2060504926494440560907887

theorem tailTrace_4012819 : CollatzResearch.WordTrace tailWord_4012819 prefixEnd_4012819 2060504926494440560907887 := by
  unfold tailWord_4012819
  simp only [CollatzResearch.WordTrace]
  refine ⟨146359532849249572768009511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97573021899499715178673007 146359532849249572768009511)
  ·
    refine ⟨219539299273874359152014267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146359532849249572768009511 219539299273874359152014267)
    ·
      refine ⟨329308948910811538728021401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219539299273874359152014267 329308948910811538728021401)
      ·
        refine ⟨246981711683108654046016051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329308948910811538728021401 246981711683108654046016051)
        ·
          refine ⟨370472567524662981069024077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246981711683108654046016051 370472567524662981069024077)
          ·
            refine ⟨138927212821748617900884029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370472567524662981069024077 138927212821748617900884029)
            ·
              refine ⟨52097704808155731712831511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138927212821748617900884029 52097704808155731712831511)
              ·
                refine ⟨78146557212233597569247267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52097704808155731712831511 78146557212233597569247267)
                ·
                  refine ⟨117219835818350396353870901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78146557212233597569247267 117219835818350396353870901)
                  ·
                    refine ⟨10989359607970349658175397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117219835818350396353870901 10989359607970349658175397)
                    ·
                      refine ⟨2060504926494440560907887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10989359607970349658175397 2060504926494440560907887)
                      ·
                        rfl

theorem cell23_4012819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_4012819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012819 prefixEnd_4012819 := by exact prefixLift 4012819
  have htrace : WordTrace (prefixWord ++ tailWord_4012819) baseStart_4012819 baseEnd_4012819 := by
    simpa [prefixWord, tailWord_4012819, baseEnd_4012819] using wordTrace_append hprefix tailTrace_4012819
  have hstable : (prefixWord ++ tailWord_4012819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012819).length < 2 ^ (prefixWord ++ tailWord_4012819).sum := by decide
  have hdescent : baseEnd_4012819 < baseStart_4012819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012840 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_4012840 : Nat := 118140960795 + 4012840 * 2 ^ 59
def prefixEnd_4012840 : Nat := 4983230072969 + 3 ^ 40 * 4012840 * 2
def baseEnd_4012840 : Nat := 2060515709588184978745291

theorem tailTrace_4012840 : CollatzResearch.WordTrace tailWord_4012840 prefixEnd_4012840 2060515709588184978745291 := by
  unfold tailWord_4012840
  simp only [CollatzResearch.WordTrace]
  refine ⟨73180149391086746677261987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97573532521448995569682649 73180149391086746677261987)
  ·
    refine ⟨109770224086630120015892981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73180149391086746677261987 109770224086630120015892981)
    ·
      refine ⟨10290958508121573751489967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109770224086630120015892981 10290958508121573751489967)
      ·
        refine ⟨15436437762182360627234951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10290958508121573751489967 15436437762182360627234951)
        ·
          refine ⟨23154656643273540940852427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15436437762182360627234951 23154656643273540940852427)
          ·
            refine ⟨34731984964910311411278641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23154656643273540940852427 34731984964910311411278641)
            ·
              refine ⟨26048988723682733558458981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34731984964910311411278641 26048988723682733558458981)
              ·
                refine ⟨4884185385690512542211059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26048988723682733558458981 4884185385690512542211059)
                ·
                  refine ⟨7326278078535768813316589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884185385690512542211059 7326278078535768813316589)
                  ·
                    refine ⟨2747354279450913304993721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7326278078535768813316589 2747354279450913304993721)
                    ·
                      refine ⟨2060515709588184978745291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747354279450913304993721 2060515709588184978745291)
                      ·
                        rfl

theorem cell23_4012840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_4012840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012840 prefixEnd_4012840 := by exact prefixLift 4012840
  have htrace : WordTrace (prefixWord ++ tailWord_4012840) baseStart_4012840 baseEnd_4012840 := by
    simpa [prefixWord, tailWord_4012840, baseEnd_4012840] using wordTrace_append hprefix tailTrace_4012840
  have hstable : (prefixWord ++ tailWord_4012840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012840).length < 2 ^ (prefixWord ++ tailWord_4012840).sum := by decide
  have hdescent : baseEnd_4012840 < baseStart_4012840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012869 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_4012869 : Nat := 118140960795 + 4012869 * 2 ^ 59
def prefixEnd_4012869 : Nat := 4983230072969 + 3 ^ 40 * 4012869 * 2
def baseEnd_4012869 : Nat := 2060530600527165365282657

theorem tailTrace_4012869 : CollatzResearch.WordTrace tailWord_4012869 prefixEnd_4012869 2060530600527165365282657 := by
  unfold tailWord_4012869
  simp only [CollatzResearch.WordTrace]
  refine ⟨146361356499068431307329661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97574237666045620871553107 146361356499068431307329661)
  ·
    refine ⟨54885508687150661740248623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146361356499068431307329661 54885508687150661740248623)
    ·
      refine ⟨82328263030725992610372935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54885508687150661740248623 82328263030725992610372935)
      ·
        refine ⟨123492394546088988915559403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82328263030725992610372935 123492394546088988915559403)
        ·
          refine ⟨185238591819133483373339105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123492394546088988915559403 185238591819133483373339105)
          ·
            refine ⟨138928943864350112530004329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185238591819133483373339105 138928943864350112530004329)
            ·
              refine ⟨104196707898262584397503247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138928943864350112530004329 104196707898262584397503247)
              ·
                refine ⟨156295061847393876596254871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104196707898262584397503247 156295061847393876596254871)
                ·
                  refine ⟨234442592771090814894382307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156295061847393876596254871 234442592771090814894382307)
                  ·
                    refine ⟨351663889156636222341573461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234442592771090814894382307 351663889156636222341573461)
                    ·
                      refine ⟨2060530600527165365282657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 351663889156636222341573461 2060530600527165365282657)
                      ·
                        rfl

theorem cell23_4012869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_4012869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012869 prefixEnd_4012869 := by exact prefixLift 4012869
  have htrace : WordTrace (prefixWord ++ tailWord_4012869) baseStart_4012869 baseEnd_4012869 := by
    simpa [prefixWord, tailWord_4012869, baseEnd_4012869] using wordTrace_append hprefix tailTrace_4012869
  have hstable : (prefixWord ++ tailWord_4012869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012869).length < 2 ^ (prefixWord ++ tailWord_4012869).sum := by decide
  have hdescent : baseEnd_4012869 < baseStart_4012869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012876 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 7]
def baseStart_4012876 : Nat := 118140960795 + 4012876 * 2 ^ 59
def prefixEnd_4012876 : Nat := 4983230072969 + 3 ^ 40 * 4012876 * 2
def baseEnd_4012876 : Nat := 228948243876860759766125

theorem tailTrace_4012876 : CollatzResearch.WordTrace tailWord_4012876 prefixEnd_4012876 228948243876860759766125 := by
  unfold tailWord_4012876
  simp only [CollatzResearch.WordTrace]
  refine ⟨73180805905021535751417241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97574407873362047668556321 73180805905021535751417241)
  ·
    refine ⟨54885604428766151813562931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73180805905021535751417241 54885604428766151813562931)
    ·
      refine ⟨82328406643149227720344397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54885604428766151813562931 82328406643149227720344397)
      ·
        refine ⟨30873152491180960395129149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82328406643149227720344397 30873152491180960395129149)
        ·
          refine ⟨11577432184192860148173431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30873152491180960395129149 11577432184192860148173431)
          ·
            refine ⟨17366148276289290222260147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11577432184192860148173431 17366148276289290222260147)
            ·
              refine ⟨26049222414433935333390221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17366148276289290222260147 26049222414433935333390221)
              ·
                refine ⟨9768458405412725750021333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26049222414433935333390221 9768458405412725750021333)
                ·
                  refine ⟨228948243876860759766125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9768458405412725750021333 228948243876860759766125)
                  ·
                    rfl

theorem cell23_4012876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_4012876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012876 prefixEnd_4012876 := by exact prefixLift 4012876
  have htrace : WordTrace (prefixWord ++ tailWord_4012876) baseStart_4012876 baseEnd_4012876 := by
    simpa [prefixWord, tailWord_4012876, baseEnd_4012876] using wordTrace_append hprefix tailTrace_4012876
  have hstable : (prefixWord ++ tailWord_4012876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012876).length < 2 ^ (prefixWord ++ tailWord_4012876).sum := by decide
  have hdescent : baseEnd_4012876 < baseStart_4012876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012963 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 3]
def baseStart_4012963 : Nat := 118140960795 + 4012963 * 2 ^ 59
def prefixEnd_4012963 : Nat := 4983230072969 + 3 ^ 40 * 4012963 * 2
def baseEnd_4012963 : Nat := 2060578867708687997507225

theorem tailTrace_4012963 : CollatzResearch.WordTrace tailWord_4012963 prefixEnd_4012963 2060578867708687997507225 := by
  unfold tailWord_4012963
  simp only [CollatzResearch.WordTrace]
  refine ⟨146364784960727885361251543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97576523307151923574167695 146364784960727885361251543)
  ·
    refine ⟨219547177441091828041877315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146364784960727885361251543 219547177441091828041877315)
    ·
      refine ⟨329320766161637742062815973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219547177441091828041877315 329320766161637742062815973)
      ·
        refine ⟨61747643655307076636777995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329320766161637742062815973 61747643655307076636777995)
        ·
          refine ⟨92621465482960614955166993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61747643655307076636777995 92621465482960614955166993)
          ·
            refine ⟨69466099112220461216375245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92621465482960614955166993 69466099112220461216375245)
            ·
              refine ⟨26049787167082672956140717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69466099112220461216375245 26049787167082672956140717)
              ·
                refine ⟨9768670187656002358552769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26049787167082672956140717 9768670187656002358552769)
                ·
                  refine ⟨7326502640742001768914577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9768670187656002358552769 7326502640742001768914577)
                  ·
                    refine ⟨5494876980556501326685933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7326502640742001768914577 5494876980556501326685933)
                    ·
                      refine ⟨2060578867708687997507225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5494876980556501326685933 2060578867708687997507225)
                      ·
                        rfl

theorem cell23_4012963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_4012963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012963 prefixEnd_4012963 := by exact prefixLift 4012963
  have htrace : WordTrace (prefixWord ++ tailWord_4012963) baseStart_4012963 baseEnd_4012963 := by
    simpa [prefixWord, tailWord_4012963, baseEnd_4012963] using wordTrace_append hprefix tailTrace_4012963
  have hstable : (prefixWord ++ tailWord_4012963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012963).length < 2 ^ (prefixWord ++ tailWord_4012963).sum := by decide
  have hdescent : baseEnd_4012963 < baseStart_4012963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4012986 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_4012986 : Nat := 118140960795 + 4012986 * 2 ^ 59
def prefixEnd_4012986 : Nat := 4983230072969 + 3 ^ 40 * 4012986 * 2
def baseEnd_4012986 : Nat := 2060590677763741407519619

theorem tailTrace_4012986 : CollatzResearch.WordTrace tailWord_4012986 prefixEnd_4012986 2060590677763741407519619 := by
  unfold tailWord_4012986
  simp only [CollatzResearch.WordTrace]
  refine ⟨36591405959911140072334703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97577082559763040192892541 36591405959911140072334703)
  ·
    refine ⟨54887108939866710108502055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36591405959911140072334703 54887108939866710108502055)
    ·
      refine ⟨82330663409800065162753083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54887108939866710108502055 82330663409800065162753083)
      ·
        refine ⟨123495995114700097744129625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82330663409800065162753083 123495995114700097744129625)
        ·
          refine ⟨92621996336025073308097219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123495995114700097744129625 92621996336025073308097219)
          ·
            refine ⟨138932994504037609962145829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92621996336025073308097219 138932994504037609962145829)
            ·
              refine ⟨26049936469507051867902343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138932994504037609962145829 26049936469507051867902343)
              ·
                refine ⟨39074904704260577801853515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26049936469507051867902343 39074904704260577801853515)
                ·
                  refine ⟨58612357056390866702780273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39074904704260577801853515 58612357056390866702780273)
                  ·
                    refine ⟨43959267792293150027085205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58612357056390866702780273 43959267792293150027085205)
                    ·
                      refine ⟨2060590677763741407519619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43959267792293150027085205 2060590677763741407519619)
                      ·
                        rfl

theorem cell23_4012986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_4012986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4012986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4012986 prefixEnd_4012986 := by exact prefixLift 4012986
  have htrace : WordTrace (prefixWord ++ tailWord_4012986) baseStart_4012986 baseEnd_4012986 := by
    simpa [prefixWord, tailWord_4012986, baseEnd_4012986] using wordTrace_append hprefix tailTrace_4012986
  have hstable : (prefixWord ++ tailWord_4012986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4012986).length < 2 ^ (prefixWord ++ tailWord_4012986).sum := by decide
  have hdescent : baseEnd_4012986 < baseStart_4012986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4012986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013014 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_4013014 : Nat := 118140960795 + 4013014 * 2 ^ 59
def prefixEnd_4013014 : Nat := 4983230072969 + 3 ^ 40 * 4013014 * 2
def baseEnd_4013014 : Nat := 2060605055222067297969491

theorem tailTrace_4013014 : CollatzResearch.WordTrace tailWord_4013014 prefixEnd_4013014 2060605055222067297969491 := by
  unfold tailWord_4013014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9147915317721445066959881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97577763389028747380905397 9147915317721445066959881)
  ·
    refine ⟨6860936488291083800219911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9147915317721445066959881 6860936488291083800219911)
    ·
      refine ⟨10291404732436625700329867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6860936488291083800219911 10291404732436625700329867)
      ·
        refine ⟨15437107098654938550494801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10291404732436625700329867 15437107098654938550494801)
        ·
          refine ⟨11577830323991203912871101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15437107098654938550494801 11577830323991203912871101)
          ·
            refine ⟨4341686371496701467326663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11577830323991203912871101 4341686371496701467326663)
            ·
              refine ⟨6512529557245052200989995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341686371496701467326663 6512529557245052200989995)
              ·
                refine ⟨9768794335867578301484993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6512529557245052200989995 9768794335867578301484993)
                ·
                  refine ⟨7326595751900683726113745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9768794335867578301484993 7326595751900683726113745)
                  ·
                    refine ⟨5494946813925512794585309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7326595751900683726113745 5494946813925512794585309)
                    ·
                      refine ⟨2060605055222067297969491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5494946813925512794585309 2060605055222067297969491)
                      ·
                        rfl

theorem cell23_4013014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_4013014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013014 prefixEnd_4013014 := by exact prefixLift 4013014
  have htrace : WordTrace (prefixWord ++ tailWord_4013014) baseStart_4013014 baseEnd_4013014 := by
    simpa [prefixWord, tailWord_4013014, baseEnd_4013014] using wordTrace_append hprefix tailTrace_4013014
  have hstable : (prefixWord ++ tailWord_4013014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013014).length < 2 ^ (prefixWord ++ tailWord_4013014).sum := by decide
  have hdescent : baseEnd_4013014 < baseStart_4013014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013033 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 3, 8, 2]
def baseStart_4013033 : Nat := 118140960795 + 4013033 * 2 ^ 59
def prefixEnd_4013033 : Nat := 4983230072969 + 3 ^ 40 * 4013033 * 2
def baseEnd_4013033 : Nat := 2060614811354502723631903

theorem tailTrace_4013033 : CollatzResearch.WordTrace tailWord_4013033 prefixEnd_4013033 2060614811354502723631903 := by
  unfold tailWord_4013033
  simp only [CollatzResearch.WordTrace]
  refine ⟨146367338070474287316299753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97578225380316191544199835 146367338070474287316299753)
  ·
    refine ⟨109775503552855715487224815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146367338070474287316299753 109775503552855715487224815)
    ·
      refine ⟨164663255329283573230837223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109775503552855715487224815 164663255329283573230837223)
      ·
        refine ⟨246994882993925359846255835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164663255329283573230837223 246994882993925359846255835)
        ·
          refine ⟨370492324490888039769383753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246994882993925359846255835 370492324490888039769383753)
          ·
            refine ⟨277869243368166029827037815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370492324490888039769383753 277869243368166029827037815)
            ·
              refine ⟨416803865052249044740556723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277869243368166029827037815 416803865052249044740556723)
              ·
                refine ⟨625205797578373567110835085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416803865052249044740556723 625205797578373567110835085)
                ·
                  refine ⟨234452174091890087666563157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625205797578373567110835085 234452174091890087666563157)
                  ·
                    refine ⟨2747486415139336964842537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 234452174091890087666563157 2747486415139336964842537)
                    ·
                      refine ⟨2060614811354502723631903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747486415139336964842537 2060614811354502723631903)
                      ·
                        rfl

theorem cell23_4013033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 8, 2].length) (baseStart_4013033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013033 prefixEnd_4013033 := by exact prefixLift 4013033
  have htrace : WordTrace (prefixWord ++ tailWord_4013033) baseStart_4013033 baseEnd_4013033 := by
    simpa [prefixWord, tailWord_4013033, baseEnd_4013033] using wordTrace_append hprefix tailTrace_4013033
  have hstable : (prefixWord ++ tailWord_4013033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013033).length < 2 ^ (prefixWord ++ tailWord_4013033).sum := by decide
  have hdescent : baseEnd_4013033 < baseStart_4013033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013063 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_4013063 : Nat := 118140960795 + 4013063 * 2 ^ 59
def prefixEnd_4013063 : Nat := 4983230072969 + 3 ^ 40 * 4013063 * 2
def baseEnd_4013063 : Nat := 2060630215774137606256765

theorem tailTrace_4013063 : CollatzResearch.WordTrace tailWord_4013063 prefixEnd_4013063 2060630215774137606256765 := by
  unfold tailWord_4013063
  simp only [CollatzResearch.WordTrace]
  refine ⟨146368432260365602439891843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97578954840243734959927895 146368432260365602439891843)
  ·
    refine ⟨219552648390548403659837765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146368432260365602439891843 219552648390548403659837765)
    ·
      refine ⟨41166121573227825686219581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219552648390548403659837765 41166121573227825686219581)
      ·
        refine ⟨15437295589960434632332343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41166121573227825686219581 15437295589960434632332343)
        ·
          refine ⟨23155943384940651948498515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15437295589960434632332343 23155943384940651948498515)
          ·
            refine ⟨34733915077410977922747773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23155943384940651948498515 34733915077410977922747773)
            ·
              refine ⟨13025218154029116721030415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34733915077410977922747773 13025218154029116721030415)
              ·
                refine ⟨19537827231043675081545623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13025218154029116721030415 19537827231043675081545623)
                ·
                  refine ⟨29306740846565512622318435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19537827231043675081545623 29306740846565512622318435)
                  ·
                    refine ⟨43960111269848268933477653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29306740846565512622318435 43960111269848268933477653)
                    ·
                      refine ⟨2060630215774137606256765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43960111269848268933477653 2060630215774137606256765)
                      ·
                        rfl

theorem cell23_4013063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_4013063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013063 prefixEnd_4013063 := by exact prefixLift 4013063
  have htrace : WordTrace (prefixWord ++ tailWord_4013063) baseStart_4013063 baseEnd_4013063 := by
    simpa [prefixWord, tailWord_4013063, baseEnd_4013063] using wordTrace_append hprefix tailTrace_4013063
  have hstable : (prefixWord ++ tailWord_4013063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013063).length < 2 ^ (prefixWord ++ tailWord_4013063).sum := by decide
  have hdescent : baseEnd_4013063 < baseStart_4013063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013067 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 3, 2, 2]
def baseStart_4013067 : Nat := 118140960795 + 4013067 * 2 ^ 59
def prefixEnd_4013067 : Nat := 4983230072969 + 3 ^ 40 * 4013067 * 2
def baseEnd_4013067 : Nat := 2060632269696755590606747

theorem tailTrace_4013067 : CollatzResearch.WordTrace tailWord_4013067 prefixEnd_4013067 2060632269696755590606747 := by
  unfold tailWord_4013067
  simp only [CollatzResearch.WordTrace]
  refine ⟨146368578152351111123037455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97579052101567407415358303 146368578152351111123037455)
  ·
    refine ⟨219552867228526666684556183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146368578152351111123037455 219552867228526666684556183)
    ·
      refine ⟨329329300842790000026834275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219552867228526666684556183 329329300842790000026834275)
      ·
        refine ⟨493993951264185000040251413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329329300842790000026834275 493993951264185000040251413)
        ·
          refine ⟨23155966465508671876886785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 493993951264185000040251413 23155966465508671876886785)
          ·
            refine ⟨17366974849131503907665089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23155966465508671876886785 17366974849131503907665089)
            ·
              refine ⟨13025231136848627930748817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17366974849131503907665089 13025231136848627930748817)
              ·
                refine ⟨9768923352636470948061613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13025231136848627930748817 9768923352636470948061613)
                ·
                  refine ⟨3663346257238676605523105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9768923352636470948061613 3663346257238676605523105)
                  ·
                    refine ⟨2747509692929007454142329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3663346257238676605523105 2747509692929007454142329)
                    ·
                      refine ⟨2060632269696755590606747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747509692929007454142329 2060632269696755590606747)
                      ·
                        rfl

theorem cell23_4013067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 2, 2].length) (baseStart_4013067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013067 prefixEnd_4013067 := by exact prefixLift 4013067
  have htrace : WordTrace (prefixWord ++ tailWord_4013067) baseStart_4013067 baseEnd_4013067 := by
    simpa [prefixWord, tailWord_4013067, baseEnd_4013067] using wordTrace_append hprefix tailTrace_4013067
  have hstable : (prefixWord ++ tailWord_4013067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013067).length < 2 ^ (prefixWord ++ tailWord_4013067).sum := by decide
  have hdescent : baseEnd_4013067 < baseStart_4013067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013100 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 3]
def baseStart_4013100 : Nat := 118140960795 + 4013100 * 2 ^ 59
def prefixEnd_4013100 : Nat := 4983230072969 + 3 ^ 40 * 4013100 * 2
def baseEnd_4013100 : Nat := 2060649214558353961494095

theorem tailTrace_4013100 : CollatzResearch.WordTrace tailWord_4013100 prefixEnd_4013100 2060649214558353961494095 := by
  unfold tailWord_4013100
  simp only [CollatzResearch.WordTrace]
  refine ⟨73184890880615778879494377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97579854507487705172659169 73184890880615778879494377)
  ·
    refine ⟨54888668160461834159620783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73184890880615778879494377 54888668160461834159620783)
    ·
      refine ⟨82333002240692751239431175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54888668160461834159620783 82333002240692751239431175)
      ·
        refine ⟨123499503361039126859146763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82333002240692751239431175 123499503361039126859146763)
        ·
          refine ⟨185249255041558690288720145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123499503361039126859146763 185249255041558690288720145)
          ·
            refine ⟨138936941281169017716540109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185249255041558690288720145 138936941281169017716540109)
            ·
              refine ⟨52101352980438381643702541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138936941281169017716540109 52101352980438381643702541)
              ·
                refine ⟨19538007367664393116388453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52101352980438381643702541 19538007367664393116388453)
                ·
                  refine ⟨3663376381437073709322835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19538007367664393116388453 3663376381437073709322835)
                  ·
                    refine ⟨5495064572155610563984253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3663376381437073709322835 5495064572155610563984253)
                    ·
                      refine ⟨2060649214558353961494095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5495064572155610563984253 2060649214558353961494095)
                      ·
                        rfl

theorem cell23_4013100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_4013100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013100 prefixEnd_4013100 := by exact prefixLift 4013100
  have htrace : WordTrace (prefixWord ++ tailWord_4013100) baseStart_4013100 baseEnd_4013100 := by
    simpa [prefixWord, tailWord_4013100, baseEnd_4013100] using wordTrace_append hprefix tailTrace_4013100
  have hstable : (prefixWord ++ tailWord_4013100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013100).length < 2 ^ (prefixWord ++ tailWord_4013100).sum := by decide
  have hdescent : baseEnd_4013100 < baseStart_4013100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013121 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_4013121 : Nat := 118140960795 + 4013121 * 2 ^ 59
def prefixEnd_4013121 : Nat := 4983230072969 + 3 ^ 40 * 4013121 * 2
def baseEnd_4013121 : Nat := 2060659997652098379331499

theorem tailTrace_4013121 : CollatzResearch.WordTrace tailWord_4013121 prefixEnd_4013121 2060659997652098379331499 := by
  unfold tailWord_4013121
  simp only [CollatzResearch.WordTrace]
  refine ⟨146370547694155478345503217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97580365129436985563668811 146370547694155478345503217)
  ·
    refine ⟨109777910770616608759127413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146370547694155478345503217 109777910770616608759127413)
    ·
      refine ⟨10291679134745307071168195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109777910770616608759127413 10291679134745307071168195)
      ·
        refine ⟨15437518702117960606752293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10291679134745307071168195 15437518702117960606752293)
        ·
          refine ⟨2894534756647117613766055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15437518702117960606752293 2894534756647117613766055)
          ·
            refine ⟨4341802134970676420649083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894534756647117613766055 4341802134970676420649083)
            ·
              refine ⟨6512703202456014630973625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341802134970676420649083 6512703202456014630973625)
              ·
                refine ⟨4884527401842010973230219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6512703202456014630973625 4884527401842010973230219)
                ·
                  refine ⟨7326791102763016459845329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884527401842010973230219 7326791102763016459845329)
                  ·
                    refine ⟨5495093327072262344883997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7326791102763016459845329 5495093327072262344883997)
                    ·
                      refine ⟨2060659997652098379331499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5495093327072262344883997 2060659997652098379331499)
                      ·
                        rfl

theorem cell23_4013121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_4013121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013121 prefixEnd_4013121 := by exact prefixLift 4013121
  have htrace : WordTrace (prefixWord ++ tailWord_4013121) baseStart_4013121 baseEnd_4013121 := by
    simpa [prefixWord, tailWord_4013121, baseEnd_4013121] using wordTrace_append hprefix tailTrace_4013121
  have hstable : (prefixWord ++ tailWord_4013121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013121).length < 2 ^ (prefixWord ++ tailWord_4013121).sum := by decide
  have hdescent : baseEnd_4013121 < baseStart_4013121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013127 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_4013127 : Nat := 118140960795 + 4013127 * 2 ^ 59
def prefixEnd_4013127 : Nat := 4983230072969 + 3 ^ 40 * 4013127 * 2
def baseEnd_4013127 : Nat := 2060663078536025355856471

theorem tailTrace_4013127 : CollatzResearch.WordTrace tailWord_4013127 prefixEnd_4013127 2060663078536025355856471 := by
  unfold tailWord_4013127
  simp only [CollatzResearch.WordTrace]
  refine ⟨146370766532133741370221635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97580511021422494246814423 146370766532133741370221635)
  ·
    refine ⟨219556149798200612055332453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146370766532133741370221635 219556149798200612055332453)
    ·
      refine ⟨41166778087162614760374835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219556149798200612055332453 41166778087162614760374835)
      ·
        refine ⟨61750167130743922140562253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41166778087162614760374835 61750167130743922140562253)
        ·
          refine ⟨23156312674028970802710845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61750167130743922140562253 23156312674028970802710845)
          ·
            refine ⟨8683617252760864051016567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23156312674028970802710845 8683617252760864051016567)
            ·
              refine ⟨13025425879141296076524851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683617252760864051016567 13025425879141296076524851)
              ·
                refine ⟨19538138818711944114787277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13025425879141296076524851 19538138818711944114787277)
                ·
                  refine ⟨7326802057016979043045229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19538138818711944114787277 7326802057016979043045229)
                  ·
                    refine ⟨2747550771381367141141961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7326802057016979043045229 2747550771381367141141961)
                    ·
                      refine ⟨2060663078536025355856471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747550771381367141141961 2060663078536025355856471)
                      ·
                        rfl

theorem cell23_4013127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_4013127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013127 prefixEnd_4013127 := by exact prefixLift 4013127
  have htrace : WordTrace (prefixWord ++ tailWord_4013127) baseStart_4013127 baseEnd_4013127 := by
    simpa [prefixWord, tailWord_4013127, baseEnd_4013127] using wordTrace_append hprefix tailTrace_4013127
  have hstable : (prefixWord ++ tailWord_4013127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013127).length < 2 ^ (prefixWord ++ tailWord_4013127).sum := by decide
  have hdescent : baseEnd_4013127 < baseStart_4013127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013144 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 1, 3, 2]
def baseStart_4013144 : Nat := 118140960795 + 4013144 * 2 ^ 59
def prefixEnd_4013144 : Nat := 4983230072969 + 3 ^ 40 * 4013144 * 2
def baseEnd_4013144 : Nat := 2060671807707151789343893

theorem tailTrace_4013144 : CollatzResearch.WordTrace tailWord_4013144 prefixEnd_4013144 2060671807707151789343893 := by
  unfold tailWord_4013144
  simp only [CollatzResearch.WordTrace]
  refine ⟨73185693286536076636795243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97580924382048102182393657 73185693286536076636795243)
  ·
    refine ⟨109778539929804114955192865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73185693286536076636795243 109778539929804114955192865)
    ·
      refine ⟨82333904947353086216394649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109778539929804114955192865 82333904947353086216394649)
      ·
        refine ⟨61750428710514814662295987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82333904947353086216394649 61750428710514814662295987)
        ·
          refine ⟨92625643065772221993443981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61750428710514814662295987 92625643065772221993443981)
          ·
            refine ⟨34734616149664583247541493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92625643065772221993443981 34734616149664583247541493)
            ·
              refine ⟨3256370264031054679457015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34734616149664583247541493 3256370264031054679457015)
              ·
                refine ⟨4884555396046582019185523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3256370264031054679457015 4884555396046582019185523)
                ·
                  refine ⟨7326833094069873028778285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884555396046582019185523 7326833094069873028778285)
                  ·
                    refine ⟨2747562410276202385791857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7326833094069873028778285 2747562410276202385791857)
                    ·
                      refine ⟨2060671807707151789343893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747562410276202385791857 2060671807707151789343893)
                      ·
                        rfl

theorem cell23_4013144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_4013144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013144 prefixEnd_4013144 := by exact prefixLift 4013144
  have htrace : WordTrace (prefixWord ++ tailWord_4013144) baseStart_4013144 baseEnd_4013144 := by
    simpa [prefixWord, tailWord_4013144, baseEnd_4013144] using wordTrace_append hprefix tailTrace_4013144
  have hstable : (prefixWord ++ tailWord_4013144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013144).length < 2 ^ (prefixWord ++ tailWord_4013144).sum := by decide
  have hdescent : baseEnd_4013144 < baseStart_4013144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013170 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_4013170 : Nat := 118140960795 + 4013170 * 2 ^ 59
def prefixEnd_4013170 : Nat := 4983230072969 + 3 ^ 40 * 4013170 * 2
def baseEnd_4013170 : Nat := 2060685158204168687618773

theorem tailTrace_4013170 : CollatzResearch.WordTrace tailWord_4013170 prefixEnd_4013170 2060685158204168687618773 := by
  unfold tailWord_4013170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36593083717744489928509241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97581556580651973142691309 36593083717744489928509241)
  ·
    refine ⟨27444812788308367446381931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36593083717744489928509241 27444812788308367446381931)
    ·
      refine ⟨41167219182462551169572897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27444812788308367446381931 41167219182462551169572897)
      ·
        refine ⟨30875414386846913377179673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41167219182462551169572897 30875414386846913377179673)
        ·
          refine ⟨23156560790135185032884755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30875414386846913377179673 23156560790135185032884755)
          ·
            refine ⟨34734841185202777549327133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23156560790135185032884755 34734841185202777549327133)
            ·
              refine ⟨13025565444451041580997675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34734841185202777549327133 13025565444451041580997675)
              ·
                refine ⟨19538348166676562371496513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13025565444451041580997675 19538348166676562371496513)
                ·
                  refine ⟨14653761125007421778622385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19538348166676562371496513 14653761125007421778622385)
                  ·
                    refine ⟨10990320843755566333966789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14653761125007421778622385 10990320843755566333966789)
                    ·
                      refine ⟨2060685158204168687618773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10990320843755566333966789 2060685158204168687618773)
                      ·
                        rfl

theorem cell23_4013170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_4013170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013170 prefixEnd_4013170 := by exact prefixLift 4013170
  have htrace : WordTrace (prefixWord ++ tailWord_4013170) baseStart_4013170 baseEnd_4013170 := by
    simpa [prefixWord, tailWord_4013170, baseEnd_4013170] using wordTrace_append hprefix tailTrace_4013170
  have hstable : (prefixWord ++ tailWord_4013170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013170).length < 2 ^ (prefixWord ++ tailWord_4013170).sum := by decide
  have hdescent : baseEnd_4013170 < baseStart_4013170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013174 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_4013174 : Nat := 118140960795 + 4013174 * 2 ^ 59
def prefixEnd_4013174 : Nat := 4983230072969 + 3 ^ 40 * 4013174 * 2
def baseEnd_4013174 : Nat := 2060687212126786671968755

theorem tailTrace_4013174 : CollatzResearch.WordTrace tailWord_4013174 prefixEnd_4013174 2060687212126786671968755 := by
  unfold tailWord_4013174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9148280047685216774823911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97581653841975645598121717 9148280047685216774823911)
  ·
    refine ⟨13722420071527825162235867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9148280047685216774823911 13722420071527825162235867)
    ·
      refine ⟨20583630107291737743353801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13722420071527825162235867 20583630107291737743353801)
      ·
        refine ⟨15437722580468803307515351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20583630107291737743353801 15437722580468803307515351)
        ·
          refine ⟨23156583870703204961273027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15437722580468803307515351 23156583870703204961273027)
          ·
            refine ⟨34734875806054807441909541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23156583870703204961273027 34734875806054807441909541)
            ·
              refine ⟨6512789213635276395358039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34734875806054807441909541 6512789213635276395358039)
              ·
                refine ⟨9769183820452914593037059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6512789213635276395358039 9769183820452914593037059)
                ·
                  refine ⟨14653775730679371889555589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9769183820452914593037059 14653775730679371889555589)
                  ·
                    refine ⟨2747582949502382229291673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14653775730679371889555589 2747582949502382229291673)
                    ·
                      refine ⟨2060687212126786671968755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747582949502382229291673 2060687212126786671968755)
                      ·
                        rfl

theorem cell23_4013174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_4013174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013174 prefixEnd_4013174 := by exact prefixLift 4013174
  have htrace : WordTrace (prefixWord ++ tailWord_4013174) baseStart_4013174 baseEnd_4013174 := by
    simpa [prefixWord, tailWord_4013174, baseEnd_4013174] using wordTrace_append hprefix tailTrace_4013174
  have hstable : (prefixWord ++ tailWord_4013174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013174).length < 2 ^ (prefixWord ++ tailWord_4013174).sum := by decide
  have hdescent : baseEnd_4013174 < baseStart_4013174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013200 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 1, 7, 2]
def baseStart_4013200 : Nat := 118140960795 + 4013200 * 2 ^ 59
def prefixEnd_4013200 : Nat := 4983230072969 + 3 ^ 40 * 4013200 * 2
def baseEnd_4013200 : Nat := 2060700562623803570243635

theorem tailTrace_4013200 : CollatzResearch.WordTrace tailWord_4013200 prefixEnd_4013200 2060700562623803570243635 := by
  unfold tailWord_4013200
  simp only [CollatzResearch.WordTrace]
  refine ⟨73186714530434637418814527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97582286040579516558419369 73186714530434637418814527)
  ·
    refine ⟨109780071795651956128221791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73186714530434637418814527 109780071795651956128221791)
    ·
      refine ⟨164670107693477934192332687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109780071795651956128221791 164670107693477934192332687)
      ·
        refine ⟨247005161540216901288499031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164670107693477934192332687 247005161540216901288499031)
        ·
          refine ⟨370507742310325351932748547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247005161540216901288499031 370507742310325351932748547)
          ·
            refine ⟨555761613465488027899122821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370507742310325351932748547 555761613465488027899122821)
            ·
              refine ⟨104205302524779005231085529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 555761613465488027899122821 104205302524779005231085529)
              ·
                refine ⟨78153976893584253923314147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104205302524779005231085529 78153976893584253923314147)
                ·
                  refine ⟨117230965340376380884971221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78153976893584253923314147 117230965340376380884971221)
                  ·
                    refine ⟨2747600750165071426991513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 117230965340376380884971221 2747600750165071426991513)
                    ·
                      refine ⟨2060700562623803570243635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747600750165071426991513 2060700562623803570243635)
                      ·
                        rfl

theorem cell23_4013200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 7, 2].length) (baseStart_4013200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013200 prefixEnd_4013200 := by exact prefixLift 4013200
  have htrace : WordTrace (prefixWord ++ tailWord_4013200) baseStart_4013200 baseEnd_4013200 := by
    simpa [prefixWord, tailWord_4013200, baseEnd_4013200] using wordTrace_append hprefix tailTrace_4013200
  have hstable : (prefixWord ++ tailWord_4013200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013200).length < 2 ^ (prefixWord ++ tailWord_4013200).sum := by decide
  have hdescent : baseEnd_4013200 < baseStart_4013200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013203 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 5]
def baseStart_4013203 : Nat := 118140960795 + 4013203 * 2 ^ 59
def prefixEnd_4013203 : Nat := 4983230072969 + 3 ^ 40 * 4013203 * 2
def baseEnd_4013203 : Nat := 2060702103065767058506121

theorem tailTrace_4013203 : CollatzResearch.WordTrace tailWord_4013203 prefixEnd_4013203 2060702103065767058506121 := by
  unfold tailWord_4013203
  simp only [CollatzResearch.WordTrace]
  refine ⟨146373538479858406349988263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97582358986572270899992175 146373538479858406349988263)
  ·
    refine ⟨219560307719787609524982395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146373538479858406349988263 219560307719787609524982395)
    ·
      refine ⟨329340461579681414287473593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219560307719787609524982395 329340461579681414287473593)
      ·
        refine ⟨247005346184761060715605195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329340461579681414287473593 247005346184761060715605195)
        ·
          refine ⟨370508019277141591073407793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247005346184761060715605195 370508019277141591073407793)
          ·
            refine ⟨277881014457856193305055845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370508019277141591073407793 277881014457856193305055845)
            ·
              refine ⟨52102690210848036244697971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277881014457856193305055845 52102690210848036244697971)
              ·
                refine ⟨78154035316272054367046957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52102690210848036244697971 78154035316272054367046957)
                ·
                  refine ⟨29307763243602020387642609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78154035316272054367046957 29307763243602020387642609)
                  ·
                    refine ⟨21980822432701515290731957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29307763243602020387642609 21980822432701515290731957)
                    ·
                      refine ⟨2060702103065767058506121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21980822432701515290731957 2060702103065767058506121)
                      ·
                        rfl

theorem cell23_4013203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_4013203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013203 prefixEnd_4013203 := by exact prefixLift 4013203
  have htrace : WordTrace (prefixWord ++ tailWord_4013203) baseStart_4013203 baseEnd_4013203 := by
    simpa [prefixWord, tailWord_4013203, baseEnd_4013203] using wordTrace_append hprefix tailTrace_4013203
  have hstable : (prefixWord ++ tailWord_4013203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013203).length < 2 ^ (prefixWord ++ tailWord_4013203).sum := by decide
  have hdescent : baseEnd_4013203 < baseStart_4013203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013214 : List Nat := [4, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_4013214 : Nat := 118140960795 + 4013214 * 2 ^ 59
def prefixEnd_4013214 : Nat := 4983230072969 + 3 ^ 40 * 4013214 * 2
def baseEnd_4013214 : Nat := 228967527928107390607619

theorem tailTrace_4013214 : CollatzResearch.WordTrace tailWord_4013214 prefixEnd_4013214 228967527928107390607619 := by
  unfold tailWord_4013214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18296742460352319403579837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97582626455212370152425797 18296742460352319403579837)
  ·
    refine ⟨6861278422632119776342439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18296742460352319403579837 6861278422632119776342439)
    ·
      refine ⟨10291917633948179664513659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861278422632119776342439 10291917633948179664513659)
      ·
        refine ⟨15437876450922269496770489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10291917633948179664513659 15437876450922269496770489)
        ·
          refine ⟨11578407338191702122577867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15437876450922269496770489 11578407338191702122577867)
          ·
            refine ⟨17367611007287553183866801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11578407338191702122577867 17367611007287553183866801)
            ·
              refine ⟨13025708255465664887900101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17367611007287553183866801 13025708255465664887900101)
              ·
                refine ⟨2442320297899812166481269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13025708255465664887900101 2442320297899812166481269)
                ·
                  refine ⟨228967527928107390607619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2442320297899812166481269 228967527928107390607619)
                  ·
                    rfl

theorem cell23_4013214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_4013214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013214 prefixEnd_4013214 := by exact prefixLift 4013214
  have htrace : WordTrace (prefixWord ++ tailWord_4013214) baseStart_4013214 baseEnd_4013214 := by
    simpa [prefixWord, tailWord_4013214, baseEnd_4013214] using wordTrace_append hprefix tailTrace_4013214
  have hstable : (prefixWord ++ tailWord_4013214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013214).length < 2 ^ (prefixWord ++ tailWord_4013214).sum := by decide
  have hdescent : baseEnd_4013214 < baseStart_4013214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013240 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 5, 4]
def baseStart_4013240 : Nat := 118140960795 + 4013240 * 2 ^ 59
def prefixEnd_4013240 : Nat := 4983230072969 + 3 ^ 40 * 4013240 * 2
def baseEnd_4013240 : Nat := 686907033949994471247817

theorem tailTrace_4013240 : CollatzResearch.WordTrace tailWord_4013240 prefixEnd_4013240 686907033949994471247817 := by
  unfold tailWord_4013240
  simp only [CollatzResearch.WordTrace]
  refine ⟨73187443990362180834542587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97583258653816241112723449 73187443990362180834542587)
  ·
    refine ⟨109781165985543271251813881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73187443990362180834542587 109781165985543271251813881)
    ·
      refine ⟨82335874489157453438860411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109781165985543271251813881 82335874489157453438860411)
      ·
        refine ⟨123503811733736180158290617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82335874489157453438860411 123503811733736180158290617)
        ·
          refine ⟨92627858800302135118717963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123503811733736180158290617 92627858800302135118717963)
          ·
            refine ⟨138941788200453202678076945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92627858800302135118717963 138941788200453202678076945)
            ·
              refine ⟨104206341150339902008557709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138941788200453202678076945 104206341150339902008557709)
              ·
                refine ⟨39077377931377463253209141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104206341150339902008557709 39077377931377463253209141)
                ·
                  refine ⟨3663504181066637179988357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39077377931377463253209141 3663504181066637179988357)
                  ·
                    refine ⟨686907033949994471247817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3663504181066637179988357 686907033949994471247817)
                    ·
                      rfl

theorem cell23_4013240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_4013240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013240 prefixEnd_4013240 := by exact prefixLift 4013240
  have htrace : WordTrace (prefixWord ++ tailWord_4013240) baseStart_4013240 baseEnd_4013240 := by
    simpa [prefixWord, tailWord_4013240, baseEnd_4013240] using wordTrace_append hprefix tailTrace_4013240
  have hstable : (prefixWord ++ tailWord_4013240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013240).length < 2 ^ (prefixWord ++ tailWord_4013240).sum := by decide
  have hdescent : baseEnd_4013240 < baseStart_4013240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013243 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 6]
def baseStart_4013243 : Nat := 118140960795 + 4013243 * 2 ^ 59
def prefixEnd_4013243 : Nat := 4983230072969 + 3 ^ 40 * 4013243 * 2
def baseEnd_4013243 : Nat := 2060722642291946902005937

theorem tailTrace_4013243 : CollatzResearch.WordTrace tailWord_4013243 prefixEnd_4013243 2060722642291946902005937 := by
  unfold tailWord_4013243
  simp only [CollatzResearch.WordTrace]
  refine ⟨146374997399713493181444383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97583331599808995454296255 146374997399713493181444383)
  ·
    refine ⟨219562496099570239772166575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146374997399713493181444383 219562496099570239772166575)
    ·
      refine ⟨329343744149355359658249863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219562496099570239772166575 329343744149355359658249863)
      ·
        refine ⟨494015616224033039487374795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329343744149355359658249863 494015616224033039487374795)
        ·
          refine ⟨741023424336049559231062193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494015616224033039487374795 741023424336049559231062193)
          ·
            refine ⟨555767568252037169423296645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741023424336049559231062193 555767568252037169423296645)
            ·
              refine ⟨104206419047256969266868121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 555767568252037169423296645 104206419047256969266868121)
              ·
                refine ⟨78154814285442726950151091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104206419047256969266868121 78154814285442726950151091)
                ·
                  refine ⟨117232221428164090425226637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78154814285442726950151091 117232221428164090425226637)
                  ·
                    refine ⟨43962083035561533909459989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117232221428164090425226637 43962083035561533909459989)
                    ·
                      refine ⟨2060722642291946902005937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43962083035561533909459989 2060722642291946902005937)
                      ·
                        rfl

theorem cell23_4013243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_4013243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013243 prefixEnd_4013243 := by exact prefixLift 4013243
  have htrace : WordTrace (prefixWord ++ tailWord_4013243) baseStart_4013243 baseEnd_4013243 := by
    simpa [prefixWord, tailWord_4013243, baseEnd_4013243] using wordTrace_append hprefix tailTrace_4013243
  have hstable : (prefixWord ++ tailWord_4013243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013243).length < 2 ^ (prefixWord ++ tailWord_4013243).sum := by decide
  have hdescent : baseEnd_4013243 < baseStart_4013243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013261 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4013261 : Nat := 118140960795 + 4013261 * 2 ^ 59
def prefixEnd_4013261 : Nat := 4983230072969 + 3 ^ 40 * 4013261 * 2
def baseEnd_4013261 : Nat := 686910628314575943860285

theorem tailTrace_4013261 : CollatzResearch.WordTrace tailWord_4013261 prefixEnd_4013261 686910628314575943860285 := by
  unfold tailWord_4013261
  simp only [CollatzResearch.WordTrace]
  refine ⟨146375653913648282255599637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97583769275765521503733091 146375653913648282255599637)
  ·
    refine ⟨6861358777202263230731233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146375653913648282255599637 6861358777202263230731233)
    ·
      refine ⟨5146019082901697423048425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6861358777202263230731233 5146019082901697423048425)
      ·
        refine ⟨3859514312176273067286319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5146019082901697423048425 3859514312176273067286319)
        ·
          refine ⟨5789271468264409600929479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859514312176273067286319 5789271468264409600929479)
          ·
            refine ⟨8683907202396614401394219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5789271468264409600929479 8683907202396614401394219)
            ·
              refine ⟨13025860803594921602091329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683907202396614401394219 13025860803594921602091329)
              ·
                refine ⟨9769395602696191201568497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13025860803594921602091329 9769395602696191201568497)
                ·
                  refine ⟨7327046702022143401176373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9769395602696191201568497 7327046702022143401176373)
                  ·
                    refine ⟨686910628314575943860285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7327046702022143401176373 686910628314575943860285)
                    ·
                      rfl

theorem cell23_4013261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4013261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013261 prefixEnd_4013261 := by exact prefixLift 4013261
  have htrace : WordTrace (prefixWord ++ tailWord_4013261) baseStart_4013261 baseEnd_4013261 := by
    simpa [prefixWord, tailWord_4013261, baseEnd_4013261] using wordTrace_append hprefix tailTrace_4013261
  have hstable : (prefixWord ++ tailWord_4013261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013261).length < 2 ^ (prefixWord ++ tailWord_4013261).sum := by decide
  have hdescent : baseEnd_4013261 < baseStart_4013261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013297 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 3]
def baseStart_4013297 : Nat := 118140960795 + 4013297 * 2 ^ 59
def prefixEnd_4013297 : Nat := 4983230072969 + 3 ^ 40 * 4013297 * 2
def baseEnd_4013297 : Nat := 2060750370247289690730689

theorem tailTrace_4013297 : CollatzResearch.WordTrace tailWord_4013297 prefixEnd_4013297 2060750370247289690730689 := by
  unfold tailWord_4013297
  simp only [CollatzResearch.WordTrace]
  refine ⟨146376966941517860403910145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97584644627678573602606763 146376966941517860403910145)
  ·
    refine ⟨109782725206138395302932609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146376966941517860403910145 109782725206138395302932609)
    ·
      refine ⟨82337043904603796477199457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109782725206138395302932609 82337043904603796477199457)
      ·
        refine ⟨61752782928452847357899593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82337043904603796477199457 61752782928452847357899593)
        ·
          refine ⟨46314587196339635518424695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61752782928452847357899593 46314587196339635518424695)
          ·
            refine ⟨69471880794509453277637043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46314587196339635518424695 69471880794509453277637043)
            ·
              refine ⟨104207821191764179916455565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69471880794509453277637043 104207821191764179916455565)
              ·
                refine ⟨39077932946911567468670837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104207821191764179916455565 39077932946911567468670837)
                ·
                  refine ⟨3663556213772959450187891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39077932946911567468670837 3663556213772959450187891)
                  ·
                    refine ⟨5495334320659439175281837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3663556213772959450187891 5495334320659439175281837)
                    ·
                      refine ⟨2060750370247289690730689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5495334320659439175281837 2060750370247289690730689)
                      ·
                        rfl

theorem cell23_4013297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_4013297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013297 prefixEnd_4013297 := by exact prefixLift 4013297
  have htrace : WordTrace (prefixWord ++ tailWord_4013297) baseStart_4013297 baseEnd_4013297 := by
    simpa [prefixWord, tailWord_4013297, baseEnd_4013297] using wordTrace_append hprefix tailTrace_4013297
  have hstable : (prefixWord ++ tailWord_4013297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013297).length < 2 ^ (prefixWord ++ tailWord_4013297).sum := by decide
  have hdescent : baseEnd_4013297 < baseStart_4013297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013324 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 2, 3, 2]
def baseStart_4013324 : Nat := 118140960795 + 4013324 * 2 ^ 59
def prefixEnd_4013324 : Nat := 4983230072969 + 3 ^ 40 * 4013324 * 2
def baseEnd_4013324 : Nat := 2060764234224961085093065

theorem tailTrace_4013324 : CollatzResearch.WordTrace tailWord_4013324 prefixEnd_4013324 2060764234224961085093065 := by
  unfold tailWord_4013324
  simp only [CollatzResearch.WordTrace]
  refine ⟨73188975856210022007571513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97585301141613362676762017 73188975856210022007571513)
  ·
    refine ⟨54891731892157516505678635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73188975856210022007571513 54891731892157516505678635)
    ·
      refine ⟨82337597838236274758517953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54891731892157516505678635 82337597838236274758517953)
      ·
        refine ⟨61753198378677206068888465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82337597838236274758517953 61753198378677206068888465)
        ·
          refine ⟨46314898784007904551666349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61753198378677206068888465 46314898784007904551666349)
          ·
            refine ⟨17368087044002964206874881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46314898784007904551666349 17368087044002964206874881)
            ·
              refine ⟨13026065283002223155156161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17368087044002964206874881 13026065283002223155156161)
              ·
                refine ⟨9769548962251667366367121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13026065283002223155156161 9769548962251667366367121)
                ·
                  refine ⟨7327161721688750524775341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9769548962251667366367121 7327161721688750524775341)
                  ·
                    refine ⟨2747685645633281446790753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7327161721688750524775341 2747685645633281446790753)
                    ·
                      refine ⟨2060764234224961085093065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747685645633281446790753 2060764234224961085093065)
                      ·
                        rfl

theorem cell23_4013324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_4013324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013324 prefixEnd_4013324 := by exact prefixLift 4013324
  have htrace : WordTrace (prefixWord ++ tailWord_4013324) baseStart_4013324 baseEnd_4013324 := by
    simpa [prefixWord, tailWord_4013324, baseEnd_4013324] using wordTrace_append hprefix tailTrace_4013324
  have hstable : (prefixWord ++ tailWord_4013324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013324).length < 2 ^ (prefixWord ++ tailWord_4013324).sum := by decide
  have hdescent : baseEnd_4013324 < baseStart_4013324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013347 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 1, 6]
def baseStart_4013347 : Nat := 118140960795 + 4013347 * 2 ^ 59
def prefixEnd_4013347 : Nat := 4983230072969 + 3 ^ 40 * 4013347 * 2
def baseEnd_4013347 : Nat := 686925348093338165035153

theorem tailTrace_4013347 : CollatzResearch.WordTrace tailWord_4013347 prefixEnd_4013347 686925348093338165035153 := by
  unfold tailWord_4013347
  simp only [CollatzResearch.WordTrace]
  refine ⟨146378790591336718943230295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97585860394224479295486863 146378790591336718943230295)
  ·
    refine ⟨219568185887005078414845443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146378790591336718943230295 219568185887005078414845443)
    ·
      refine ⟨329352278830507617622268165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219568185887005078414845443 329352278830507617622268165)
      ·
        refine ⟨61753552280720178304175281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329352278830507617622268165 61753552280720178304175281)
        ·
          refine ⟨46315164210540133728131461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61753552280720178304175281 46315164210540133728131461)
          ·
            refine ⟨8684093289476275074024649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46315164210540133728131461 8684093289476275074024649)
            ·
              refine ⟨6513069967107206305518487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8684093289476275074024649 6513069967107206305518487)
              ·
                refine ⟨9769604950660809458277731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513069967107206305518487 9769604950660809458277731)
                ·
                  refine ⟨14654407425991214187416597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9769604950660809458277731 14654407425991214187416597)
                  ·
                    refine ⟨686925348093338165035153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14654407425991214187416597 686925348093338165035153)
                    ·
                      rfl

theorem cell23_4013347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 6].length) (baseStart_4013347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013347 prefixEnd_4013347 := by exact prefixLift 4013347
  have htrace : WordTrace (prefixWord ++ tailWord_4013347) baseStart_4013347 baseEnd_4013347 := by
    simpa [prefixWord, tailWord_4013347, baseEnd_4013347] using wordTrace_append hprefix tailTrace_4013347
  have hstable : (prefixWord ++ tailWord_4013347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013347).length < 2 ^ (prefixWord ++ tailWord_4013347).sum := by decide
  have hdescent : baseEnd_4013347 < baseStart_4013347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013354 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4013354 : Nat := 118140960795 + 4013354 * 2 ^ 59
def prefixEnd_4013354 : Nat := 4983230072969 + 3 ^ 40 * 4013354 * 2
def baseEnd_4013354 : Nat := 2060779638644595967717927

theorem tailTrace_4013354 : CollatzResearch.WordTrace tailWord_4013354 prefixEnd_4013354 2060779638644595967717927 := by
  unfold tailWord_4013354
  simp only [CollatzResearch.WordTrace]
  refine ⟨36594761475577839784683779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97586030601540906092490077 36594761475577839784683779)
  ·
    refine ⟨54892142213366759677025669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36594761475577839784683779 54892142213366759677025669)
    ·
      refine ⟨10292276665006267439442313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54892142213366759677025669 10292276665006267439442313)
      ·
        refine ⟨7719207498754700579581735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10292276665006267439442313 7719207498754700579581735)
        ·
          refine ⟨11578811248132050869372603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7719207498754700579581735 11578811248132050869372603)
          ·
            refine ⟨17368216872198076304058905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11578811248132050869372603 17368216872198076304058905)
            ·
              refine ⟨13026162654148557228044179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17368216872198076304058905 13026162654148557228044179)
              ·
                refine ⟨19539243981222835842066269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13026162654148557228044179 19539243981222835842066269)
                ·
                  refine ⟨7327216492958563440774851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19539243981222835842066269 7327216492958563440774851)
                  ·
                    refine ⟨10990824739437845161162277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7327216492958563440774851 10990824739437845161162277)
                    ·
                      refine ⟨2060779638644595967717927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10990824739437845161162277 2060779638644595967717927)
                      ·
                        rfl

theorem cell23_4013354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4013354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013354 prefixEnd_4013354 := by exact prefixLift 4013354
  have htrace : WordTrace (prefixWord ++ tailWord_4013354) baseStart_4013354 baseEnd_4013354 := by
    simpa [prefixWord, tailWord_4013354, baseEnd_4013354] using wordTrace_append hprefix tailTrace_4013354
  have hstable : (prefixWord ++ tailWord_4013354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013354).length < 2 ^ (prefixWord ++ tailWord_4013354).sum := by decide
  have hdescent : baseEnd_4013354 < baseStart_4013354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013364 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_4013364 : Nat := 118140960795 + 4013364 * 2 ^ 59
def prefixEnd_4013364 : Nat := 4983230072969 + 3 ^ 40 * 4013364 * 2
def baseEnd_4013364 : Nat := 686928257817046976197627

theorem tailTrace_4013364 : CollatzResearch.WordTrace tailWord_4013364 prefixEnd_4013364 686928257817046976197627 := by
  unfold tailWord_4013364
  simp only [CollatzResearch.WordTrace]
  refine ⟨73189705316137565423299573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97586273754850087231066097 73189705316137565423299573)
  ·
    refine ⟨6861534873387896758434335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73189705316137565423299573 6861534873387896758434335)
    ·
      refine ⟨10292302310081845137651503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861534873387896758434335 10292302310081845137651503)
      ·
        refine ⟨15438453465122767706477255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10292302310081845137651503 15438453465122767706477255)
        ·
          refine ⟨23157680197684151559715883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15438453465122767706477255 23157680197684151559715883)
          ·
            refine ⟨34736520296526227339573825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23157680197684151559715883 34736520296526227339573825)
            ·
              refine ⟨26052390222394670504680369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34736520296526227339573825 26052390222394670504680369)
              ·
                refine ⟨19539292666796002878510277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26052390222394670504680369 19539292666796002878510277)
                ·
                  refine ⟨3663617375024250539720677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19539292666796002878510277 3663617375024250539720677)
                  ·
                    refine ⟨686928257817046976197627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3663617375024250539720677 686928257817046976197627)
                    ·
                      rfl

theorem cell23_4013364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_4013364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013364 prefixEnd_4013364 := by exact prefixLift 4013364
  have htrace : WordTrace (prefixWord ++ tailWord_4013364) baseStart_4013364 baseEnd_4013364 := by
    simpa [prefixWord, tailWord_4013364, baseEnd_4013364] using wordTrace_append hprefix tailTrace_4013364
  have hstable : (prefixWord ++ tailWord_4013364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013364).length < 2 ^ (prefixWord ++ tailWord_4013364).sum := by decide
  have hdescent : baseEnd_4013364 < baseStart_4013364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013377 : List Nat := [1, 2, 5, 2, 1, 2, 10]
def baseStart_4013377 : Nat := 118140960795 + 4013377 * 2 ^ 59
def prefixEnd_4013377 : Nat := 4983230072969 + 3 ^ 40 * 4013377 * 2
def baseEnd_4013377 : Nat := 25441869737032708367041

theorem tailTrace_4013377 : CollatzResearch.WordTrace tailWord_4013377 prefixEnd_4013377 25441869737032708367041 := by
  unfold tailWord_4013377
  simp only [CollatzResearch.WordTrace]
  refine ⟨146379884781228034066822385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97586589854152022711214923 146379884781228034066822385)
  ·
    refine ⟨109784913585921025550116789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146379884781228034066822385 109784913585921025550116789)
    ·
      refine ⟨10292335648680096145323449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109784913585921025550116789 10292335648680096145323449)
      ·
        refine ⟨7719251736510072108992587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10292335648680096145323449 7719251736510072108992587)
        ·
          refine ⟨11578877604765108163488881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7719251736510072108992587 11578877604765108163488881)
          ·
            refine ⟨8684158203573831122616661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11578877604765108163488881 8684158203573831122616661)
            ·
              refine ⟨25441869737032708367041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8684158203573831122616661 25441869737032708367041)
              ·
                rfl

theorem cell23_4013377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 10].length) (baseStart_4013377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013377 prefixEnd_4013377 := by exact prefixLift 4013377
  have htrace : WordTrace (prefixWord ++ tailWord_4013377) baseStart_4013377 baseEnd_4013377 := by
    simpa [prefixWord, tailWord_4013377, baseEnd_4013377] using wordTrace_append hprefix tailTrace_4013377
  have hstable : (prefixWord ++ tailWord_4013377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013377).length < 2 ^ (prefixWord ++ tailWord_4013377).sum := by decide
  have hdescent : baseEnd_4013377 < baseStart_4013377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013388 : List Nat := [2, 2, 1, 3, 2, 2, 2, 4, 1, 2, 2]
def baseStart_4013388 : Nat := 118140960795 + 4013388 * 2 ^ 59
def prefixEnd_4013388 : Nat := 4983230072969 + 3 ^ 40 * 4013388 * 2
def baseEnd_4013388 : Nat := 2060797096986848834692771

theorem tailTrace_4013388 : CollatzResearch.WordTrace tailWord_4013388 prefixEnd_4013388 2060797096986848834692771 := by
  unfold tailWord_4013388
  simp only [CollatzResearch.WordTrace]
  refine ⟨73190142992094091472736409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97586857322792121963648545 73190142992094091472736409)
  ·
    refine ⟨54892607244070568604552307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73190142992094091472736409 54892607244070568604552307)
    ·
      refine ⟨82338910866105852906828461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54892607244070568604552307 82338910866105852906828461)
      ·
        refine ⟨30877091574789694840060673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82338910866105852906828461 30877091574789694840060673)
        ·
          refine ⟨23157818681092271130045505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30877091574789694840060673 23157818681092271130045505)
          ·
            refine ⟨17368364010819203347534129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23157818681092271130045505 17368364010819203347534129)
            ·
              refine ⟨13026273008114402510650597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17368364010819203347534129 13026273008114402510650597)
              ·
                refine ⟨2442426189021450470746987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13026273008114402510650597 2442426189021450470746987)
                ·
                  refine ⟨3663639283532175706120481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442426189021450470746987 3663639283532175706120481)
                  ·
                    refine ⟨2747729462649131779590361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3663639283532175706120481 2747729462649131779590361)
                    ·
                      refine ⟨2060797096986848834692771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747729462649131779590361 2060797096986848834692771)
                      ·
                        rfl

theorem cell23_4013388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_4013388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013388 prefixEnd_4013388 := by exact prefixLift 4013388
  have htrace : WordTrace (prefixWord ++ tailWord_4013388) baseStart_4013388 baseEnd_4013388 := by
    simpa [prefixWord, tailWord_4013388, baseEnd_4013388] using wordTrace_append hprefix tailTrace_4013388
  have hstable : (prefixWord ++ tailWord_4013388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013388).length < 2 ^ (prefixWord ++ tailWord_4013388).sum := by decide
  have hdescent : baseEnd_4013388 < baseStart_4013388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013405 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4013405 : Nat := 118140960795 + 4013405 * 2 ^ 59
def prefixEnd_4013405 : Nat := 4983230072969 + 3 ^ 40 * 4013405 * 2
def baseEnd_4013405 : Nat := 2060805826157975268180193

theorem tailTrace_4013405 : CollatzResearch.WordTrace tailWord_4013405 prefixEnd_4013405 2060805826157975268180193 := by
  unfold tailWord_4013405
  simp only [CollatzResearch.WordTrace]
  refine ⟨146380906025126594848841669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97587270683417729899227779 146380906025126594848841669)
  ·
    refine ⟨27446419879711236534157813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146380906025126594848841669 27446419879711236534157813)
    ·
      refine ⟨2573101863722928425077295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27446419879711236534157813 2573101863722928425077295)
      ·
        refine ⟨3859652795584392637615943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573101863722928425077295 3859652795584392637615943)
        ·
          refine ⟨5789479193376588956423915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859652795584392637615943 5789479193376588956423915)
          ·
            refine ⟨8684218790064883434635873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5789479193376588956423915 8684218790064883434635873)
            ·
              refine ⟨6513164092548662575976905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8684218790064883434635873 6513164092548662575976905)
              ·
                refine ⟨4884873069411496931982679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513164092548662575976905 4884873069411496931982679)
                ·
                  refine ⟨7327309604117245397974019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884873069411496931982679 7327309604117245397974019)
                  ·
                    refine ⟨10990964406175868096961029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7327309604117245397974019 10990964406175868096961029)
                    ·
                      refine ⟨2060805826157975268180193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10990964406175868096961029 2060805826157975268180193)
                      ·
                        rfl

theorem cell23_4013405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4013405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013405 prefixEnd_4013405 := by exact prefixLift 4013405
  have htrace : WordTrace (prefixWord ++ tailWord_4013405) baseStart_4013405 baseEnd_4013405 := by
    simpa [prefixWord, tailWord_4013405, baseEnd_4013405] using wordTrace_append hprefix tailTrace_4013405
  have hstable : (prefixWord ++ tailWord_4013405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013405).length < 2 ^ (prefixWord ++ tailWord_4013405).sum := by decide
  have hdescent : baseEnd_4013405 < baseStart_4013405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013477 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_4013477 : Nat := 118140960795 + 4013477 * 2 ^ 59
def prefixEnd_4013477 : Nat := 4983230072969 + 3 ^ 40 * 4013477 * 2
def baseEnd_4013477 : Nat := 2060842796765098986479861

theorem tailTrace_4013477 : CollatzResearch.WordTrace tailWord_4013477 prefixEnd_4013477 2060842796765098986479861 := by
  unfold tailWord_4013477
  simp only [CollatzResearch.WordTrace]
  refine ⟨146383532080865751145462685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97589021387243834096975123 146383532080865751145462685)
  ·
    refine ⟨54893824530324656679548507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146383532080865751145462685 54893824530324656679548507)
    ·
      refine ⟨82340736795486985019322761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54893824530324656679548507 82340736795486985019322761)
      ·
        refine ⟨61755552596615238764492071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82340736795486985019322761 61755552596615238764492071)
        ·
          refine ⟨92633328894922858146738107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61755552596615238764492071 92633328894922858146738107)
          ·
            refine ⟨138949993342384287220107161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92633328894922858146738107 138949993342384287220107161)
            ·
              refine ⟨104212495006788215415080371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138949993342384287220107161 104212495006788215415080371)
              ·
                refine ⟨156318742510182323122620557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104212495006788215415080371 156318742510182323122620557)
                ·
                  refine ⟨58619528441318371170982709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156318742510182323122620557 58619528441318371170982709)
                  ·
                    refine ⟨5495580791373597297279629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58619528441318371170982709 5495580791373597297279629)
                    ·
                      refine ⟨2060842796765098986479861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5495580791373597297279629 2060842796765098986479861)
                      ·
                        rfl

theorem cell23_4013477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_4013477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013477 prefixEnd_4013477 := by exact prefixLift 4013477
  have htrace : WordTrace (prefixWord ++ tailWord_4013477) baseStart_4013477 baseEnd_4013477 := by
    simpa [prefixWord, tailWord_4013477, baseEnd_4013477] using wordTrace_append hprefix tailTrace_4013477
  have hstable : (prefixWord ++ tailWord_4013477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013477).length < 2 ^ (prefixWord ++ tailWord_4013477).sum := by decide
  have hdescent : baseEnd_4013477 < baseStart_4013477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013504 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 2, 5, 2]
def baseStart_4013504 : Nat := 118140960795 + 4013504 * 2 ^ 59
def prefixEnd_4013504 : Nat := 4983230072969 + 3 ^ 40 * 4013504 * 2
def baseEnd_4013504 : Nat := 2060856660742770380842237

theorem tailTrace_4013504 : CollatzResearch.WordTrace tailWord_4013504 prefixEnd_4013504 2060856660742770380842237 := by
  unfold tailWord_4013504
  simp only [CollatzResearch.WordTrace]
  refine ⟨73192258425883967378347783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97589677901178623171130377 73192258425883967378347783)
  ·
    refine ⟨109788387638825951067521675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73192258425883967378347783 109788387638825951067521675)
    ·
      refine ⟨164682581458238926601282513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109788387638825951067521675 164682581458238926601282513)
      ·
        refine ⟨123511936093679194950961885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164682581458238926601282513 123511936093679194950961885)
        ·
          refine ⟨46316976035129698106610707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123511936093679194950961885 46316976035129698106610707)
          ·
            refine ⟨69475464052694547159916061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46316976035129698106610707 69475464052694547159916061)
            ·
              refine ⟨26053299019760455184968523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69475464052694547159916061 26053299019760455184968523)
              ·
                refine ⟨39079948529640682777452785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26053299019760455184968523 39079948529640682777452785)
                ·
                  refine ⟨29309961397230512083089589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39079948529640682777452785 29309961397230512083089589)
                  ·
                    refine ⟨2747808880990360507789649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29309961397230512083089589 2747808880990360507789649)
                    ·
                      refine ⟨2060856660742770380842237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2747808880990360507789649 2060856660742770380842237)
                      ·
                        rfl

theorem cell23_4013504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_4013504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013504 prefixEnd_4013504 := by exact prefixLift 4013504
  have htrace : WordTrace (prefixWord ++ tailWord_4013504) baseStart_4013504 baseEnd_4013504 := by
    simpa [prefixWord, tailWord_4013504, baseEnd_4013504] using wordTrace_append hprefix tailTrace_4013504
  have hstable : (prefixWord ++ tailWord_4013504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013504).length < 2 ^ (prefixWord ++ tailWord_4013504).sum := by decide
  have hdescent : baseEnd_4013504 < baseStart_4013504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013507 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 5]
def baseStart_4013507 : Nat := 118140960795 + 4013507 * 2 ^ 59
def prefixEnd_4013507 : Nat := 4983230072969 + 3 ^ 40 * 4013507 * 2
def baseEnd_4013507 : Nat := 2060858201184733869104723

theorem tailTrace_4013507 : CollatzResearch.WordTrace tailWord_4013507 prefixEnd_4013507 2060858201184733869104723 := by
  unfold tailWord_4013507
  simp only [CollatzResearch.WordTrace]
  refine ⟨146384626270757066269054775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97589750847171377512703183 146384626270757066269054775)
  ·
    refine ⟨219576939406135599403582163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146384626270757066269054775 219576939406135599403582163)
    ·
      refine ⟨329365409109203399105373245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219576939406135599403582163 329365409109203399105373245)
      ·
        refine ⟨123512028415951274664514967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329365409109203399105373245 123512028415951274664514967)
        ·
          refine ⟨185268042623926911996772451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123512028415951274664514967 185268042623926911996772451)
          ·
            refine ⟨277902063935890367995158677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185268042623926911996772451 277902063935890367995158677)
            ·
              refine ⟨13026659246994860999773063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277902063935890367995158677 13026659246994860999773063)
              ·
                refine ⟨19539988870492291499659595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13026659246994860999773063 19539988870492291499659595)
                ·
                  refine ⟨29309983305738437249489393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19539988870492291499659595 29309983305738437249489393)
                  ·
                    refine ⟨21982487479303827937117045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29309983305738437249489393 21982487479303827937117045)
                    ·
                      refine ⟨2060858201184733869104723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21982487479303827937117045 2060858201184733869104723)
                      ·
                        rfl

theorem cell23_4013507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_4013507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013507 prefixEnd_4013507 := by exact prefixLift 4013507
  have htrace : WordTrace (prefixWord ++ tailWord_4013507) baseStart_4013507 baseEnd_4013507 := by
    simpa [prefixWord, tailWord_4013507, baseEnd_4013507] using wordTrace_append hprefix tailTrace_4013507
  have hstable : (prefixWord ++ tailWord_4013507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013507).length < 2 ^ (prefixWord ++ tailWord_4013507).sum := by decide
  have hdescent : baseEnd_4013507 < baseStart_4013507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013544 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 5, 4]
def baseStart_4013544 : Nat := 118140960795 + 4013544 * 2 ^ 59
def prefixEnd_4013544 : Nat := 4983230072969 + 3 ^ 40 * 4013544 * 2
def baseEnd_4013544 : Nat := 686959066656316741447351

theorem tailTrace_4013544 : CollatzResearch.WordTrace tailWord_4013544 prefixEnd_4013544 686959066656316741447351 := by
  unfold tailWord_4013544
  simp only [CollatzResearch.WordTrace]
  refine ⟨73192987885811510794075843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97590650514415347725434457 73192987885811510794075843)
  ·
    refine ⟨109789481828717266191113765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73192987885811510794075843 109789481828717266191113765)
    ·
      refine ⟨20585527842884487410833831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109789481828717266191113765 20585527842884487410833831)
      ·
        refine ⟨30878291764326731116250747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20585527842884487410833831 30878291764326731116250747)
        ·
          refine ⟨46317437646490096674376121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30878291764326731116250747 46317437646490096674376121)
          ·
            refine ⟨34738078234867572505782091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46317437646490096674376121 34738078234867572505782091)
            ·
              refine ⟨52107117352301358758673137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34738078234867572505782091 52107117352301358758673137)
              ·
                refine ⟨39080338014226019069004853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52107117352301358758673137 39080338014226019069004853)
                ·
                  refine ⟨3663781688833689287719205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39080338014226019069004853 3663781688833689287719205)
                  ·
                    refine ⟨686959066656316741447351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3663781688833689287719205 686959066656316741447351)
                    ·
                      rfl

theorem cell23_4013544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_4013544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013544 prefixEnd_4013544 := by exact prefixLift 4013544
  have htrace : WordTrace (prefixWord ++ tailWord_4013544) baseStart_4013544 baseEnd_4013544 := by
    simpa [prefixWord, tailWord_4013544, baseEnd_4013544] using wordTrace_append hprefix tailTrace_4013544
  have hstable : (prefixWord ++ tailWord_4013544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013544).length < 2 ^ (prefixWord ++ tailWord_4013544).sum := by decide
  have hdescent : baseEnd_4013544 < baseStart_4013544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013577 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_4013577 : Nat := 118140960795 + 4013577 * 2 ^ 59
def prefixEnd_4013577 : Nat := 4983230072969 + 3 ^ 40 * 4013577 * 2
def baseEnd_4013577 : Nat := 2060894144830548595229401

theorem tailTrace_4013577 : CollatzResearch.WordTrace tailWord_4013577 prefixEnd_4013577 2060894144830548595229401 := by
  unfold tailWord_4013577
  simp only [CollatzResearch.WordTrace]
  refine ⟨146387179380503468224102985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97591452920335645482735323 146387179380503468224102985)
  ·
    refine ⟨109790384535377601168077239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146387179380503468224102985 109790384535377601168077239)
    ·
      refine ⟨164685576803066401752115859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109790384535377601168077239 164685576803066401752115859)
      ·
        refine ⟨247028365204599602628173789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164685576803066401752115859 247028365204599602628173789)
        ·
          refine ⟨92635636951724850985565171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247028365204599602628173789 92635636951724850985565171)
          ·
            refine ⟨138953455427587276478347757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92635636951724850985565171 138953455427587276478347757)
            ·
              refine ⟨52107545785345228679380409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138953455427587276478347757 52107545785345228679380409)
              ·
                refine ⟨39080659339008921509535307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52107545785345228679380409 39080659339008921509535307)
                ·
                  refine ⟨58620989008513382264302961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39080659339008921509535307 58620989008513382264302961)
                  ·
                    refine ⟨43965741756385036698227221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58620989008513382264302961 43965741756385036698227221)
                    ·
                      refine ⟨2060894144830548595229401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43965741756385036698227221 2060894144830548595229401)
                      ·
                        rfl

theorem cell23_4013577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_4013577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013577 prefixEnd_4013577 := by exact prefixLift 4013577
  have htrace : WordTrace (prefixWord ++ tailWord_4013577) baseStart_4013577 baseEnd_4013577 := by
    simpa [prefixWord, tailWord_4013577, baseEnd_4013577] using wordTrace_append hprefix tailTrace_4013577
  have hstable : (prefixWord ++ tailWord_4013577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013577).length < 2 ^ (prefixWord ++ tailWord_4013577).sum := by decide
  have hdescent : baseEnd_4013577 < baseStart_4013577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013668 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_4013668 : Nat := 118140960795 + 4013668 * 2 ^ 59
def prefixEnd_4013668 : Nat := 4983230072969 + 3 ^ 40 * 4013668 * 2
def baseEnd_4013668 : Nat := 686980290523369246397161

theorem tailTrace_4013668 : CollatzResearch.WordTrace tailWord_4013668 prefixEnd_4013668 686980290523369246397161 := by
  unfold tailWord_4013668
  simp only [CollatzResearch.WordTrace]
  refine ⟨73195249211586895382832829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97593665615449193843777105 73195249211586895382832829)
  ·
    refine ⟨27448218454345085768562311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73195249211586895382832829 27448218454345085768562311)
    ·
      refine ⟨41172327681517628652843467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27448218454345085768562311 41172327681517628652843467)
      ·
        refine ⟨61758491522276442979265201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41172327681517628652843467 61758491522276442979265201)
        ·
          refine ⟨46318868641707332234448901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61758491522276442979265201 46318868641707332234448901)
          ·
            refine ⟨8684787870320124793959169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46318868641707332234448901 8684787870320124793959169)
            ·
              refine ⟨6513590902740093595469377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8684787870320124793959169 6513590902740093595469377)
              ·
                refine ⟨4885193177055070196602033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513590902740093595469377 4885193177055070196602033)
                ·
                  refine ⟨3663894882791302647451525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4885193177055070196602033 3663894882791302647451525)
                  ·
                    refine ⟨686980290523369246397161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3663894882791302647451525 686980290523369246397161)
                    ·
                      rfl

theorem cell23_4013668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_4013668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013668 prefixEnd_4013668 := by exact prefixLift 4013668
  have htrace : WordTrace (prefixWord ++ tailWord_4013668) baseStart_4013668 baseEnd_4013668 := by
    simpa [prefixWord, tailWord_4013668, baseEnd_4013668] using wordTrace_append hprefix tailTrace_4013668
  have hstable : (prefixWord ++ tailWord_4013668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013668).length < 2 ^ (prefixWord ++ tailWord_4013668).sum := by decide
  have hdescent : baseEnd_4013668 < baseStart_4013668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013691 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 3]
def baseStart_4013691 : Nat := 118140960795 + 4013691 * 2 ^ 59
def prefixEnd_4013691 : Nat := 4983230072969 + 3 ^ 40 * 4013691 * 2
def baseEnd_4013691 : Nat := 2060952681625161149203877

theorem tailTrace_4013691 : CollatzResearch.WordTrace tailWord_4013691 prefixEnd_4013691 2060952681625161149203877 := by
  unfold tailWord_4013691
  simp only [CollatzResearch.WordTrace]
  refine ⟨146391337302090465693752927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97594224868060310462501951 146391337302090465693752927)
  ·
    refine ⟨219587005953135698540629391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146391337302090465693752927 219587005953135698540629391)
    ·
      refine ⟨329380508929703547810944087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219587005953135698540629391 329380508929703547810944087)
      ·
        refine ⟨494070763394555321716416131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329380508929703547810944087 494070763394555321716416131)
        ·
          refine ⟨741106145091832982574624197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494070763394555321716416131 741106145091832982574624197)
          ·
            refine ⟨138957402204718684232742037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 741106145091832982574624197 138957402204718684232742037)
            ·
              refine ⟨6513628228346188323409783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138957402204718684232742037 6513628228346188323409783)
              ·
                refine ⟨9770442342519282485114675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513628228346188323409783 9770442342519282485114675)
                ·
                  refine ⟨14655663513778923727672013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9770442342519282485114675 14655663513778923727672013)
                  ·
                    refine ⟨5495873817667096397877005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14655663513778923727672013 5495873817667096397877005)
                    ·
                      refine ⟨2060952681625161149203877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5495873817667096397877005 2060952681625161149203877)
                      ·
                        rfl

theorem cell23_4013691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 3].length) (baseStart_4013691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013691 prefixEnd_4013691 := by exact prefixLift 4013691
  have htrace : WordTrace (prefixWord ++ tailWord_4013691) baseStart_4013691 baseEnd_4013691 := by
    simpa [prefixWord, tailWord_4013691, baseEnd_4013691] using wordTrace_append hprefix tailTrace_4013691
  have hstable : (prefixWord ++ tailWord_4013691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013691).length < 2 ^ (prefixWord ++ tailWord_4013691).sum := by decide
  have hdescent : baseEnd_4013691 < baseStart_4013691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013741 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_4013741 : Nat := 118140960795 + 4013741 * 2 ^ 59
def prefixEnd_4013741 : Nat := 4983230072969 + 3 ^ 40 * 4013741 * 2
def baseEnd_4013741 : Nat := 686992785219295317859549

theorem tailTrace_4013741 : CollatzResearch.WordTrace tailWord_4013741 prefixEnd_4013741 686992785219295317859549 := by
  unfold tailWord_4013741
  simp only [CollatzResearch.WordTrace]
  refine ⟨146393160951909324233073077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97595440634606216155382051 146393160951909324233073077)
  ·
    refine ⟨13724358839241499146850601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146393160951909324233073077 13724358839241499146850601)
    ·
      refine ⟨10293269129431124360137951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13724358839241499146850601 10293269129431124360137951)
      ·
        refine ⟨15439903694146686540206927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10293269129431124360137951 15439903694146686540206927)
        ·
          refine ⟨23159855541220029810310391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15439903694146686540206927 23159855541220029810310391)
          ·
            refine ⟨34739783311830044715465587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23159855541220029810310391 34739783311830044715465587)
            ·
              refine ⟨52109674967745067073198381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34739783311830044715465587 52109674967745067073198381)
              ·
                refine ⟨19541128112904400152449393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52109674967745067073198381 19541128112904400152449393)
                ·
                  refine ⟨14655846084678300114337045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19541128112904400152449393 14655846084678300114337045)
                  ·
                    refine ⟨686992785219295317859549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14655846084678300114337045 686992785219295317859549)
                    ·
                      rfl

theorem cell23_4013741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_4013741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013741 prefixEnd_4013741 := by exact prefixLift 4013741
  have htrace : WordTrace (prefixWord ++ tailWord_4013741) baseStart_4013741 baseEnd_4013741 := by
    simpa [prefixWord, tailWord_4013741, baseEnd_4013741] using wordTrace_append hprefix tailTrace_4013741
  have hstable : (prefixWord ++ tailWord_4013741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013741).length < 2 ^ (prefixWord ++ tailWord_4013741).sum := by decide
  have hdescent : baseEnd_4013741 < baseStart_4013741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013742 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4013742 : Nat := 118140960795 + 4013742 * 2 ^ 59
def prefixEnd_4013742 : Nat := 4983230072969 + 3 ^ 40 * 4013742 * 2
def baseEnd_4013742 : Nat := 2060978869138540449666143

theorem tailTrace_4013742 : CollatzResearch.WordTrace tailWord_4013742 prefixEnd_4013742 2060978869138540449666143 := by
  unfold tailWord_4013742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18299149678113212675482435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97595464949937134269239653 18299149678113212675482435)
  ·
    refine ⟨27448724517169819013223653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18299149678113212675482435 27448724517169819013223653)
    ·
      refine ⟨5146635846969341064979435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27448724517169819013223653 5146635846969341064979435)
      ·
        refine ⟨7719953770454011597469153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5146635846969341064979435 7719953770454011597469153)
        ·
          refine ⟨5789965327840508698101865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7719953770454011597469153 5789965327840508698101865)
          ·
            refine ⟨4342473995880381523576399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5789965327840508698101865 4342473995880381523576399)
            ·
              refine ⟨6513710993820572285364599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342473995880381523576399 6513710993820572285364599)
              ·
                refine ⟨9770566490730858428046899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513710993820572285364599 9770566490730858428046899)
                ·
                  refine ⟨14655849736096287642070349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9770566490730858428046899 14655849736096287642070349)
                  ·
                    refine ⟨5495943651036107865776381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14655849736096287642070349 5495943651036107865776381)
                    ·
                      refine ⟨2060978869138540449666143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5495943651036107865776381 2060978869138540449666143)
                      ·
                        rfl

theorem cell23_4013742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4013742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013742 prefixEnd_4013742 := by exact prefixLift 4013742
  have htrace : WordTrace (prefixWord ++ tailWord_4013742) baseStart_4013742 baseEnd_4013742 := by
    simpa [prefixWord, tailWord_4013742, baseEnd_4013742] using wordTrace_append hprefix tailTrace_4013742
  have hstable : (prefixWord ++ tailWord_4013742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013742).length < 2 ^ (prefixWord ++ tailWord_4013742).sum := by decide
  have hdescent : baseEnd_4013742 < baseStart_4013742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013799 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4013799 : Nat := 118140960795 + 4013799 * 2 ^ 59
def prefixEnd_4013799 : Nat := 4983230072969 + 3 ^ 40 * 4013799 * 2
def baseEnd_4013799 : Nat := 2061008137535846726653381

theorem tailTrace_4013799 : CollatzResearch.WordTrace tailWord_4013799 prefixEnd_4013799 2061008137535846726653381 := by
  unfold tailWord_4013799
  simp only [CollatzResearch.WordTrace]
  refine ⟨146395276385699200138684451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97596850923799466759122967 146395276385699200138684451)
  ·
    refine ⟨219592914578548800208026677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146395276385699200138684451 219592914578548800208026677)
    ·
      refine ⟨20586835741738950019502501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219592914578548800208026677 20586835741738950019502501)
      ·
        refine ⟨3860031701576053128656719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20586835741738950019502501 3860031701576053128656719)
        ·
          refine ⟨5790047552364079692985079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860031701576053128656719 5790047552364079692985079)
          ·
            refine ⟨8685071328546119539477619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790047552364079692985079 8685071328546119539477619)
            ·
              refine ⟨13027606992819179309216429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8685071328546119539477619 13027606992819179309216429)
              ·
                refine ⟨4885352622307192240956161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13027606992819179309216429 4885352622307192240956161)
                ·
                  refine ⟨3664014466730394180717121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4885352622307192240956161 3664014466730394180717121)
                  ·
                    refine ⟨2748010850047795635537841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3664014466730394180717121 2748010850047795635537841)
                    ·
                      refine ⟨2061008137535846726653381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748010850047795635537841 2061008137535846726653381)
                      ·
                        rfl

theorem cell23_4013799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4013799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013799 prefixEnd_4013799 := by exact prefixLift 4013799
  have htrace : WordTrace (prefixWord ++ tailWord_4013799) baseStart_4013799 baseEnd_4013799 := by
    simpa [prefixWord, tailWord_4013799, baseEnd_4013799] using wordTrace_append hprefix tailTrace_4013799
  have hstable : (prefixWord ++ tailWord_4013799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013799).length < 2 ^ (prefixWord ++ tailWord_4013799).sum := by decide
  have hdescent : baseEnd_4013799 < baseStart_4013799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013838 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4013838 : Nat := 118140960795 + 4013838 * 2 ^ 59
def prefixEnd_4013838 : Nat := 4983230072969 + 3 ^ 40 * 4013838 * 2
def baseEnd_4013838 : Nat := 2061028163281372074065701

theorem tailTrace_4013838 : CollatzResearch.WordTrace tailWord_4013838 prefixEnd_4013838 2061028163281372074065701 := by
  unfold tailWord_4013838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18299587354069738724919271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97597799221705273199569445 18299587354069738724919271)
  ·
    refine ⟨27449381031104608087378907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18299587354069738724919271 27449381031104608087378907)
    ·
      refine ⟨41174071546656912131068361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27449381031104608087378907 41174071546656912131068361)
      ·
        refine ⟨30880553659992684098301271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41174071546656912131068361 30880553659992684098301271)
        ·
          refine ⟨46320830489989026147451907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30880553659992684098301271 46320830489989026147451907)
          ·
            refine ⟨69481245734983539221177861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46320830489989026147451907 69481245734983539221177861)
            ·
              refine ⟨13027733575309413603970849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69481245734983539221177861 13027733575309413603970849)
              ·
                refine ⟨9770800181482060202978137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13027733575309413603970849 9770800181482060202978137)
                ·
                  refine ⟨7328100136111545152233603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9770800181482060202978137 7328100136111545152233603)
                  ·
                    refine ⟨10992150204167317728350405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7328100136111545152233603 10992150204167317728350405)
                    ·
                      refine ⟨2061028163281372074065701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10992150204167317728350405 2061028163281372074065701)
                      ·
                        rfl

theorem cell23_4013838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4013838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013838 prefixEnd_4013838 := by exact prefixLift 4013838
  have htrace : WordTrace (prefixWord ++ tailWord_4013838) baseStart_4013838 baseEnd_4013838 := by
    simpa [prefixWord, tailWord_4013838, baseEnd_4013838] using wordTrace_append hprefix tailTrace_4013838
  have hstable : (prefixWord ++ tailWord_4013838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013838).length < 2 ^ (prefixWord ++ tailWord_4013838).sum := by decide
  have hdescent : baseEnd_4013838 < baseStart_4013838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013841 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_4013841 : Nat := 118140960795 + 4013841 * 2 ^ 59
def prefixEnd_4013841 : Nat := 4983230072969 + 3 ^ 40 * 4013841 * 2
def baseEnd_4013841 : Nat := 2061029703723335562328187

theorem tailTrace_4013841 : CollatzResearch.WordTrace tailWord_4013841 prefixEnd_4013841 2061029703723335562328187 := by
  unfold tailWord_4013841
  simp only [CollatzResearch.WordTrace]
  refine ⟨146396808251547041311713377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97597872167698027541142251 146396808251547041311713377)
  ·
    refine ⟨109797606188660280983785033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146396808251547041311713377 109797606188660280983785033)
    ·
      refine ⟨82348204641495210737838775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109797606188660280983785033 82348204641495210737838775)
      ·
        refine ⟨123522306962242816106758163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82348204641495210737838775 123522306962242816106758163)
        ·
          refine ⟨185283460443364224160137245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123522306962242816106758163 185283460443364224160137245)
          ·
            refine ⟨69481297666261584060051467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185283460443364224160137245 69481297666261584060051467)
            ·
              refine ⟨104221946499392376090077201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69481297666261584060051467 104221946499392376090077201)
              ·
                refine ⟨78166459874544282067557901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104221946499392376090077201 78166459874544282067557901)
                ·
                  refine ⟨29312422452954105775334213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78166459874544282067557901 29312422452954105775334213)
                  ·
                    refine ⟨5496079209928894832875165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29312422452954105775334213 5496079209928894832875165)
                    ·
                      refine ⟨2061029703723335562328187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5496079209928894832875165 2061029703723335562328187)
                      ·
                        rfl

theorem cell23_4013841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_4013841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013841 prefixEnd_4013841 := by exact prefixLift 4013841
  have htrace : WordTrace (prefixWord ++ tailWord_4013841) baseStart_4013841 baseEnd_4013841 := by
    simpa [prefixWord, tailWord_4013841, baseEnd_4013841] using wordTrace_append hprefix tailTrace_4013841
  have hstable : (prefixWord ++ tailWord_4013841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013841).length < 2 ^ (prefixWord ++ tailWord_4013841).sum := by decide
  have hdescent : baseEnd_4013841 < baseStart_4013841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013858 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_4013858 : Nat := 118140960795 + 4013858 * 2 ^ 59
def prefixEnd_4013858 : Nat := 4983230072969 + 3 ^ 40 * 4013858 * 2
def baseEnd_4013858 : Nat := 2061038432894461995815609

theorem tailTrace_4013858 : CollatzResearch.WordTrace tailWord_4013858 prefixEnd_4013858 2061038432894461995815609 := by
  unfold tailWord_4013858
  simp only [CollatzResearch.WordTrace]
  refine ⟨36599357073121363303770557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97598285528323635476721485 36599357073121363303770557)
  ·
    refine ⟨13724758902420511238913959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36599357073121363303770557 13724758902420511238913959)
    ·
      refine ⟨20587138353630766858370939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13724758902420511238913959 20587138353630766858370939)
      ·
        refine ⟨30880707530446150287556409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20587138353630766858370939 30880707530446150287556409)
        ·
          refine ⟨23160530647834612715667307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30880707530446150287556409 23160530647834612715667307)
          ·
            refine ⟨34740795971751919073500961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23160530647834612715667307 34740795971751919073500961)
            ·
              refine ⟨26055596978813939305125721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34740795971751919073500961 26055596978813939305125721)
              ·
                refine ⟨19541697734110454478844291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26055596978813939305125721 19541697734110454478844291)
                ·
                  refine ⟨29312546601165681718266437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19541697734110454478844291 29312546601165681718266437)
                  ·
                    refine ⟨5496102487718565322174957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29312546601165681718266437 5496102487718565322174957)
                    ·
                      refine ⟨2061038432894461995815609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5496102487718565322174957 2061038432894461995815609)
                      ·
                        rfl

theorem cell23_4013858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_4013858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013858 prefixEnd_4013858 := by exact prefixLift 4013858
  have htrace : WordTrace (prefixWord ++ tailWord_4013858) baseStart_4013858 baseEnd_4013858 := by
    simpa [prefixWord, tailWord_4013858, baseEnd_4013858] using wordTrace_append hprefix tailTrace_4013858
  have hstable : (prefixWord ++ tailWord_4013858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013858).length < 2 ^ (prefixWord ++ tailWord_4013858).sum := by decide
  have hdescent : baseEnd_4013858 < baseStart_4013858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013871 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 3]
def baseStart_4013871 : Nat := 118140960795 + 4013871 * 2 ^ 59
def prefixEnd_4013871 : Nat := 4983230072969 + 3 ^ 40 * 4013871 * 2
def baseEnd_4013871 : Nat := 2061045108142970444953049

theorem tailTrace_4013871 : CollatzResearch.WordTrace tailWord_4013871 prefixEnd_4013871 2061045108142970444953049 := by
  unfold tailWord_4013871
  simp only [CollatzResearch.WordTrace]
  refine ⟨146397902441438356435305467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97598601627625570956870311 146397902441438356435305467)
  ·
    refine ⟨219596853662157534652958201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146397902441438356435305467 219596853662157534652958201)
    ·
      refine ⟨164697640246618150989718651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219596853662157534652958201 164697640246618150989718651)
      ·
        refine ⟨247046460369927226484577977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164697640246618150989718651 247046460369927226484577977)
        ·
          refine ⟨185284845277445419863433483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247046460369927226484577977 185284845277445419863433483)
          ·
            refine ⟨277927267916168129795150225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185284845277445419863433483 277927267916168129795150225)
            ·
              refine ⟨208445450937126097346362669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277927267916168129795150225 208445450937126097346362669)
              ·
                refine ⟨78167044101422286504886001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208445450937126097346362669 78167044101422286504886001)
                ·
                  refine ⟨58625283076066714878664501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78167044101422286504886001 58625283076066714878664501)
                  ·
                    refine ⟨5496120288381254519874797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58625283076066714878664501 5496120288381254519874797)
                    ·
                      refine ⟨2061045108142970444953049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5496120288381254519874797 2061045108142970444953049)
                      ·
                        rfl

theorem cell23_4013871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_4013871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013871 prefixEnd_4013871 := by exact prefixLift 4013871
  have htrace : WordTrace (prefixWord ++ tailWord_4013871) baseStart_4013871 baseEnd_4013871 := by
    simpa [prefixWord, tailWord_4013871, baseEnd_4013871] using wordTrace_append hprefix tailTrace_4013871
  have hstable : (prefixWord ++ tailWord_4013871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013871).length < 2 ^ (prefixWord ++ tailWord_4013871).sum := by decide
  have hdescent : baseEnd_4013871 < baseStart_4013871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013882 : List Nat := [3, 1, 1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_4013882 : Nat := 118140960795 + 4013882 * 2 ^ 59
def prefixEnd_4013882 : Nat := 4983230072969 + 3 ^ 40 * 4013882 * 2
def baseEnd_4013882 : Nat := 687016918810056633971833

theorem tailTrace_4013882 : CollatzResearch.WordTrace tailWord_4013882 prefixEnd_4013882 687016918810056633971833 := by
  unfold tailWord_4013882
  simp only [CollatzResearch.WordTrace]
  refine ⟨36599575911099626328488975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97598869096265670209303933 36599575911099626328488975)
  ·
    refine ⟨54899363866649439492733463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36599575911099626328488975 54899363866649439492733463)
    ·
      refine ⟨82349045799974159239100195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54899363866649439492733463 82349045799974159239100195)
      ·
        refine ⟨123523568699961238858650293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82349045799974159239100195 123523568699961238858650293)
        ·
          refine ⟨11580334565621366142998465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123523568699961238858650293 11580334565621366142998465)
          ·
            refine ⟨8685250924216024607248849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11580334565621366142998465 8685250924216024607248849)
            ·
              refine ⟨6513938193162018455436637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8685250924216024607248849 6513938193162018455436637)
              ·
                refine ⟨2442726822435756920788739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6513938193162018455436637 2442726822435756920788739)
                ·
                  refine ⟨3664090233653635381183109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442726822435756920788739 3664090233653635381183109)
                  ·
                    refine ⟨687016918810056633971833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3664090233653635381183109 687016918810056633971833)
                    ·
                      rfl

theorem cell23_4013882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_4013882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013882 prefixEnd_4013882 := by exact prefixLift 4013882
  have htrace : WordTrace (prefixWord ++ tailWord_4013882) baseStart_4013882 baseEnd_4013882 := by
    simpa [prefixWord, tailWord_4013882, baseEnd_4013882] using wordTrace_append hprefix tailTrace_4013882
  have hstable : (prefixWord ++ tailWord_4013882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013882).length < 2 ^ (prefixWord ++ tailWord_4013882).sum := by decide
  have hdescent : baseEnd_4013882 < baseStart_4013882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013905 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 3]
def baseStart_4013905 : Nat := 118140960795 + 4013905 * 2 ^ 59
def prefixEnd_4013905 : Nat := 4983230072969 + 3 ^ 40 * 4013905 * 2
def baseEnd_4013905 : Nat := 2061062566485223311927893

theorem tailTrace_4013905 : CollatzResearch.WordTrace tailWord_4013905 prefixEnd_4013905 2061062566485223311927893 := by
  unfold tailWord_4013905
  simp only [CollatzResearch.WordTrace]
  refine ⟨146399142523315180242043169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97599428348876786828028779 146399142523315180242043169)
  ·
    refine ⟨109799356892486385181532377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146399142523315180242043169 109799356892486385181532377)
    ·
      refine ⟨82349517669364788886149283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109799356892486385181532377 82349517669364788886149283)
      ·
        refine ⟨123524276504047183329223925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82349517669364788886149283 123524276504047183329223925)
        ·
          refine ⟨11580400922254423437114743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123524276504047183329223925 11580400922254423437114743)
          ·
            refine ⟨17370601383381635155672115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11580400922254423437114743 17370601383381635155672115)
            ·
              refine ⟨26055902075072452733508173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17370601383381635155672115 26055902075072452733508173)
              ·
                refine ⟨9770963278152169775065565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26055902075072452733508173 9770963278152169775065565)
                ·
                  refine ⟨3664111229307063665649587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9770963278152169775065565 3664111229307063665649587)
                  ·
                    refine ⟨5496166843960595498474381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3664111229307063665649587 5496166843960595498474381)
                    ·
                      refine ⟨2061062566485223311927893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5496166843960595498474381 2061062566485223311927893)
                      ·
                        rfl

theorem cell23_4013905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_4013905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013905 prefixEnd_4013905 := by exact prefixLift 4013905
  have htrace : WordTrace (prefixWord ++ tailWord_4013905) baseStart_4013905 baseEnd_4013905 := by
    simpa [prefixWord, tailWord_4013905, baseEnd_4013905] using wordTrace_append hprefix tailTrace_4013905
  have hstable : (prefixWord ++ tailWord_4013905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013905).length < 2 ^ (prefixWord ++ tailWord_4013905).sum := by decide
  have hdescent : baseEnd_4013905 < baseStart_4013905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013922 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4013922 : Nat := 118140960795 + 4013922 * 2 ^ 59
def prefixEnd_4013922 : Nat := 4983230072969 + 3 ^ 40 * 4013922 * 2
def baseEnd_4013922 : Nat := 2061071295656349745415315

theorem tailTrace_4013922 : CollatzResearch.WordTrace tailWord_4013922 prefixEnd_4013922 2061071295656349745415315 := by
  unfold tailWord_4013922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36599940641063398036353005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97599841709502394763608013 36599940641063398036353005)
  ·
    refine ⟨13724977740398774263632377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36599940641063398036353005 13724977740398774263632377)
    ·
      refine ⟨10293733305299080697724283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13724977740398774263632377 10293733305299080697724283)
      ·
        refine ⟨15440599957948621046586425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10293733305299080697724283 15440599957948621046586425)
        ·
          refine ⟨11580449968461465784939819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15440599957948621046586425 11580449968461465784939819)
          ·
            refine ⟨17370674952692198677409729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11580449968461465784939819 17370674952692198677409729)
            ·
              refine ⟨13028006214519149008057297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17370674952692198677409729 13028006214519149008057297)
              ·
                refine ⟨9771004660889361756042973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13028006214519149008057297 9771004660889361756042973)
                ·
                  refine ⟨3664126747833510658516115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9771004660889361756042973 3664126747833510658516115)
                  ·
                    refine ⟨5496190121750265987774173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3664126747833510658516115 5496190121750265987774173)
                    ·
                      refine ⟨2061071295656349745415315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5496190121750265987774173 2061071295656349745415315)
                      ·
                        rfl

theorem cell23_4013922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4013922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013922 prefixEnd_4013922 := by exact prefixLift 4013922
  have htrace : WordTrace (prefixWord ++ tailWord_4013922) baseStart_4013922 baseEnd_4013922 := by
    simpa [prefixWord, tailWord_4013922, baseEnd_4013922] using wordTrace_append hprefix tailTrace_4013922
  have hstable : (prefixWord ++ tailWord_4013922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013922).length < 2 ^ (prefixWord ++ tailWord_4013922).sum := by decide
  have hdescent : baseEnd_4013922 < baseStart_4013922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013931 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 5]
def baseStart_4013931 : Nat := 118140960795 + 4013931 * 2 ^ 59
def prefixEnd_4013931 : Nat := 4983230072969 + 3 ^ 40 * 4013931 * 2
def baseEnd_4013931 : Nat := 2061075916982240210202773

theorem tailTrace_4013931 : CollatzResearch.WordTrace tailWord_4013931 prefixEnd_4013931 2061075916982240210202773 := by
  unfold tailWord_4013931
  simp only [CollatzResearch.WordTrace]
  refine ⟨146400090821220986682489647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97600060547480657788326431 146400090821220986682489647)
  ·
    refine ⟨219600136231831480023734471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146400090821220986682489647 219600136231831480023734471)
    ·
      refine ⟨329400204347747220035601707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219600136231831480023734471 329400204347747220035601707)
      ·
        refine ⟨494100306521620830053402561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329400204347747220035601707 494100306521620830053402561)
        ·
          refine ⟨370575229891215622540051921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494100306521620830053402561 370575229891215622540051921)
          ·
            refine ⟨277931422418411716905038941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370575229891215622540051921 277931422418411716905038941)
            ·
              refine ⟨104224283406904393839389603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277931422418411716905038941 104224283406904393839389603)
              ·
                refine ⟨156336425110356590759084405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104224283406904393839389603 156336425110356590759084405)
                ·
                  refine ⟨14656539854095930383664163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156336425110356590759084405 14656539854095930383664163)
                  ·
                    refine ⟨21984809781143895575496245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14656539854095930383664163 21984809781143895575496245)
                    ·
                      refine ⟨2061075916982240210202773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21984809781143895575496245 2061075916982240210202773)
                      ·
                        rfl

theorem cell23_4013931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 5].length) (baseStart_4013931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013931 prefixEnd_4013931 := by exact prefixLift 4013931
  have htrace : WordTrace (prefixWord ++ tailWord_4013931) baseStart_4013931 baseEnd_4013931 := by
    simpa [prefixWord, tailWord_4013931, baseEnd_4013931] using wordTrace_append hprefix tailTrace_4013931
  have hstable : (prefixWord ++ tailWord_4013931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013931).length < 2 ^ (prefixWord ++ tailWord_4013931).sum := by decide
  have hdescent : baseEnd_4013931 < baseStart_4013931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013948 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_4013948 : Nat := 118140960795 + 4013948 * 2 ^ 59
def prefixEnd_4013948 : Nat := 4983230072969 + 3 ^ 40 * 4013948 * 2
def baseEnd_4013948 : Nat := 2061084646153366643690195

theorem tailTrace_4013948 : CollatzResearch.WordTrace tailWord_4013948 prefixEnd_4013948 2061084646153366643690195 := by
  unfold tailWord_4013948
  simp only [CollatzResearch.WordTrace]
  refine ⟨73200355431079699292929249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97600473908106265723905665 73200355431079699292929249)
  ·
    refine ⟨54900266573309774469696937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73200355431079699292929249 54900266573309774469696937)
    ·
      refine ⟨41175199929982330852272703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54900266573309774469696937 41175199929982330852272703)
      ·
        refine ⟨61762799894973496278409055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41175199929982330852272703 61762799894973496278409055)
        ·
          refine ⟨92644199842460244417613583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61762799894973496278409055 92644199842460244417613583)
          ·
            refine ⟨138966299763690366626420375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92644199842460244417613583 138966299763690366626420375)
            ·
              refine ⟨208449449645535549939630563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138966299763690366626420375 208449449645535549939630563)
              ·
                refine ⟨312674174468303324909445845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208449449645535549939630563 312674174468303324909445845)
                ·
                  refine ⟨7328300964100859177565137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 312674174468303324909445845 7328300964100859177565137)
                  ·
                    refine ⟨5496225723075644383173853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7328300964100859177565137 5496225723075644383173853)
                    ·
                      refine ⟨2061084646153366643690195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5496225723075644383173853 2061084646153366643690195)
                      ·
                        rfl

theorem cell23_4013948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_4013948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013948 prefixEnd_4013948 := by exact prefixLift 4013948
  have htrace : WordTrace (prefixWord ++ tailWord_4013948) baseStart_4013948 baseEnd_4013948 := by
    simpa [prefixWord, tailWord_4013948, baseEnd_4013948] using wordTrace_append hprefix tailTrace_4013948
  have hstable : (prefixWord ++ tailWord_4013948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013948).length < 2 ^ (prefixWord ++ tailWord_4013948).sum := by decide
  have hdescent : baseEnd_4013948 < baseStart_4013948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4013972 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_4013972 : Nat := 118140960795 + 4013972 * 2 ^ 59
def prefixEnd_4013972 : Nat := 4983230072969 + 3 ^ 40 * 4013972 * 2
def baseEnd_4013972 : Nat := 687032323229691516596695

theorem tailTrace_4013972 : CollatzResearch.WordTrace tailWord_4013972 prefixEnd_4013972 687032323229691516596695 := by
  unfold tailWord_4013972
  simp only [CollatzResearch.WordTrace]
  refine ⟨73200793107036225342366085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97601057476048300456488113 73200793107036225342366085)
  ·
    refine ⟨13725148707569292251693641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73200793107036225342366085 13725148707569292251693641)
    ·
      refine ⟨10293861530676969188770231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13725148707569292251693641 10293861530676969188770231)
      ·
        refine ⟨15440792296015453783155347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10293861530676969188770231 15440792296015453783155347)
        ·
          refine ⟨23161188444023180674733021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15440792296015453783155347 23161188444023180674733021)
          ·
            refine ⟨8685445666508692753024883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23161188444023180674733021 8685445666508692753024883)
            ·
              refine ⟨13028168499763039129537325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8685445666508692753024883 13028168499763039129537325)
              ·
                refine ⟨4885563187411139673576497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13028168499763039129537325 4885563187411139673576497)
                ·
                  refine ⟨3664172390558354755182373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4885563187411139673576497 3664172390558354755182373)
                  ·
                    refine ⟨687032323229691516596695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3664172390558354755182373 687032323229691516596695)
                    ·
                      rfl

theorem cell23_4013972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_4013972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4013972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4013972 prefixEnd_4013972 := by exact prefixLift 4013972
  have htrace : WordTrace (prefixWord ++ tailWord_4013972) baseStart_4013972 baseEnd_4013972 := by
    simpa [prefixWord, tailWord_4013972, baseEnd_4013972] using wordTrace_append hprefix tailTrace_4013972
  have hstable : (prefixWord ++ tailWord_4013972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4013972).length < 2 ^ (prefixWord ++ tailWord_4013972).sum := by decide
  have hdescent : baseEnd_4013972 < baseStart_4013972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4013972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014013 : List Nat := [1, 4, 1, 2, 3, 3, 2, 2, 1, 2, 2]
def baseStart_4014013 : Nat := 118140960795 + 4014013 * 2 ^ 59
def prefixEnd_4014013 : Nat := 4983230072969 + 3 ^ 40 * 4014013 * 2
def baseEnd_4014013 : Nat := 2061118022395908889377397

theorem tailTrace_4014013 : CollatzResearch.WordTrace tailWord_4014013 prefixEnd_4014013 2061118022395908889377397 := by
  unfold tailWord_4014013
  simp only [CollatzResearch.WordTrace]
  refine ⟨146403081606923914686974693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97602054404615943124649795 146403081606923914686974693)
  ·
    refine ⟨27450577801298234003807755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146403081606923914686974693 27450577801298234003807755)
    ·
      refine ⟨41175866701947351005711633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27450577801298234003807755 41175866701947351005711633)
      ·
        refine ⟨30881900026460513254283725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41175866701947351005711633 30881900026460513254283725)
        ·
          refine ⟨11580712509922692470356397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30881900026460513254283725 11580712509922692470356397)
          ·
            refine ⟨4342767191221009676383649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11580712509922692470356397 4342767191221009676383649)
            ·
              refine ⟨3257075393415757257287737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4342767191221009676383649 3257075393415757257287737)
              ·
                refine ⟨2442806545061817942965803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3257075393415757257287737 2442806545061817942965803)
                ·
                  refine ⟨3664209817592726914448705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442806545061817942965803 3664209817592726914448705)
                  ·
                    refine ⟨2748157363194545185836529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3664209817592726914448705 2748157363194545185836529)
                    ·
                      refine ⟨2061118022395908889377397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748157363194545185836529 2061118022395908889377397)
                      ·
                        rfl

theorem cell23_4014013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_4014013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014013 prefixEnd_4014013 := by exact prefixLift 4014013
  have htrace : WordTrace (prefixWord ++ tailWord_4014013) baseStart_4014013 baseEnd_4014013 := by
    simpa [prefixWord, tailWord_4014013, baseEnd_4014013] using wordTrace_append hprefix tailTrace_4014013
  have hstable : (prefixWord ++ tailWord_4014013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014013).length < 2 ^ (prefixWord ++ tailWord_4014013).sum := by decide
  have hdescent : baseEnd_4014013 < baseStart_4014013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014028 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_4014028 : Nat := 118140960795 + 4014028 * 2 ^ 59
def prefixEnd_4014028 : Nat := 4983230072969 + 3 ^ 40 * 4014028 * 2
def baseEnd_4014028 : Nat := 687041908201908776896609

theorem tailTrace_4014028 : CollatzResearch.WordTrace tailWord_4014028 prefixEnd_4014028 687041908201908776896609 := by
  unfold tailWord_4014028
  simp only [CollatzResearch.WordTrace]
  refine ⟨73201814350934786124385369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97602419134579714832513825 73201814350934786124385369)
  ·
    refine ⟨54901360763201089593289027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73201814350934786124385369 54901360763201089593289027)
    ·
      refine ⟨82352041144801634389933541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54901360763201089593289027 82352041144801634389933541)
      ·
        refine ⟨15441007714650306448112539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82352041144801634389933541 15441007714650306448112539)
        ·
          refine ⟨23161511571975459672168809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15441007714650306448112539 23161511571975459672168809)
          ·
            refine ⟨17371133678981594754126607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23161511571975459672168809 17371133678981594754126607)
            ·
              refine ⟨26056700518472392131189911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17371133678981594754126607 26056700518472392131189911)
              ·
                refine ⟨39085050777708588196784867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26056700518472392131189911 39085050777708588196784867)
                ·
                  refine ⟨58627576166562882295177301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39085050777708588196784867 58627576166562882295177301)
                  ·
                    refine ⟨687041908201908776896609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58627576166562882295177301 687041908201908776896609)
                    ·
                      rfl

theorem cell23_4014028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_4014028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014028 prefixEnd_4014028 := by exact prefixLift 4014028
  have htrace : WordTrace (prefixWord ++ tailWord_4014028) baseStart_4014028 baseEnd_4014028 := by
    simpa [prefixWord, tailWord_4014028, baseEnd_4014028] using wordTrace_append hprefix tailTrace_4014028
  have hstable : (prefixWord ++ tailWord_4014028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014028).length < 2 ^ (prefixWord ++ tailWord_4014028).sum := by decide
  have hdescent : baseEnd_4014028 < baseStart_4014028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014052 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_4014052 : Nat := 118140960795 + 4014052 * 2 ^ 59
def prefixEnd_4014052 : Nat := 4983230072969 + 3 ^ 40 * 4014052 * 2
def baseEnd_4014052 : Nat := 2061138048141434236789717

theorem tailTrace_4014052 : CollatzResearch.WordTrace tailWord_4014052 prefixEnd_4014052 2061138048141434236789717 := by
  unfold tailWord_4014052
  simp only [CollatzResearch.WordTrace]
  refine ⟨73202252026891312173822205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97603002702521749565096273 73202252026891312173822205)
  ·
    refine ⟨27450844510084242065183327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73202252026891312173822205 27450844510084242065183327)
    ·
      refine ⟨41176266765126363097774991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27450844510084242065183327 41176266765126363097774991)
      ·
        refine ⟨61764400147689544646662487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41176266765126363097774991 61764400147689544646662487)
        ·
          refine ⟨92646600221534316969993731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61764400147689544646662487 92646600221534316969993731)
          ·
            refine ⟨138969900332301475454990597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92646600221534316969993731 138969900332301475454990597)
            ·
              refine ⟨26056856312306526647810737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138969900332301475454990597 26056856312306526647810737)
              ·
                refine ⟨19542642234229894985858053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26056856312306526647810737 19542642234229894985858053)
                ·
                  refine ⟨3664245418918105309848385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19542642234229894985858053 3664245418918105309848385)
                  ·
                    refine ⟨2748184064188578982386289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3664245418918105309848385 2748184064188578982386289)
                    ·
                      refine ⟨2061138048141434236789717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748184064188578982386289 2061138048141434236789717)
                      ·
                        rfl

theorem cell23_4014052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_4014052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014052 prefixEnd_4014052 := by exact prefixLift 4014052
  have htrace : WordTrace (prefixWord ++ tailWord_4014052) baseStart_4014052 baseEnd_4014052 := by
    simpa [prefixWord, tailWord_4014052, baseEnd_4014052] using wordTrace_append hprefix tailTrace_4014052
  have hstable : (prefixWord ++ tailWord_4014052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014052).length < 2 ^ (prefixWord ++ tailWord_4014052).sum := by decide
  have hdescent : baseEnd_4014052 < baseStart_4014052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014058 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 9]
def baseStart_4014058 : Nat := 118140960795 + 4014058 * 2 ^ 59
def prefixEnd_4014058 : Nat := 4983230072969 + 3 ^ 40 * 4014058 * 2
def baseEnd_4014058 : Nat := 229015681002817912590521

theorem tailTrace_4014058 : CollatzResearch.WordTrace tailWord_4014058 prefixEnd_4014058 229015681002817912590521 := by
  unfold tailWord_4014058
  simp only [CollatzResearch.WordTrace]
  refine ⟨36601180722940221843090707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97603148594507258248241885 36601180722940221843090707)
  ·
    refine ⟨54901771084410332764636061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36601180722940221843090707 54901771084410332764636061)
    ·
      refine ⟨20588164156653874786738523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54901771084410332764636061 20588164156653874786738523)
      ·
        refine ⟨30882246234980812180107785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20588164156653874786738523 30882246234980812180107785)
        ·
          refine ⟨23161684676235609135080839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30882246234980812180107785 23161684676235609135080839)
          ·
            refine ⟨34742527014353413702621259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23161684676235609135080839 34742527014353413702621259)
            ·
              refine ⟨52113790521530120553931889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34742527014353413702621259 52113790521530120553931889)
              ·
                refine ⟨39085342891147590415448917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52113790521530120553931889 39085342891147590415448917)
                ·
                  refine ⟨229015681002817912590521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39085342891147590415448917 229015681002817912590521)
                  ·
                    rfl

theorem cell23_4014058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_4014058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014058 prefixEnd_4014058 := by exact prefixLift 4014058
  have htrace : WordTrace (prefixWord ++ tailWord_4014058) baseStart_4014058 baseEnd_4014058 := by
    simpa [prefixWord, tailWord_4014058, baseEnd_4014058] using wordTrace_append hprefix tailTrace_4014058
  have hstable : (prefixWord ++ tailWord_4014058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014058).length < 2 ^ (prefixWord ++ tailWord_4014058).sum := by decide
  have hdescent : baseEnd_4014058 < baseStart_4014058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014075 : List Nat := [1, 1, 1, 1, 1, 3, 6, 4, 5]
def baseStart_4014075 : Nat := 118140960795 + 4014075 * 2 ^ 59
def prefixEnd_4014075 : Nat := 4983230072969 + 3 ^ 40 * 4014075 * 2
def baseEnd_4014075 : Nat := 229016650910720849644679

theorem tailTrace_4014075 : CollatzResearch.WordTrace tailWord_4014075 prefixEnd_4014075 229016650910720849644679 := by
  unfold tailWord_4014075
  simp only [CollatzResearch.WordTrace]
  refine ⟨146405342932699299275731679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97603561955132866183821119 146405342932699299275731679)
  ·
    refine ⟨219608014399048948913597519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146405342932699299275731679 219608014399048948913597519)
    ·
      refine ⟨329412021598573423370396279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219608014399048948913597519 329412021598573423370396279)
      ·
        refine ⟨494118032397860135055594419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329412021598573423370396279 494118032397860135055594419)
        ·
          refine ⟨741177048596790202583391629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494118032397860135055594419 741177048596790202583391629)
          ·
            refine ⟨277941393223796325968771861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741177048596790202583391629 277941393223796325968771861)
            ·
              refine ⟨13028502807365452779786181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277941393223796325968771861 13028502807365452779786181)
              ·
                refine ⟨2442844276381022396209909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13028502807365452779786181 2442844276381022396209909)
                ·
                  refine ⟨229016650910720849644679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2442844276381022396209909 229016650910720849644679)
                  ·
                    rfl

theorem cell23_4014075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 5].length) (baseStart_4014075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014075 prefixEnd_4014075 := by exact prefixLift 4014075
  have htrace : WordTrace (prefixWord ++ tailWord_4014075) baseStart_4014075 baseEnd_4014075 := by
    simpa [prefixWord, tailWord_4014075, baseEnd_4014075] using wordTrace_append hprefix tailTrace_4014075
  have hstable : (prefixWord ++ tailWord_4014075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014075).length < 2 ^ (prefixWord ++ tailWord_4014075).sum := by decide
  have hdescent : baseEnd_4014075 < baseStart_4014075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014085 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_4014085 : Nat := 118140960795 + 4014085 * 2 ^ 59
def prefixEnd_4014085 : Nat := 4983230072969 + 3 ^ 40 * 4014085 * 2
def baseEnd_4014085 : Nat := 2061154993003032607677065

theorem tailTrace_4014085 : CollatzResearch.WordTrace tailWord_4014085 prefixEnd_4014085 2061154993003032607677065 := by
  unfold tailWord_4014085
  simp only [CollatzResearch.WordTrace]
  refine ⟨146405707662663070983595709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97603805108442047322397139 146405707662663070983595709)
  ·
    refine ⟨54902140373498651618848391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146405707662663070983595709 54902140373498651618848391)
    ·
      refine ⟨82353210560247977428272587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54902140373498651618848391 82353210560247977428272587)
      ·
        refine ⟨123529815840371966142408881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82353210560247977428272587 123529815840371966142408881)
        ·
          refine ⟨92647361880278974606806661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123529815840371966142408881 92647361880278974606806661)
          ·
            refine ⟨17371380352552307738776249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92647361880278974606806661 17371380352552307738776249)
            ·
              refine ⟨13028535264414230804082187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17371380352552307738776249 13028535264414230804082187)
              ·
                refine ⟨19542802896621346206123281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13028535264414230804082187 19542802896621346206123281)
                ·
                  refine ⟨14657102172466009654592461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19542802896621346206123281 14657102172466009654592461)
                  ·
                    refine ⟨5496413314674753620472173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14657102172466009654592461 5496413314674753620472173)
                    ·
                      refine ⟨2061154993003032607677065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5496413314674753620472173 2061154993003032607677065)
                      ·
                        rfl

theorem cell23_4014085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_4014085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014085 prefixEnd_4014085 := by exact prefixLift 4014085
  have htrace : WordTrace (prefixWord ++ tailWord_4014085) baseStart_4014085 baseEnd_4014085 := by
    simpa [prefixWord, tailWord_4014085, baseEnd_4014085] using wordTrace_append hprefix tailTrace_4014085
  have hstable : (prefixWord ++ tailWord_4014085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014085).length < 2 ^ (prefixWord ++ tailWord_4014085).sum := by decide
  have hdescent : baseEnd_4014085 < baseStart_4014085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014088 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 3, 7]
def baseStart_4014088 : Nat := 118140960795 + 4014088 * 2 ^ 59
def prefixEnd_4014088 : Nat := 4983230072969 + 3 ^ 40 * 4014088 * 2
def baseEnd_4014088 : Nat := 687052177814998698646517

theorem tailTrace_4014088 : CollatzResearch.WordTrace tailWord_4014088 prefixEnd_4014088 687052177814998698646517 := by
  unfold tailWord_4014088
  simp only [CollatzResearch.WordTrace]
  refine ⟨73202908540826101247977459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97603878054434801663969945 73202908540826101247977459)
  ·
    refine ⟨109804362811239151871966189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73202908540826101247977459 109804362811239151871966189)
    ·
      refine ⟨41176636054214681951987321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109804362811239151871966189 41176636054214681951987321)
      ·
        refine ⟨30882477040661011463990491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41176636054214681951987321 30882477040661011463990491)
        ·
          refine ⟨46323715560991517195985737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30882477040661011463990491 46323715560991517195985737)
          ·
            refine ⟨34742786670743637896989303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46323715560991517195985737 34742786670743637896989303)
            ·
              refine ⟨52114180006115456845483955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34742786670743637896989303 52114180006115456845483955)
              ·
                refine ⟨78171270009173185268225933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52114180006115456845483955 78171270009173185268225933)
                ·
                  refine ⟨29314226253439944475584725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78171270009173185268225933 29314226253439944475584725)
                  ·
                    refine ⟨687052177814998698646517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29314226253439944475584725 687052177814998698646517)
                    ·
                      rfl

theorem cell23_4014088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_4014088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014088 prefixEnd_4014088 := by exact prefixLift 4014088
  have htrace : WordTrace (prefixWord ++ tailWord_4014088) baseStart_4014088 baseEnd_4014088 := by
    simpa [prefixWord, tailWord_4014088, baseEnd_4014088] using wordTrace_append hprefix tailTrace_4014088
  have hstable : (prefixWord ++ tailWord_4014088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014088).length < 2 ^ (prefixWord ++ tailWord_4014088).sum := by decide
  have hdescent : baseEnd_4014088 < baseStart_4014088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014109 : List Nat := [1, 4, 2, 2, 2, 3, 1, 3, 5]
def baseStart_4014109 : Nat := 118140960795 + 4014109 * 2 ^ 59
def prefixEnd_4014109 : Nat := 4983230072969 + 3 ^ 40 * 4014109 * 2
def baseEnd_4014109 : Nat := 229018590726526723752995

theorem tailTrace_4014109 : CollatzResearch.WordTrace tailWord_4014109 prefixEnd_4014109 229018590726526723752995 := by
  unfold tailWord_4014109
  simp only [CollatzResearch.WordTrace]
  refine ⟨146406583014576123082469381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97604388676384082054979587 146406583014576123082469381)
  ·
    refine ⟨27451234315233023077963009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146406583014576123082469381 27451234315233023077963009)
    ·
      refine ⟨20588425736424767308472257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27451234315233023077963009 20588425736424767308472257)
      ·
        refine ⟨15441319302318575481354193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20588425736424767308472257 15441319302318575481354193)
        ·
          refine ⟨11580989476738931611015645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15441319302318575481354193 11580989476738931611015645)
          ·
            refine ⟨4342871053777099354130867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11580989476738931611015645 4342871053777099354130867)
            ·
              refine ⟨6514306580665649031196301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342871053777099354130867 6514306580665649031196301)
              ·
                refine ⟨2442864967749618386698613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6514306580665649031196301 2442864967749618386698613)
                ·
                  refine ⟨229018590726526723752995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2442864967749618386698613 229018590726526723752995)
                  ·
                    rfl

theorem cell23_4014109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_4014109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014109 prefixEnd_4014109 := by exact prefixLift 4014109
  have htrace : WordTrace (prefixWord ++ tailWord_4014109) baseStart_4014109 baseEnd_4014109 := by
    simpa [prefixWord, tailWord_4014109, baseEnd_4014109] using wordTrace_append hprefix tailTrace_4014109
  have hstable : (prefixWord ++ tailWord_4014109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014109).length < 2 ^ (prefixWord ++ tailWord_4014109).sum := by decide
  have hdescent : baseEnd_4014109 < baseStart_4014109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014122 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4014122 : Nat := 118140960795 + 4014122 * 2 ^ 59
def prefixEnd_4014122 : Nat := 4983230072969 + 3 ^ 40 * 4014122 * 2
def baseEnd_4014122 : Nat := 687057997262416320971465

theorem tailTrace_4014122 : CollatzResearch.WordTrace tailWord_4014122 prefixEnd_4014122 687057997262416320971465 := by
  unfold tailWord_4014122
  simp only [CollatzResearch.WordTrace]
  refine ⟨36601764290882256575673155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97604704775686017535128413 36601764290882256575673155)
  ·
    refine ⟨54902646436323384863509733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36601764290882256575673155 54902646436323384863509733)
    ·
      refine ⟨10294246206810634661908075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54902646436323384863509733 10294246206810634661908075)
      ·
        refine ⟨15441369310215951992862113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10294246206810634661908075 15441369310215951992862113)
        ·
          refine ⟨11581026982661963994646585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15441369310215951992862113 11581026982661963994646585)
          ·
            refine ⟨8685770236996472995984939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11581026982661963994646585 8685770236996472995984939)
            ·
              refine ⟨13028655355494709493977409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8685770236996472995984939 13028655355494709493977409)
              ·
                refine ⟨9771491516621032120483057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13028655355494709493977409 9771491516621032120483057)
                ·
                  refine ⟨7328618637465774090362293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9771491516621032120483057 7328618637465774090362293)
                  ·
                    refine ⟨687057997262416320971465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7328618637465774090362293 687057997262416320971465)
                    ·
                      rfl

theorem cell23_4014122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4014122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014122 prefixEnd_4014122 := by exact prefixLift 4014122
  have htrace : WordTrace (prefixWord ++ tailWord_4014122) baseStart_4014122 baseEnd_4014122 := by
    simpa [prefixWord, tailWord_4014122, baseEnd_4014122] using wordTrace_append hprefix tailTrace_4014122
  have hstable : (prefixWord ++ tailWord_4014122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014122).length < 2 ^ (prefixWord ++ tailWord_4014122).sum := by decide
  have hdescent : baseEnd_4014122 < baseStart_4014122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014186 : List Nat := [3, 1, 3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_4014186 : Nat := 118140960795 + 4014186 * 2 ^ 59
def prefixEnd_4014186 : Nat := 4983230072969 + 3 ^ 40 * 4014186 * 2
def baseEnd_4014186 : Nat := 687068951516378904171367

theorem tailTrace_4014186 : CollatzResearch.WordTrace tailWord_4014186 prefixEnd_4014186 687068951516378904171367 := by
  unfold tailWord_4014186
  simp only [CollatzResearch.WordTrace]
  refine ⟨36602347858824291308255603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97606260956864776822014941 36602347858824291308255603)
  ·
    refine ⟨54903521788236436962383405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36602347858824291308255603 54903521788236436962383405)
    ·
      refine ⟨20588820670588663860893777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54903521788236436962383405 20588820670588663860893777)
      ·
        refine ⟨15441615502941497895670333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20588820670588663860893777 15441615502941497895670333)
        ·
          refine ⟨5790605813603061710876375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15441615502941497895670333 5790605813603061710876375)
          ·
            refine ⟨8685908720404592566314563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790605813603061710876375 8685908720404592566314563)
            ·
              refine ⟨13028863080606888849471845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8685908720404592566314563 13028863080606888849471845)
              ·
                refine ⟨2442911827613791659275971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13028863080606888849471845 2442911827613791659275971)
                ·
                  refine ⟨3664367741420687488913957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442911827613791659275971 3664367741420687488913957)
                  ·
                    refine ⟨687068951516378904171367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3664367741420687488913957 687068951516378904171367)
                    ·
                      rfl

theorem cell23_4014186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_4014186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014186 prefixEnd_4014186 := by exact prefixLift 4014186
  have htrace : WordTrace (prefixWord ++ tailWord_4014186) baseStart_4014186 baseEnd_4014186 := by
    simpa [prefixWord, tailWord_4014186, baseEnd_4014186] using wordTrace_append hprefix tailTrace_4014186
  have hstable : (prefixWord ++ tailWord_4014186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014186).length < 2 ^ (prefixWord ++ tailWord_4014186).sum := by decide
  have hdescent : baseEnd_4014186 < baseStart_4014186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014212 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_4014212 : Nat := 118140960795 + 4014212 * 2 ^ 59
def prefixEnd_4014212 : Nat := 4983230072969 + 3 ^ 40 * 4014212 * 2
def baseEnd_4014212 : Nat := 687073401682051203596327

theorem tailTrace_4014212 : CollatzResearch.WordTrace tailWord_4014212 prefixEnd_4014212 687073401682051203596327 := by
  unfold tailWord_4014212
  simp only [CollatzResearch.WordTrace]
  refine ⟨73205169866601485836734445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97606893155468647782312593 73205169866601485836734445)
  ·
    refine ⟨27451938699975557188775417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73205169866601485836734445 27451938699975557188775417)
    ·
      refine ⟨20588954024981667891581563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27451938699975557188775417 20588954024981667891581563)
      ·
        refine ⟨30883431037472501837372345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20588954024981667891581563 30883431037472501837372345)
        ·
          refine ⟨23162573278104376378029259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30883431037472501837372345 23162573278104376378029259)
          ·
            refine ⟨34743859917156564567043889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23162573278104376378029259 34743859917156564567043889)
            ·
              refine ⟨26057894937867423425282917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34743859917156564567043889 26057894937867423425282917)
              ·
                refine ⟨4885855300850141892240547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26057894937867423425282917 4885855300850141892240547)
                ·
                  refine ⟨7328782951275212838360821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4885855300850141892240547 7328782951275212838360821)
                  ·
                    refine ⟨687073401682051203596327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7328782951275212838360821 687073401682051203596327)
                    ·
                      rfl

theorem cell23_4014212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_4014212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014212 prefixEnd_4014212 := by exact prefixLift 4014212
  have htrace : WordTrace (prefixWord ++ tailWord_4014212) baseStart_4014212 baseEnd_4014212 := by
    simpa [prefixWord, tailWord_4014212, baseEnd_4014212] using wordTrace_append hprefix tailTrace_4014212
  have hstable : (prefixWord ++ tailWord_4014212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014212).length < 2 ^ (prefixWord ++ tailWord_4014212).sum := by decide
  have hdescent : baseEnd_4014212 < baseStart_4014212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014245 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_4014245 : Nat := 118140960795 + 4014245 * 2 ^ 59
def prefixEnd_4014245 : Nat := 4983230072969 + 3 ^ 40 * 4014245 * 2
def baseEnd_4014245 : Nat := 2061237149907751981676329

theorem tailTrace_4014245 : CollatzResearch.WordTrace tailWord_4014245 prefixEnd_4014245 2061237149907751981676329 := by
  unfold tailWord_4014245
  simp only [CollatzResearch.WordTrace]
  refine ⟨146411543342083418309420189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97607695561388945539613459 146411543342083418309420189)
  ·
    refine ⟨54904328753281281866032571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146411543342083418309420189 54904328753281281866032571)
    ·
      refine ⟨82356493129921922799048857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54904328753281281866032571 82356493129921922799048857)
      ·
        refine ⟨61767369847441442099286643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82356493129921922799048857 61767369847441442099286643)
        ·
          refine ⟨92651054771162163148929965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61767369847441442099286643 92651054771162163148929965)
          ·
            refine ⟨34744145539185811180848737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92651054771162163148929965 34744145539185811180848737)
            ·
              refine ⟨26058109154389358385636553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34744145539185811180848737 26058109154389358385636553)
              ·
                refine ⟨19543581865792018789227415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26058109154389358385636553 19543581865792018789227415)
                ·
                  refine ⟨29315372798688028183841123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19543581865792018789227415 29315372798688028183841123)
                  ·
                    refine ⟨43973059198032042275761685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29315372798688028183841123 43973059198032042275761685)
                    ·
                      refine ⟨2061237149907751981676329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43973059198032042275761685 2061237149907751981676329)
                      ·
                        rfl

theorem cell23_4014245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_4014245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014245 prefixEnd_4014245 := by exact prefixLift 4014245
  have htrace : WordTrace (prefixWord ++ tailWord_4014245) baseStart_4014245 baseEnd_4014245 := by
    simpa [prefixWord, tailWord_4014245, baseEnd_4014245] using wordTrace_append hprefix tailTrace_4014245
  have hstable : (prefixWord ++ tailWord_4014245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014245).length < 2 ^ (prefixWord ++ tailWord_4014245).sum := by decide
  have hdescent : baseEnd_4014245 < baseStart_4014245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014272 : List Nat := [2, 1, 1, 2, 5, 1, 4, 7]
def baseStart_4014272 : Nat := 118140960795 + 4014272 * 2 ^ 59
def prefixEnd_4014272 : Nat := 4983230072969 + 3 ^ 40 * 4014272 * 2
def baseEnd_4014272 : Nat := 76342630143904569482915

theorem tailTrace_4014272 : CollatzResearch.WordTrace tailWord_4014272 prefixEnd_4014272 76342630143904569482915 := by
  unfold tailWord_4014272
  simp only [CollatzResearch.WordTrace]
  refine ⟨73206264056492800960326535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97608352075323734613768713 73206264056492800960326535)
  ·
    refine ⟨109809396084739201440489803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73206264056492800960326535 109809396084739201440489803)
    ·
      refine ⟨164714094127108802160734705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109809396084739201440489803 164714094127108802160734705)
      ·
        refine ⟨123535570595331601620551029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164714094127108802160734705 123535570595331601620551029)
        ·
          refine ⟨11581459743312337651926659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123535570595331601620551029 11581459743312337651926659)
          ·
            refine ⟨17372189614968506477889989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11581459743312337651926659 17372189614968506477889989)
            ·
              refine ⟨3257285552806594964604373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17372189614968506477889989 3257285552806594964604373)
              ·
                refine ⟨76342630143904569482915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3257285552806594964604373 76342630143904569482915)
                ·
                  rfl

theorem cell23_4014272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 7].length) (baseStart_4014272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014272 prefixEnd_4014272 := by exact prefixLift 4014272
  have htrace : WordTrace (prefixWord ++ tailWord_4014272) baseStart_4014272 baseEnd_4014272 := by
    simpa [prefixWord, tailWord_4014272, baseEnd_4014272] using wordTrace_append hprefix tailTrace_4014272
  have hstable : (prefixWord ++ tailWord_4014272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014272).length < 2 ^ (prefixWord ++ tailWord_4014272).sum := by decide
  have hdescent : baseEnd_4014272 < baseStart_4014272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014282 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_4014282 : Nat := 118140960795 + 4014282 * 2 ^ 59
def prefixEnd_4014282 : Nat := 4983230072969 + 3 ^ 40 * 4014282 * 2
def baseEnd_4014282 : Nat := 2061256148691968336913659

theorem tailTrace_4014282 : CollatzResearch.WordTrace tailWord_4014282 prefixEnd_4014282 2061256148691968336913659 := by
  unfold tailWord_4014282
  simp only [CollatzResearch.WordTrace]
  refine ⟨36603223210737343407129275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97608595228632915752344733 36603223210737343407129275)
  ·
    refine ⟨54904834816106015110693913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36603223210737343407129275 54904834816106015110693913)
    ·
      refine ⟨41178626112079511333020435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54904834816106015110693913 41178626112079511333020435)
      ·
        refine ⟨61767939168119266999530653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41178626112079511333020435 61767939168119266999530653)
        ·
          refine ⟨23162977188044725124823995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61767939168119266999530653 23162977188044725124823995)
          ·
            refine ⟨34744465782067087687235993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23162977188044725124823995 34744465782067087687235993)
            ·
              refine ⟨26058349336550315765426995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34744465782067087687235993 26058349336550315765426995)
              ·
                refine ⟨39087524004825473648140493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26058349336550315765426995 39087524004825473648140493)
                ·
                  refine ⟨14657821501809552618052685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39087524004825473648140493 14657821501809552618052685)
                  ·
                    refine ⟨5496683063178582231769757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14657821501809552618052685 5496683063178582231769757)
                    ·
                      refine ⟨2061256148691968336913659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5496683063178582231769757 2061256148691968336913659)
                      ·
                        rfl

theorem cell23_4014282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_4014282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014282 prefixEnd_4014282 := by exact prefixLift 4014282
  have htrace : WordTrace (prefixWord ++ tailWord_4014282) baseStart_4014282 baseEnd_4014282 := by
    simpa [prefixWord, tailWord_4014282, baseEnd_4014282] using wordTrace_append hprefix tailTrace_4014282
  have hstable : (prefixWord ++ tailWord_4014282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014282).length < 2 ^ (prefixWord ++ tailWord_4014282).sum := by decide
  have hdescent : baseEnd_4014282 < baseStart_4014282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014295 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_4014295 : Nat := 118140960795 + 4014295 * 2 ^ 59
def prefixEnd_4014295 : Nat := 4983230072969 + 3 ^ 40 * 4014295 * 2
def baseEnd_4014295 : Nat := 2061262823940476786051099

theorem tailTrace_4014295 : CollatzResearch.WordTrace tailWord_4014295 prefixEnd_4014295 2061262823940476786051099 := by
  unfold tailWord_4014295
  simp only [CollatzResearch.WordTrace]
  refine ⟨146413366991902276848740339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97608911327934851232493559 146413366991902276848740339)
  ·
    refine ⟨219620050487853415273110509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146413366991902276848740339 219620050487853415273110509)
    ·
      refine ⟨82357518932945030727416441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219620050487853415273110509 82357518932945030727416441)
      ·
        refine ⟨61768139199708773045562331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82357518932945030727416441 61768139199708773045562331)
        ·
          refine ⟨92652208799563159568343497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61768139199708773045562331 92652208799563159568343497)
          ·
            refine ⟨69489156599672369676257623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92652208799563159568343497 69489156599672369676257623)
            ·
              refine ⟨104233734899508554514386435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69489156599672369676257623 104233734899508554514386435)
              ·
                refine ⟨156350602349262831771579653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104233734899508554514386435 156350602349262831771579653)
                ·
                  refine ⟨29315737940486780957171185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156350602349262831771579653 29315737940486780957171185)
                  ·
                    refine ⟨21986803455365085717878389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29315737940486780957171185 21986803455365085717878389)
                    ·
                      refine ⟨2061262823940476786051099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21986803455365085717878389 2061262823940476786051099)
                      ·
                        rfl

theorem cell23_4014295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_4014295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014295 prefixEnd_4014295 := by exact prefixLift 4014295
  have htrace : WordTrace (prefixWord ++ tailWord_4014295) baseStart_4014295 baseEnd_4014295 := by
    simpa [prefixWord, tailWord_4014295, baseEnd_4014295] using wordTrace_append hprefix tailTrace_4014295
  have hstable : (prefixWord ++ tailWord_4014295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014295).length < 2 ^ (prefixWord ++ tailWord_4014295).sum := by decide
  have hdescent : baseEnd_4014295 < baseStart_4014295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014315 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 1, 8]
def baseStart_4014315 : Nat := 118140960795 + 4014315 * 2 ^ 59
def prefixEnd_4014315 : Nat := 4983230072969 + 3 ^ 40 * 4014315 * 2
def baseEnd_4014315 : Nat := 687091031184522235933669

theorem tailTrace_4014315 : CollatzResearch.WordTrace tailWord_4014315 prefixEnd_4014315 687091031184522235933669 := by
  unfold tailWord_4014315
  simp only [CollatzResearch.WordTrace]
  refine ⟨146414096451829820264468399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97609397634553213509645599 146414096451829820264468399)
  ·
    refine ⟨219621144677744730396702599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146414096451829820264468399 219621144677744730396702599)
    ·
      refine ⟨329431717016617095595053899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219621144677744730396702599 329431717016617095595053899)
      ·
        refine ⟨494147575524925643392580849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329431717016617095595053899 494147575524925643392580849)
        ·
          refine ⟨370610681643694232544435637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494147575524925643392580849 370610681643694232544435637)
          ·
            refine ⟨34744751404096334301040841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370610681643694232544435637 34744751404096334301040841)
            ·
              refine ⟨26058563553072250725780631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34744751404096334301040841 26058563553072250725780631)
              ·
                refine ⟨39087845329608376088670947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26058563553072250725780631 39087845329608376088670947)
                ·
                  refine ⟨58631767994412564133006421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39087845329608376088670947 58631767994412564133006421)
                  ·
                    refine ⟨687091031184522235933669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58631767994412564133006421 687091031184522235933669)
                    ·
                      rfl

theorem cell23_4014315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 8].length) (baseStart_4014315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014315 prefixEnd_4014315 := by exact prefixLift 4014315
  have htrace : WordTrace (prefixWord ++ tailWord_4014315) baseStart_4014315 baseEnd_4014315 := by
    simpa [prefixWord, tailWord_4014315, baseEnd_4014315] using wordTrace_append hprefix tailTrace_4014315
  have hstable : (prefixWord ++ tailWord_4014315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014315).length < 2 ^ (prefixWord ++ tailWord_4014315).sum := by decide
  have hdescent : baseEnd_4014315 < baseStart_4014315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014339 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 1, 4, 2]
def baseStart_4014339 : Nat := 118140960795 + 4014339 * 2 ^ 59
def prefixEnd_4014339 : Nat := 4983230072969 + 3 ^ 40 * 4014339 * 2
def baseEnd_4014339 : Nat := 2061285417089274613900897

theorem tailTrace_4014339 : CollatzResearch.WordTrace tailWord_4014339 prefixEnd_4014339 2061285417089274613900897 := by
  unfold tailWord_4014339
  simp only [CollatzResearch.WordTrace]
  refine ⟨146414971803742872363342071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97609981202495248242228047 146414971803742872363342071)
  ·
    refine ⟨219622457705614308545013107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146414971803742872363342071 219622457705614308545013107)
    ·
      refine ⟨329433686558421462817519661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219622457705614308545013107 329433686558421462817519661)
      ·
        refine ⟨123537632459408048556569873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329433686558421462817519661 123537632459408048556569873)
        ·
          refine ⟨92653224344556036417427405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123537632459408048556569873 92653224344556036417427405)
          ·
            refine ⟨34744959129208513656535277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92653224344556036417427405 34744959129208513656535277)
            ·
              refine ⟨13029359673453192621200729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34744959129208513656535277 13029359673453192621200729)
              ·
                refine ⟨9772019755089894465900547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13029359673453192621200729 9772019755089894465900547)
                ·
                  refine ⟨14658029632634841698850821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9772019755089894465900547 14658029632634841698850821)
                  ·
                    refine ⟨2748380556119032818534529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14658029632634841698850821 2748380556119032818534529)
                    ·
                      refine ⟨2061285417089274613900897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748380556119032818534529 2061285417089274613900897)
                      ·
                        rfl

theorem cell23_4014339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_4014339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014339 prefixEnd_4014339 := by exact prefixLift 4014339
  have htrace : WordTrace (prefixWord ++ tailWord_4014339) baseStart_4014339 baseEnd_4014339 := by
    simpa [prefixWord, tailWord_4014339, baseEnd_4014339] using wordTrace_append hprefix tailTrace_4014339
  have hstable : (prefixWord ++ tailWord_4014339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014339).length < 2 ^ (prefixWord ++ tailWord_4014339).sum := by decide
  have hdescent : baseEnd_4014339 < baseStart_4014339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014355 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 7]
def baseStart_4014355 : Nat := 118140960795 + 4014355 * 2 ^ 59
def prefixEnd_4014355 : Nat := 4983230072969 + 3 ^ 40 * 4014355 * 2
def baseEnd_4014355 : Nat := 2061293632779746551300823

theorem tailTrace_4014355 : CollatzResearch.WordTrace tailWord_4014355 prefixEnd_4014355 2061293632779746551300823 := by
  unfold tailWord_4014355
  simp only [CollatzResearch.WordTrace]
  refine ⟨146415555371684907095924519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97610370247789938063949679 146415555371684907095924519)
  ·
    refine ⟨219623333057527360643886779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146415555371684907095924519 219623333057527360643886779)
    ·
      refine ⟨329434999586291040965830169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219623333057527360643886779 329434999586291040965830169)
      ·
        refine ⟨247076249689718280724372627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329434999586291040965830169 247076249689718280724372627)
        ·
          refine ⟨370614374534577421086558941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247076249689718280724372627 370614374534577421086558941)
          ·
            refine ⟨138980390450466532907459603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370614374534577421086558941 138980390450466532907459603)
            ·
              refine ⟨208470585675699799361189405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138980390450466532907459603 208470585675699799361189405)
              ·
                refine ⟨78176469628387424760446027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208470585675699799361189405 78176469628387424760446027)
                ·
                  refine ⟨117264704442581137140669041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78176469628387424760446027 117264704442581137140669041)
                  ·
                    refine ⟨87948528331935852855501781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117264704442581137140669041 87948528331935852855501781)
                    ·
                      refine ⟨2061293632779746551300823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87948528331935852855501781 2061293632779746551300823)
                      ·
                        rfl

theorem cell23_4014355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_4014355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014355 prefixEnd_4014355 := by exact prefixLift 4014355
  have htrace : WordTrace (prefixWord ++ tailWord_4014355) baseStart_4014355 baseEnd_4014355 := by
    simpa [prefixWord, tailWord_4014355, baseEnd_4014355] using wordTrace_append hprefix tailTrace_4014355
  have hstable : (prefixWord ++ tailWord_4014355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014355).length < 2 ^ (prefixWord ++ tailWord_4014355).sum := by decide
  have hdescent : baseEnd_4014355 < baseStart_4014355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014366 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4014366 : Nat := 118140960795 + 4014366 * 2 ^ 59
def prefixEnd_4014366 : Nat := 4983230072969 + 3 ^ 40 * 4014366 * 2
def baseEnd_4014366 : Nat := 687099760355648669421091

theorem tailTrace_4014366 : CollatzResearch.WordTrace tailWord_4014366 prefixEnd_4014366 687099760355648669421091 := by
  unfold tailWord_4014366
  simp only [CollatzResearch.WordTrace]
  refine ⟨18301994571830631996821869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97610637716430037316383301 18301994571830631996821869)
  ·
    refine ⟨6863247964436486998808201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18301994571830631996821869 6863247964436486998808201)
    ·
      refine ⟨5147435973327365249106151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6863247964436486998808201 5147435973327365249106151)
      ·
        refine ⟨7721153959991047873659227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147435973327365249106151 7721153959991047873659227)
        ·
          refine ⟨11581730939986571810488841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7721153959991047873659227 11581730939986571810488841)
          ·
            refine ⟨8686298204989928857866631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11581730939986571810488841 8686298204989928857866631)
            ·
              refine ⟨13029447307484893286799947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8686298204989928857866631 13029447307484893286799947)
              ·
                refine ⟨19544170961227339930199921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13029447307484893286799947 19544170961227339930199921)
                ·
                  refine ⟨14658128220920504947649941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19544170961227339930199921 14658128220920504947649941)
                  ·
                    refine ⟨687099760355648669421091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14658128220920504947649941 687099760355648669421091)
                    ·
                      rfl

theorem cell23_4014366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4014366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014366 prefixEnd_4014366 := by exact prefixLift 4014366
  have htrace : WordTrace (prefixWord ++ tailWord_4014366) baseStart_4014366 baseEnd_4014366 := by
    simpa [prefixWord, tailWord_4014366, baseEnd_4014366] using wordTrace_append hprefix tailTrace_4014366
  have hstable : (prefixWord ++ tailWord_4014366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014366).length < 2 ^ (prefixWord ++ tailWord_4014366).sum := by decide
  have hdescent : baseEnd_4014366 < baseStart_4014366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014449 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_4014449 : Nat := 118140960795 + 4014449 * 2 ^ 59
def prefixEnd_4014449 : Nat := 4983230072969 + 3 ^ 40 * 4014449 * 2
def baseEnd_4014449 : Nat := 2061341899961269183525391

theorem tailTrace_4014449 : CollatzResearch.WordTrace tailWord_4014449 prefixEnd_4014449 2061341899961269183525391 := by
  unfold tailWord_4014449
  simp only [CollatzResearch.WordTrace]
  refine ⟨146418983833344361149846401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97612655888896240766564267 146418983833344361149846401)
  ·
    refine ⟨109814237875008270862384801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146418983833344361149846401 109814237875008270862384801)
    ·
      refine ⟨82360678406256203146788601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109814237875008270862384801 82360678406256203146788601)
      ·
        refine ⟨61770508804692152360091451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82360678406256203146788601 61770508804692152360091451)
        ·
          refine ⟨92655763207038228540137177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61770508804692152360091451 92655763207038228540137177)
          ·
            refine ⟨69491822405278671405102883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92655763207038228540137177 69491822405278671405102883)
            ·
              refine ⟨104237733607918007107654325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69491822405278671405102883 104237733607918007107654325)
              ·
                refine ⟨9772287525742313166342593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104237733607918007107654325 9772287525742313166342593)
                ·
                  refine ⟨7329215644306734874756945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9772287525742313166342593 7329215644306734874756945)
                  ·
                    refine ⟨5496911733230051156067709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7329215644306734874756945 5496911733230051156067709)
                    ·
                      refine ⟨2061341899961269183525391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5496911733230051156067709 2061341899961269183525391)
                      ·
                        rfl

theorem cell23_4014449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_4014449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014449 prefixEnd_4014449 := by exact prefixLift 4014449
  have htrace : WordTrace (prefixWord ++ tailWord_4014449) baseStart_4014449 baseEnd_4014449 := by
    simpa [prefixWord, tailWord_4014449, baseEnd_4014449] using wordTrace_append hprefix tailTrace_4014449
  have hstable : (prefixWord ++ tailWord_4014449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014449).length < 2 ^ (prefixWord ++ tailWord_4014449).sum := by decide
  have hdescent : baseEnd_4014449 < baseStart_4014449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014499 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 3, 5]
def baseStart_4014499 : Nat := 118140960795 + 4014499 * 2 ^ 59
def prefixEnd_4014499 : Nat := 4983230072969 + 3 ^ 40 * 4014499 * 2
def baseEnd_4014499 : Nat := 687122524664664662633387

theorem tailTrace_4014499 : CollatzResearch.WordTrace tailWord_4014499 prefixEnd_4014499 687122524664664662633387 := by
  unfold tailWord_4014499
  simp only [CollatzResearch.WordTrace]
  refine ⟨146420807483163219689166551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97613871655442146459444367 146420807483163219689166551)
  ·
    refine ⟨219631211224744829533749827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146420807483163219689166551 219631211224744829533749827)
    ·
      refine ⟨329446816837117244300624741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219631211224744829533749827 329446816837117244300624741)
      ·
        refine ⟨61771278156959483306367139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329446816837117244300624741 61771278156959483306367139)
        ·
          refine ⟨92656917235439224959550709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61771278156959483306367139 92656917235439224959550709)
          ·
            refine ⟨8686585990822427339957879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92656917235439224959550709 8686585990822427339957879)
            ·
              refine ⟨13029878986233641009936819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8686585990822427339957879 13029878986233641009936819)
              ·
                refine ⟨19544818479350461514905229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13029878986233641009936819 19544818479350461514905229)
                ·
                  refine ⟨7329306929756423068089461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19544818479350461514905229 7329306929756423068089461)
                  ·
                    refine ⟨687122524664664662633387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7329306929756423068089461 687122524664664662633387)
                    ·
                      rfl

theorem cell23_4014499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 5].length) (baseStart_4014499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014499 prefixEnd_4014499 := by exact prefixLift 4014499
  have htrace : WordTrace (prefixWord ++ tailWord_4014499) baseStart_4014499 baseEnd_4014499 := by
    simpa [prefixWord, tailWord_4014499, baseEnd_4014499] using wordTrace_append hprefix tailTrace_4014499
  have hstable : (prefixWord ++ tailWord_4014499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014499).length < 2 ^ (prefixWord ++ tailWord_4014499).sum := by decide
  have hdescent : baseEnd_4014499 < baseStart_4014499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014553 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 3, 2, 2]
def baseStart_4014553 : Nat := 118140960795 + 4014553 * 2 ^ 59
def prefixEnd_4014553 : Nat := 4983230072969 + 3 ^ 40 * 4014553 * 2
def baseEnd_4014553 : Nat := 2061395301949336776624913

theorem tailTrace_4014553 : CollatzResearch.WordTrace tailWord_4014553 prefixEnd_4014553 2061395301949336776624913 := by
  unfold tailWord_4014553
  simp only [CollatzResearch.WordTrace]
  refine ⟨146422777024967586911632313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97615184683311724607754875 146422777024967586911632313)
  ·
    refine ⟨109817082768725690183724235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146422777024967586911632313 109817082768725690183724235)
    ·
      refine ⟨164725624153088535275586353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109817082768725690183724235 164725624153088535275586353)
      ·
        refine ⟨123544218114816401456689765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164725624153088535275586353 123544218114816401456689765)
        ·
          refine ⟨23164540896528075273129331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123544218114816401456689765 23164540896528075273129331)
          ·
            refine ⟨34746811344792112909693997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23164540896528075273129331 34746811344792112909693997)
            ·
              refine ⟨13030054254297042341135249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34746811344792112909693997 13030054254297042341135249)
              ·
                refine ⟨9772540690722781755851437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13030054254297042341135249 9772540690722781755851437)
                ·
                  refine ⟨3664702759021043158444289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9772540690722781755851437 3664702759021043158444289)
                  ·
                    refine ⟨2748527069265782368833217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3664702759021043158444289 2748527069265782368833217)
                    ·
                      refine ⟨2061395301949336776624913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748527069265782368833217 2061395301949336776624913)
                      ·
                        rfl

theorem cell23_4014553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_4014553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014553 prefixEnd_4014553 := by exact prefixLift 4014553
  have htrace : WordTrace (prefixWord ++ tailWord_4014553) baseStart_4014553 baseEnd_4014553 := by
    simpa [prefixWord, tailWord_4014553, baseEnd_4014553] using wordTrace_append hprefix tailTrace_4014553
  have hstable : (prefixWord ++ tailWord_4014553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014553).length < 2 ^ (prefixWord ++ tailWord_4014553).sum := by decide
  have hdescent : baseEnd_4014553 < baseStart_4014553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014569 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 3]
def baseStart_4014569 : Nat := 118140960795 + 4014569 * 2 ^ 59
def prefixEnd_4014569 : Nat := 4983230072969 + 3 ^ 40 * 4014569 * 2
def baseEnd_4014569 : Nat := 2061403517639808714024839

theorem tailTrace_4014569 : CollatzResearch.WordTrace tailWord_4014569 prefixEnd_4014569 2061403517639808714024839 := by
  unfold tailWord_4014569
  simp only [CollatzResearch.WordTrace]
  refine ⟨146423360592909621644214761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97615573728606414429476507 146423360592909621644214761)
  ·
    refine ⟨109817520444682216233161071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146423360592909621644214761 109817520444682216233161071)
    ·
      refine ⟨164726280667023324349741607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109817520444682216233161071 164726280667023324349741607)
      ·
        refine ⟨247089421000534986524612411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164726280667023324349741607 247089421000534986524612411)
        ·
          refine ⟨370634131500802479786918617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247089421000534986524612411 370634131500802479786918617)
          ·
            refine ⟨277975598625601859840188963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370634131500802479786918617 277975598625601859840188963)
            ·
              refine ⟨416963397938402789760283445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277975598625601859840188963 416963397938402789760283445)
              ·
                refine ⟨39090318556725261540026573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 416963397938402789760283445 39090318556725261540026573)
                ·
                  refine ⟨14658869458771973077509965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39090318556725261540026573 14658869458771973077509965)
                  ·
                    refine ⟨5497076047039489904066237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14658869458771973077509965 5497076047039489904066237)
                    ·
                      refine ⟨2061403517639808714024839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497076047039489904066237 2061403517639808714024839)
                      ·
                        rfl

theorem cell23_4014569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_4014569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014569 prefixEnd_4014569 := by exact prefixLift 4014569
  have htrace : WordTrace (prefixWord ++ tailWord_4014569) baseStart_4014569 baseEnd_4014569 := by
    simpa [prefixWord, tailWord_4014569, baseEnd_4014569] using wordTrace_append hprefix tailTrace_4014569
  have hstable : (prefixWord ++ tailWord_4014569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014569).length < 2 ^ (prefixWord ++ tailWord_4014569).sum := by decide
  have hdescent : baseEnd_4014569 < baseStart_4014569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014570 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_4014570 : Nat := 118140960795 + 4014570 * 2 ^ 59
def prefixEnd_4014570 : Nat := 4983230072969 + 3 ^ 40 * 4014570 * 2
def baseEnd_4014570 : Nat := 2061404031120463210112335

theorem tailTrace_4014570 : CollatzResearch.WordTrace tailWord_4014570 prefixEnd_4014570 2061404031120463210112335 := by
  unfold tailWord_4014570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36605849266476499703750291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97615598043937332543334109 36605849266476499703750291)
  ·
    refine ⟨54908773899714749555625437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36605849266476499703750291 54908773899714749555625437)
    ·
      refine ⟨20590790212393031083359539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54908773899714749555625437 20590790212393031083359539)
      ·
        refine ⟨30886185318589546625039309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20590790212393031083359539 30886185318589546625039309)
        ·
          refine ⟨11582319494471079984389741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30886185318589546625039309 11582319494471079984389741)
          ·
            refine ⟨4343369810426654994146153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11582319494471079984389741 4343369810426654994146153)
            ·
              refine ⟨3257527357819991245609615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4343369810426654994146153 3257527357819991245609615)
              ·
                refine ⟨4886291036729986868414423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3257527357819991245609615 4886291036729986868414423)
                ·
                  refine ⟨7329436555094980302621635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886291036729986868414423 7329436555094980302621635)
                  ·
                    refine ⟨10994154832642470453932453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7329436555094980302621635 10994154832642470453932453)
                    ·
                      refine ⟨2061404031120463210112335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10994154832642470453932453 2061404031120463210112335)
                      ·
                        rfl

theorem cell23_4014570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_4014570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014570 prefixEnd_4014570 := by exact prefixLift 4014570
  have htrace : WordTrace (prefixWord ++ tailWord_4014570) baseStart_4014570 baseEnd_4014570 := by
    simpa [prefixWord, tailWord_4014570, baseEnd_4014570] using wordTrace_append hprefix tailTrace_4014570
  have hstable : (prefixWord ++ tailWord_4014570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014570).length < 2 ^ (prefixWord ++ tailWord_4014570).sum := by decide
  have hdescent : baseEnd_4014570 < baseStart_4014570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014603 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 3]
def baseStart_4014603 : Nat := 118140960795 + 4014603 * 2 ^ 59
def prefixEnd_4014603 : Nat := 4983230072969 + 3 ^ 40 * 4014603 * 2
def baseEnd_4014603 : Nat := 2061420975982061580999683

theorem tailTrace_4014603 : CollatzResearch.WordTrace tailWord_4014603 prefixEnd_4014603 2061420975982061580999683 := by
  unfold tailWord_4014603
  simp only [CollatzResearch.WordTrace]
  refine ⟨146424600674786445450952463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97616400449857630300634975 146424600674786445450952463)
  ·
    refine ⟨219636901012179668176428695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146424600674786445450952463 219636901012179668176428695)
    ·
      refine ⟨329455351518269502264643043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219636901012179668176428695 329455351518269502264643043)
      ·
        refine ⟨494183027277404253396964565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329455351518269502264643043 494183027277404253396964565)
        ·
          refine ⟨11582414701814162188991357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 494183027277404253396964565 11582414701814162188991357)
          ·
            refine ⟨4343405513180310820871759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11582414701814162188991357 4343405513180310820871759)
            ·
              refine ⟨6515108269770466231307639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343405513180310820871759 6515108269770466231307639)
              ·
                refine ⟨9772662404655699346961459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6515108269770466231307639 9772662404655699346961459)
                ·
                  refine ⟨14658993606983549020442189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9772662404655699346961459 14658993606983549020442189)
                  ·
                    refine ⟨5497122602618830882665821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14658993606983549020442189 5497122602618830882665821)
                    ·
                      refine ⟨2061420975982061580999683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497122602618830882665821 2061420975982061580999683)
                      ·
                        rfl

theorem cell23_4014603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 3].length) (baseStart_4014603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014603 prefixEnd_4014603 := by exact prefixLift 4014603
  have htrace : WordTrace (prefixWord ++ tailWord_4014603) baseStart_4014603 baseEnd_4014603 := by
    simpa [prefixWord, tailWord_4014603, baseEnd_4014603] using wordTrace_append hprefix tailTrace_4014603
  have hstable : (prefixWord ++ tailWord_4014603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014603).length < 2 ^ (prefixWord ++ tailWord_4014603).sum := by decide
  have hdescent : baseEnd_4014603 < baseStart_4014603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014629 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_4014629 : Nat := 118140960795 + 4014629 * 2 ^ 59
def prefixEnd_4014629 : Nat := 4983230072969 + 3 ^ 40 * 4014629 * 2
def baseEnd_4014629 : Nat := 2061434326479078479274563

theorem tailTrace_4014629 : CollatzResearch.WordTrace tailWord_4014629 prefixEnd_4014629 2061434326479078479274563 := by
  unfold tailWord_4014629
  simp only [CollatzResearch.WordTrace]
  refine ⟨146425548972692251891398941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97617032648461501260932627 146425548972692251891398941)
  ·
    refine ⟨54909580864759594459274603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146425548972692251891398941 54909580864759594459274603)
    ·
      refine ⟨82364371297139391688911905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54909580864759594459274603 82364371297139391688911905)
      ·
        refine ⟨61773278472854543766683929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82364371297139391688911905 61773278472854543766683929)
        ·
          refine ⟨46329958854640907825012947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61773278472854543766683929 46329958854640907825012947)
          ·
            refine ⟨69494938281961361737519421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46329958854640907825012947 69494938281961361737519421)
            ·
              refine ⟨26060601855735510651569783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69494938281961361737519421 26060601855735510651569783)
              ·
                refine ⟨39090902783603265977354675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26060601855735510651569783 39090902783603265977354675)
                ·
                  refine ⟨58636354175404898966032013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39090902783603265977354675 58636354175404898966032013)
                  ·
                    refine ⟨21988632815776837112262005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58636354175404898966032013 21988632815776837112262005)
                    ·
                      refine ⟨2061434326479078479274563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21988632815776837112262005 2061434326479078479274563)
                      ·
                        rfl

theorem cell23_4014629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_4014629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014629 prefixEnd_4014629 := by exact prefixLift 4014629
  have htrace : WordTrace (prefixWord ++ tailWord_4014629) baseStart_4014629 baseEnd_4014629 := by
    simpa [prefixWord, tailWord_4014629, baseEnd_4014629] using wordTrace_append hprefix tailTrace_4014629
  have hstable : (prefixWord ++ tailWord_4014629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014629).length < 2 ^ (prefixWord ++ tailWord_4014629).sum := by decide
  have hdescent : baseEnd_4014629 < baseStart_4014629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014643 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 4, 2, 2]
def baseStart_4014643 : Nat := 118140960795 + 4014643 * 2 ^ 59
def prefixEnd_4014643 : Nat := 4983230072969 + 3 ^ 40 * 4014643 * 2
def baseEnd_4014643 : Nat := 2061441515208241424499499

theorem tailTrace_4014643 : CollatzResearch.WordTrace tailWord_4014643 prefixEnd_4014643 2061441515208241424499499 := by
  unfold tailWord_4014643
  simp only [CollatzResearch.WordTrace]
  refine ⟨146426059594641532282408583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97617373063094354854939055 146426059594641532282408583)
  ·
    refine ⟨219639089391962298423612875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146426059594641532282408583 219639089391962298423612875)
    ·
      refine ⟨329458634087943447635419313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219639089391962298423612875 329458634087943447635419313)
      ·
        refine ⟨247093975565957585726564485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329458634087943447635419313 247093975565957585726564485)
        ·
          refine ⟨46330120418617047323730841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247093975565957585726564485 46330120418617047323730841)
          ·
            refine ⟨34747590313962785492798131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46330120418617047323730841 34747590313962785492798131)
            ·
              refine ⟨52121385470944178239197197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34747590313962785492798131 52121385470944178239197197)
              ·
                refine ⟨19545519551604066839698949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52121385470944178239197197 19545519551604066839698949)
                ·
                  refine ⟨3664784915925762532443553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19545519551604066839698949 3664784915925762532443553)
                  ·
                    refine ⟨2748588686944321899332665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3664784915925762532443553 2748588686944321899332665)
                    ·
                      refine ⟨2061441515208241424499499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748588686944321899332665 2061441515208241424499499)
                      ·
                        rfl

theorem cell23_4014643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 2, 2].length) (baseStart_4014643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014643 prefixEnd_4014643 := by exact prefixLift 4014643
  have htrace : WordTrace (prefixWord ++ tailWord_4014643) baseStart_4014643 baseEnd_4014643 := by
    simpa [prefixWord, tailWord_4014643, baseEnd_4014643] using wordTrace_append hprefix tailTrace_4014643
  have hstable : (prefixWord ++ tailWord_4014643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014643).length < 2 ^ (prefixWord ++ tailWord_4014643).sum := by decide
  have hdescent : baseEnd_4014643 < baseStart_4014643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014710 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_4014710 : Nat := 118140960795 + 4014710 * 2 ^ 59
def prefixEnd_4014710 : Nat := 4983230072969 + 3 ^ 40 * 4014710 * 2
def baseEnd_4014710 : Nat := 2061475918412092662361691

theorem tailTrace_4014710 : CollatzResearch.WordTrace tailWord_4014710 prefixEnd_4014710 2061475918412092662361691 := by
  unfold tailWord_4014710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151781455337425170318599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97619002190265868483398389 9151781455337425170318599)
  ·
    refine ⟨13727672183006137755477899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9151781455337425170318599 13727672183006137755477899)
    ·
      refine ⟨20591508274509206633216849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13727672183006137755477899 20591508274509206633216849)
      ·
        refine ⟨15443631205881904974912637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20591508274509206633216849 15443631205881904974912637)
        ·
          refine ⟨5791361702205714365592239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15443631205881904974912637 5791361702205714365592239)
          ·
            refine ⟨8687042553308571548388359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791361702205714365592239 8687042553308571548388359)
            ·
              refine ⟨13030563829962857322582539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687042553308571548388359 13030563829962857322582539)
              ·
                refine ⟨19545845744944285983873809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13030563829962857322582539 19545845744944285983873809)
                ·
                  refine ⟨14659384308708214487905357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19545845744944285983873809 14659384308708214487905357)
                  ·
                    refine ⟨5497269115765580432964509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14659384308708214487905357 5497269115765580432964509)
                    ·
                      refine ⟨2061475918412092662361691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497269115765580432964509 2061475918412092662361691)
                      ·
                        rfl

theorem cell23_4014710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_4014710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014710 prefixEnd_4014710 := by exact prefixLift 4014710
  have htrace : WordTrace (prefixWord ++ tailWord_4014710) baseStart_4014710 baseEnd_4014710 := by
    simpa [prefixWord, tailWord_4014710, baseEnd_4014710] using wordTrace_append hprefix tailTrace_4014710
  have hstable : (prefixWord ++ tailWord_4014710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014710).length < 2 ^ (prefixWord ++ tailWord_4014710).sum := by decide
  have hdescent : baseEnd_4014710 < baseStart_4014710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014716 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_4014716 : Nat := 118140960795 + 4014716 * 2 ^ 59
def prefixEnd_4014716 : Nat := 4983230072969 + 3 ^ 40 * 4014716 * 2
def baseEnd_4014716 : Nat := 2061478999296019638886663

theorem tailTrace_4014716 : CollatzResearch.WordTrace tailWord_4014716 prefixEnd_4014716 2061478999296019638886663 := by
  unfold tailWord_4014716
  simp only [CollatzResearch.WordTrace]
  refine ⟨73214361061688532874908001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97619148082251377166544001 73214361061688532874908001)
  ·
    refine ⟨54910770796266399656181001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73214361061688532874908001 54910770796266399656181001)
    ·
      refine ⟨41183078097199799742135751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54910770796266399656181001 41183078097199799742135751)
      ·
        refine ⟨61774617145799699613203627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41183078097199799742135751 61774617145799699613203627)
        ·
          refine ⟨92661925718699549419805441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61774617145799699613203627 92661925718699549419805441)
          ·
            refine ⟨69496444289024662064854081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92661925718699549419805441 69496444289024662064854081)
            ·
              refine ⟨52122333216768496548640561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69496444289024662064854081 52122333216768496548640561)
              ·
                refine ⟨39091749912576372411480421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52122333216768496548640561 39091749912576372411480421)
                ·
                  refine ⟨7329703108608069827152579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39091749912576372411480421 7329703108608069827152579)
                  ·
                    refine ⟨10994554662912104740728869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7329703108608069827152579 10994554662912104740728869)
                    ·
                      refine ⟨2061478999296019638886663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10994554662912104740728869 2061478999296019638886663)
                      ·
                        rfl

theorem cell23_4014716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_4014716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014716 prefixEnd_4014716 := by exact prefixLift 4014716
  have htrace : WordTrace (prefixWord ++ tailWord_4014716) baseStart_4014716 baseEnd_4014716 := by
    simpa [prefixWord, tailWord_4014716, baseEnd_4014716] using wordTrace_append hprefix tailTrace_4014716
  have hstable : (prefixWord ++ tailWord_4014716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014716).length < 2 ^ (prefixWord ++ tailWord_4014716).sum := by decide
  have hdescent : baseEnd_4014716 < baseStart_4014716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014730 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_4014730 : Nat := 118140960795 + 4014730 * 2 ^ 59
def prefixEnd_4014730 : Nat := 4983230072969 + 3 ^ 40 * 4014730 * 2
def baseEnd_4014730 : Nat := 687162062675060861370533

theorem tailTrace_4014730 : CollatzResearch.WordTrace tailWord_4014730 prefixEnd_4014730 687162062675060861370533 := by
  unfold tailWord_4014730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36607308186331586535206411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97619488496884230760550429 36607308186331586535206411)
  ·
    refine ⟨54910962279497379802809617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36607308186331586535206411 54910962279497379802809617)
    ·
      refine ⟨41183221709623034852107213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54910962279497379802809617 41183221709623034852107213)
      ·
        refine ⟨15443708141108638069540205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41183221709623034852107213 15443708141108638069540205)
        ·
          refine ⟨5791390552915739276077577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15443708141108638069540205 5791390552915739276077577)
          ·
            refine ⟨4343542914686804457058183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5791390552915739276077577 4343542914686804457058183)
            ·
              refine ⟨6515314372030206685587275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343542914686804457058183 6515314372030206685587275)
              ·
                refine ⟨9772971558045310028380913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6515314372030206685587275 9772971558045310028380913)
                ·
                  refine ⟨7329728668533982521285685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9772971558045310028380913 7329728668533982521285685)
                  ·
                    refine ⟨687162062675060861370533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7329728668533982521285685 687162062675060861370533)
                    ·
                      rfl

theorem cell23_4014730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_4014730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014730 prefixEnd_4014730 := by exact prefixLift 4014730
  have htrace : WordTrace (prefixWord ++ tailWord_4014730) baseStart_4014730 baseEnd_4014730 := by
    simpa [prefixWord, tailWord_4014730, baseEnd_4014730] using wordTrace_append hprefix tailTrace_4014730
  have hstable : (prefixWord ++ tailWord_4014730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014730).length < 2 ^ (prefixWord ++ tailWord_4014730).sum := by decide
  have hdescent : baseEnd_4014730 < baseStart_4014730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014739 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 10]
def baseStart_4014739 : Nat := 118140960795 + 4014739 * 2 ^ 59
def prefixEnd_4014739 : Nat := 4983230072969 + 3 ^ 40 * 4014739 * 2
def baseEnd_4014739 : Nat := 229054534372341449877673

theorem tailTrace_4014739 : CollatzResearch.WordTrace tailWord_4014739 prefixEnd_4014739 229054534372341449877673 := by
  unfold tailWord_4014739
  simp only [CollatzResearch.WordTrace]
  refine ⟨146429561002293740677903271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97619707334862493785268847 146429561002293740677903271)
  ·
    refine ⟨219644341503440611016854907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146429561002293740677903271 219644341503440611016854907)
    ·
      refine ⟨329466512255160916525282361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219644341503440611016854907 329466512255160916525282361)
      ·
        refine ⟨247099884191370687393961771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329466512255160916525282361 247099884191370687393961771)
        ·
          refine ⟨370649826287056031090942657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247099884191370687393961771 370649826287056031090942657)
          ·
            refine ⟨277987369715292023318206993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370649826287056031090942657 277987369715292023318206993)
            ·
              refine ⟨208490527286469017488655245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277987369715292023318206993 208490527286469017488655245)
              ·
                refine ⟨78183947732425881558245717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208490527286469017488655245 78183947732425881558245717)
                ·
                  refine ⟨229054534372341449877673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 78183947732425881558245717 229054534372341449877673)
                  ·
                    rfl

theorem cell23_4014739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 10].length) (baseStart_4014739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014739 prefixEnd_4014739 := by exact prefixLift 4014739
  have htrace : WordTrace (prefixWord ++ tailWord_4014739) baseStart_4014739 baseEnd_4014739 := by
    simpa [prefixWord, tailWord_4014739, baseEnd_4014739] using wordTrace_append hprefix tailTrace_4014739
  have hstable : (prefixWord ++ tailWord_4014739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014739).length < 2 ^ (prefixWord ++ tailWord_4014739).sum := by decide
  have hdescent : baseEnd_4014739 < baseStart_4014739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014750 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_4014750 : Nat := 118140960795 + 4014750 * 2 ^ 59
def prefixEnd_4014750 : Nat := 4983230072969 + 3 ^ 40 * 4014750 * 2
def baseEnd_4014750 : Nat := 2061496457638272505861507

theorem tailTrace_4014750 : CollatzResearch.WordTrace tailWord_4014750 prefixEnd_4014750 2061496457638272505861507 := by
  unfold tailWord_4014750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18303745275656736194569213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97619974803502593037702469 18303745275656736194569213)
  ·
    refine ⟨6863904478371276072963455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18303745275656736194569213 6863904478371276072963455)
    ·
      refine ⟨10295856717556914109445183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6863904478371276072963455 10295856717556914109445183)
      ·
        refine ⟨15443785076335371164167775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10295856717556914109445183 15443785076335371164167775)
        ·
          refine ⟨23165677614503056746251663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15443785076335371164167775 23165677614503056746251663)
          ·
            refine ⟨34748516421754585119377495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23165677614503056746251663 34748516421754585119377495)
            ·
              refine ⟨52122774632631877679066243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34748516421754585119377495 52122774632631877679066243)
              ·
                refine ⟨78184161948947816518599365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52122774632631877679066243 78184161948947816518599365)
                ·
                  refine ⟨14659530365427715597237381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78184161948947816518599365 14659530365427715597237381)
                  ·
                    refine ⟨2748661943517696674482009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14659530365427715597237381 2748661943517696674482009)
                    ·
                      refine ⟨2061496457638272505861507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748661943517696674482009 2061496457638272505861507)
                      ·
                        rfl

theorem cell23_4014750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_4014750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014750 prefixEnd_4014750 := by exact prefixLift 4014750
  have htrace : WordTrace (prefixWord ++ tailWord_4014750) baseStart_4014750 baseEnd_4014750 := by
    simpa [prefixWord, tailWord_4014750, baseEnd_4014750] using wordTrace_append hprefix tailTrace_4014750
  have hstable : (prefixWord ++ tailWord_4014750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014750).length < 2 ^ (prefixWord ++ tailWord_4014750).sum := by decide
  have hdescent : baseEnd_4014750 < baseStart_4014750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014756 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 8]
def baseStart_4014756 : Nat := 118140960795 + 4014756 * 2 ^ 59
def prefixEnd_4014756 : Nat := 4983230072969 + 3 ^ 40 * 4014756 * 2
def baseEnd_4014756 : Nat := 229055504280244386931831

theorem tailTrace_4014756 : CollatzResearch.WordTrace tailWord_4014756 prefixEnd_4014756 229055504280244386931831 := by
  unfold tailWord_4014756
  simp only [CollatzResearch.WordTrace]
  refine ⟨73215090521616076290636061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97620120695488101720848081 73215090521616076290636061)
  ·
    refine ⟨27455658945606028608988523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73215090521616076290636061 27455658945606028608988523)
    ·
      refine ⟨41183488418409042913482785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27455658945606028608988523 41183488418409042913482785)
      ·
        refine ⟨30887616313806782185112089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41183488418409042913482785 30887616313806782185112089)
        ·
          refine ⟨23165712235355086638834067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30887616313806782185112089 23165712235355086638834067)
          ·
            refine ⟨34748568353032629958251101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23165712235355086638834067 34748568353032629958251101)
            ·
              refine ⟨13030713132387236234344163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34748568353032629958251101 13030713132387236234344163)
              ·
                refine ⟨19546069698580854351516245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13030713132387236234344163 19546069698580854351516245)
                ·
                  refine ⟨229055504280244386931831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19546069698580854351516245 229055504280244386931831)
                  ·
                    rfl

theorem cell23_4014756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_4014756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014756 prefixEnd_4014756 := by exact prefixLift 4014756
  have htrace : WordTrace (prefixWord ++ tailWord_4014756) baseStart_4014756 baseEnd_4014756 := by
    simpa [prefixWord, tailWord_4014756, baseEnd_4014756] using wordTrace_append hprefix tailTrace_4014756
  have hstable : (prefixWord ++ tailWord_4014756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014756).length < 2 ^ (prefixWord ++ tailWord_4014756).sum := by decide
  have hdescent : baseEnd_4014756 < baseStart_4014756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014793 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 8, 3, 2]
def baseStart_4014793 : Nat := 118140960795 + 4014793 * 2 ^ 59
def prefixEnd_4014793 : Nat := 4983230072969 + 3 ^ 40 * 4014793 * 2
def baseEnd_4014793 : Nat := 2061518537306415837623809

theorem tailTrace_4014793 : CollatzResearch.WordTrace tailWord_4014793 prefixEnd_4014793 2061518537306415837623809 := by
  unfold tailWord_4014793
  simp only [CollatzResearch.WordTrace]
  refine ⟨146431530544098107900369033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97621020362732071933579355 146431530544098107900369033)
  ·
    refine ⟨109823647908073580925276775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146431530544098107900369033 109823647908073580925276775)
    ·
      refine ⟨164735471862110371387915163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109823647908073580925276775 164735471862110371387915163)
      ·
        refine ⟨247103207793165557081872745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164735471862110371387915163 247103207793165557081872745)
        ·
          refine ⟨185327405844874167811404559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247103207793165557081872745 185327405844874167811404559)
          ·
            refine ⟨277991108767311251717106839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185327405844874167811404559 277991108767311251717106839)
            ·
              refine ⟨416986663150966877575660259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277991108767311251717106839 416986663150966877575660259)
              ·
                refine ⟨625479994726450316363490389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416986663150966877575660259 625479994726450316363490389)
                ·
                  refine ⟨7329843688200589644884653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 625479994726450316363490389 7329843688200589644884653)
                  ·
                    refine ⟨2748691383075221116831745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7329843688200589644884653 2748691383075221116831745)
                    ·
                      refine ⟨2061518537306415837623809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748691383075221116831745 2061518537306415837623809)
                      ·
                        rfl

theorem cell23_4014793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 3, 2].length) (baseStart_4014793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014793 prefixEnd_4014793 := by exact prefixLift 4014793
  have htrace : WordTrace (prefixWord ++ tailWord_4014793) baseStart_4014793 baseEnd_4014793 := by
    simpa [prefixWord, tailWord_4014793, baseEnd_4014793] using wordTrace_append hprefix tailTrace_4014793
  have hstable : (prefixWord ++ tailWord_4014793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014793).length < 2 ^ (prefixWord ++ tailWord_4014793).sum := by decide
  have hdescent : baseEnd_4014793 < baseStart_4014793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014810 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2]
def baseStart_4014810 : Nat := 118140960795 + 4014810 * 2 ^ 59
def prefixEnd_4014810 : Nat := 4983230072969 + 3 ^ 40 * 4014810 * 2
def baseEnd_4014810 : Nat := 2061527266477542271111231

theorem tailTrace_4014810 : CollatzResearch.WordTrace tailWord_4014810 prefixEnd_4014810 2061527266477542271111231 := by
  unfold tailWord_4014810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36608037646259129950934471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97621433723357679869158589 36608037646259129950934471)
  ·
    refine ⟨54912056469388694926401707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36608037646259129950934471 54912056469388694926401707)
    ·
      refine ⟨82368084704083042389602561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54912056469388694926401707 82368084704083042389602561)
      ·
        refine ⟨61776063528062281792201921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82368084704083042389602561 61776063528062281792201921)
        ·
          refine ⟨46332047646046711344151441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61776063528062281792201921 46332047646046711344151441)
          ·
            refine ⟨34749035734535033508113581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46332047646046711344151441 34749035734535033508113581)
            ·
              refine ⟨13030888400450637565542593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34749035734535033508113581 13030888400450637565542593)
              ·
                refine ⟨9773166300337978174156945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13030888400450637565542593 9773166300337978174156945)
                ·
                  refine ⟨7329874725253483630617709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9773166300337978174156945 7329874725253483630617709)
                  ·
                    refine ⟨2748703021970056361481641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7329874725253483630617709 2748703021970056361481641)
                    ·
                      refine ⟨2061527266477542271111231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748703021970056361481641 2061527266477542271111231)
                      ·
                        rfl

theorem cell23_4014810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_4014810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014810 prefixEnd_4014810 := by exact prefixLift 4014810
  have htrace : WordTrace (prefixWord ++ tailWord_4014810) baseStart_4014810 baseEnd_4014810 := by
    simpa [prefixWord, tailWord_4014810, baseEnd_4014810] using wordTrace_append hprefix tailTrace_4014810
  have hstable : (prefixWord ++ tailWord_4014810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014810).length < 2 ^ (prefixWord ++ tailWord_4014810).sum := by decide
  have hdescent : baseEnd_4014810 < baseStart_4014810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014817 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_4014817 : Nat := 118140960795 + 4014817 * 2 ^ 59
def prefixEnd_4014817 : Nat := 4983230072969 + 3 ^ 40 * 4014817 * 2
def baseEnd_4014817 : Nat := 2061530860842123743723699

theorem tailTrace_4014817 : CollatzResearch.WordTrace tailWord_4014817 prefixEnd_4014817 2061530860842123743723699 := by
  unfold tailWord_4014817
  simp only [CollatzResearch.WordTrace]
  refine ⟨146432405896011159999242705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97621603930674106666161803 146432405896011159999242705)
  ·
    refine ⟨109824304422008369999432029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146432405896011159999242705 109824304422008369999432029)
    ·
      refine ⟨41184114158253138749787011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109824304422008369999432029 41184114158253138749787011)
      ·
        refine ⟨61776171237379708124680517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41184114158253138749787011 61776171237379708124680517)
        ·
          refine ⟨11583032107008695273377597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61776171237379708124680517 11583032107008695273377597)
          ·
            refine ⟨4343637040128260727516599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11583032107008695273377597 4343637040128260727516599)
            ·
              refine ⟨6515455560192391091274899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343637040128260727516599 6515455560192391091274899)
              ·
                refine ⟨9773183340288586636912349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6515455560192391091274899 9773183340288586636912349)
                ·
                  refine ⟨3664943752608219988842131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9773183340288586636912349 3664943752608219988842131)
                  ·
                    refine ⟨5497415628912329983263197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3664943752608219988842131 5497415628912329983263197)
                    ·
                      refine ⟨2061530860842123743723699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497415628912329983263197 2061530860842123743723699)
                      ·
                        rfl

theorem cell23_4014817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_4014817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014817 prefixEnd_4014817 := by exact prefixLift 4014817
  have htrace : WordTrace (prefixWord ++ tailWord_4014817) baseStart_4014817 baseEnd_4014817 := by
    simpa [prefixWord, tailWord_4014817, baseEnd_4014817] using wordTrace_append hprefix tailTrace_4014817
  have hstable : (prefixWord ++ tailWord_4014817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014817).length < 2 ^ (prefixWord ++ tailWord_4014817).sum := by decide
  have hdescent : baseEnd_4014817 < baseStart_4014817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014840 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 5, 2, 2]
def baseStart_4014840 : Nat := 118140960795 + 4014840 * 2 ^ 59
def prefixEnd_4014840 : Nat := 4983230072969 + 3 ^ 40 * 4014840 * 2
def baseEnd_4014840 : Nat := 2061542670897177153736093

theorem tailTrace_4014840 : CollatzResearch.WordTrace tailWord_4014840 prefixEnd_4014840 2061542670897177153736093 := by
  unfold tailWord_4014840
  simp only [CollatzResearch.WordTrace]
  refine ⟨73216622387463917463664987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97622163183285223284886649 73216622387463917463664987)
  ·
    refine ⟨109824933581195876195497481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73216622387463917463664987 109824933581195876195497481)
    ·
      refine ⟨82368700185896907146623111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109824933581195876195497481 82368700185896907146623111)
      ·
        refine ⟨123553050278845360719934667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82368700185896907146623111 123553050278845360719934667)
        ·
          refine ⟨185329575418268041079902001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123553050278845360719934667 185329575418268041079902001)
          ·
            refine ⟨138997181563701030809926501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185329575418268041079902001 138997181563701030809926501)
            ·
              refine ⟨26061971543193943276861219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138997181563701030809926501 26061971543193943276861219)
              ·
                refine ⟨39092957314790914915291829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26061971543193943276861219 39092957314790914915291829)
                ·
                  refine ⟨3664964748261648273308609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39092957314790914915291829 3664964748261648273308609)
                  ·
                    refine ⟨2748723561196236204981457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3664964748261648273308609 2748723561196236204981457)
                    ·
                      refine ⟨2061542670897177153736093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748723561196236204981457 2061542670897177153736093)
                      ·
                        rfl

theorem cell23_4014840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_4014840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014840 prefixEnd_4014840 := by exact prefixLift 4014840
  have htrace : WordTrace (prefixWord ++ tailWord_4014840) baseStart_4014840 baseEnd_4014840 := by
    simpa [prefixWord, tailWord_4014840, baseEnd_4014840] using wordTrace_append hprefix tailTrace_4014840
  have hstable : (prefixWord ++ tailWord_4014840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014840).length < 2 ^ (prefixWord ++ tailWord_4014840).sum := by decide
  have hdescent : baseEnd_4014840 < baseStart_4014840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014850 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4014850 : Nat := 118140960795 + 4014850 * 2 ^ 59
def prefixEnd_4014850 : Nat := 4983230072969 + 3 ^ 40 * 4014850 * 2
def baseEnd_4014850 : Nat := 687182601901240704870349

theorem tailTrace_4014850 : CollatzResearch.WordTrace tailWord_4014850 prefixEnd_4014850 687182601901240704870349 := by
  unfold tailWord_4014850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36608402376222901658798501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97622406336594404423462669 36608402376222901658798501)
  ·
    refine ⟨6864075445541794061024719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36608402376222901658798501 6864075445541794061024719)
    ·
      refine ⟨10296113168312691091537079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6864075445541794061024719 10296113168312691091537079)
      ·
        refine ⟨15444169752469036637305619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10296113168312691091537079 15444169752469036637305619)
        ·
          refine ⟨23166254628703554955958429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15444169752469036637305619 23166254628703554955958429)
          ·
            refine ⟨8687345485763833108484411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23166254628703554955958429 8687345485763833108484411)
            ·
              refine ⟨13031018228645749662726617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687345485763833108484411 13031018228645749662726617)
              ·
                refine ⟨9773263671484312247044963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13031018228645749662726617 9773263671484312247044963)
                ·
                  refine ⟨14659895507226468370567445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9773263671484312247044963 14659895507226468370567445)
                  ·
                    refine ⟨687182601901240704870349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14659895507226468370567445 687182601901240704870349)
                    ·
                      rfl

theorem cell23_4014850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4014850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014850 prefixEnd_4014850 := by exact prefixLift 4014850
  have htrace : WordTrace (prefixWord ++ tailWord_4014850) baseStart_4014850 baseEnd_4014850 := by
    simpa [prefixWord, tailWord_4014850, baseEnd_4014850] using wordTrace_append hprefix tailTrace_4014850
  have hstable : (prefixWord ++ tailWord_4014850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014850).length < 2 ^ (prefixWord ++ tailWord_4014850).sum := by decide
  have hdescent : baseEnd_4014850 < baseStart_4014850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014874 : List Nat := [3, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2]
def baseStart_4014874 : Nat := 118140960795 + 4014874 * 2 ^ 59
def prefixEnd_4014874 : Nat := 4983230072969 + 3 ^ 40 * 4014874 * 2
def baseEnd_4014874 : Nat := 2061560129239430020710937

theorem tailTrace_4014874 : CollatzResearch.WordTrace tailWord_4014874 prefixEnd_4014874 2061560129239430020710937 := by
  unfold tailWord_4014874
  simp only [CollatzResearch.WordTrace]
  refine ⟨36608621214201164683516919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97622989904536439156045117 36608621214201164683516919)
  ·
    refine ⟨54912931821301747025275379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36608621214201164683516919 54912931821301747025275379)
    ·
      refine ⟨82369397731952620537913069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54912931821301747025275379 82369397731952620537913069)
      ·
        refine ⟨30888524149482232701717401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82369397731952620537913069 30888524149482232701717401)
        ·
          refine ⟨23166393112111674526288051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30888524149482232701717401 23166393112111674526288051)
          ·
            refine ⟨34749589668167511789432077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23166393112111674526288051 34749589668167511789432077)
            ·
              refine ⟨13031096125562816921037029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34749589668167511789432077 13031096125562816921037029)
              ·
                refine ⟨2443330523543028172694443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13031096125562816921037029 2443330523543028172694443)
                ·
                  refine ⟨3664995785314542259041665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443330523543028172694443 3664995785314542259041665)
                  ·
                    refine ⟨2748746838985906694281249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3664995785314542259041665 2748746838985906694281249)
                    ·
                      refine ⟨2061560129239430020710937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2748746838985906694281249 2061560129239430020710937)
                      ·
                        rfl

theorem cell23_4014874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_4014874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014874 prefixEnd_4014874 := by exact prefixLift 4014874
  have htrace : WordTrace (prefixWord ++ tailWord_4014874) baseStart_4014874 baseEnd_4014874 := by
    simpa [prefixWord, tailWord_4014874, baseEnd_4014874] using wordTrace_append hprefix tailTrace_4014874
  have hstable : (prefixWord ++ tailWord_4014874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014874).length < 2 ^ (prefixWord ++ tailWord_4014874).sum := by decide
  have hdescent : baseEnd_4014874 < baseStart_4014874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014918 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_4014918 : Nat := 118140960795 + 4014918 * 2 ^ 59
def prefixEnd_4014918 : Nat := 4983230072969 + 3 ^ 40 * 4014918 * 2
def baseEnd_4014918 : Nat := 687194240796075949520245

theorem tailTrace_4014918 : CollatzResearch.WordTrace tailWord_4014918 prefixEnd_4014918 687194240796075949520245 := by
  unfold tailWord_4014918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4576127802145164195270919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97624059779096836165779605 4576127802145164195270919)
  ·
    refine ⟨6864191703217746292906379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4576127802145164195270919 6864191703217746292906379)
    ·
      refine ⟨10296287554826619439359569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6864191703217746292906379 10296287554826619439359569)
      ·
        refine ⟨7722215666119964579519677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10296287554826619439359569 7722215666119964579519677)
        ·
          refine ⟨2895830874794986717319879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7722215666119964579519677 2895830874794986717319879)
          ·
            refine ⟨4343746312192480075979819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895830874794986717319879 4343746312192480075979819)
            ·
              refine ⟨6515619468288720113969729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343746312192480075979819 6515619468288720113969729)
              ·
                refine ⟨4886714601216540085477297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6515619468288720113969729 4886714601216540085477297)
                ·
                  refine ⟨3665035950912405064107973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4886714601216540085477297 3665035950912405064107973)
                  ·
                    refine ⟨687194240796075949520245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3665035950912405064107973 687194240796075949520245)
                    ·
                      rfl

theorem cell23_4014918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_4014918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014918 prefixEnd_4014918 := by exact prefixLift 4014918
  have htrace : WordTrace (prefixWord ++ tailWord_4014918) baseStart_4014918 baseEnd_4014918 := by
    simpa [prefixWord, tailWord_4014918, baseEnd_4014918] using wordTrace_append hprefix tailTrace_4014918
  have hstable : (prefixWord ++ tailWord_4014918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014918).length < 2 ^ (prefixWord ++ tailWord_4014918).sum := by decide
  have hdescent : baseEnd_4014918 < baseStart_4014918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014924 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 2, 1, 3]
def baseStart_4014924 : Nat := 118140960795 + 4014924 * 2 ^ 59
def prefixEnd_4014924 : Nat := 4983230072969 + 3 ^ 40 * 4014924 * 2
def baseEnd_4014924 : Nat := 2061585803272154825085707

theorem tailTrace_4014924 : CollatzResearch.WordTrace tailWord_4014924 prefixEnd_4014924 2061585803272154825085707 := by
  unfold tailWord_4014924
  simp only [CollatzResearch.WordTrace]
  refine ⟨73218154253311758636693913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97624205671082344848925217 73218154253311758636693913)
  ·
    refine ⟨54913615689983818977520435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73218154253311758636693913 54913615689983818977520435)
    ·
      refine ⟨82370423534975728466280653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54913615689983818977520435 82370423534975728466280653)
      ·
        refine ⟨30888908825615898174855245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82370423534975728466280653 30888908825615898174855245)
        ·
          refine ⟨11583340809605961815570717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30888908825615898174855245 11583340809605961815570717)
          ·
            refine ⟨4343752803602235680839019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11583340809605961815570717 4343752803602235680839019)
            ·
              refine ⟨6515629205403353521258529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343752803602235680839019 6515629205403353521258529)
              ·
                refine ⟨4886721904052515140943897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6515629205403353521258529 4886721904052515140943897)
                ·
                  refine ⟨3665041428039386355707923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4886721904052515140943897 3665041428039386355707923)
                  ·
                    refine ⟨5497562142059079533561885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3665041428039386355707923 5497562142059079533561885)
                    ·
                      refine ⟨2061585803272154825085707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5497562142059079533561885 2061585803272154825085707)
                      ·
                        rfl

theorem cell23_4014924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_4014924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014924 prefixEnd_4014924 := by exact prefixLift 4014924
  have htrace : WordTrace (prefixWord ++ tailWord_4014924) baseStart_4014924 baseEnd_4014924 := by
    simpa [prefixWord, tailWord_4014924, baseEnd_4014924] using wordTrace_append hprefix tailTrace_4014924
  have hstable : (prefixWord ++ tailWord_4014924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014924).length < 2 ^ (prefixWord ++ tailWord_4014924).sum := by decide
  have hdescent : baseEnd_4014924 < baseStart_4014924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014940 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_4014940 : Nat := 118140960795 + 4014940 * 2 ^ 59
def prefixEnd_4014940 : Nat := 4983230072969 + 3 ^ 40 * 4014940 * 2
def baseEnd_4014940 : Nat := 687198006320875587495211

theorem tailTrace_4014940 : CollatzResearch.WordTrace tailWord_4014940 prefixEnd_4014940 687198006320875587495211 := by
  unfold tailWord_4014940
  simp only [CollatzResearch.WordTrace]
  refine ⟨73218446037282776002985137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97624594716377034670646849 73218446037282776002985137)
  ·
    refine ⟨54913834527962082002238853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73218446037282776002985137 54913834527962082002238853)
    ·
      refine ⟨10296343973992890375419785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54913834527962082002238853 10296343973992890375419785)
      ·
        refine ⟨7722257980494667781564839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10296343973992890375419785 7722257980494667781564839)
        ·
          refine ⟨11583386970742001672347259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722257980494667781564839 11583386970742001672347259)
          ·
            refine ⟨17375080456113002508520889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11583386970742001672347259 17375080456113002508520889)
            ·
              refine ⟨13031310342084751881390667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17375080456113002508520889 13031310342084751881390667)
              ·
                refine ⟨19546965513127127822086001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13031310342084751881390667 19546965513127127822086001)
                ·
                  refine ⟨14660224134845345866564501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19546965513127127822086001 14660224134845345866564501)
                  ·
                    refine ⟨687198006320875587495211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14660224134845345866564501 687198006320875587495211)
                    ·
                      rfl

theorem cell23_4014940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_4014940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014940 prefixEnd_4014940 := by exact prefixLift 4014940
  have htrace : WordTrace (prefixWord ++ tailWord_4014940) baseStart_4014940 baseEnd_4014940 := by
    simpa [prefixWord, tailWord_4014940, baseEnd_4014940] using wordTrace_append hprefix tailTrace_4014940
  have hstable : (prefixWord ++ tailWord_4014940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014940).length < 2 ^ (prefixWord ++ tailWord_4014940).sum := by decide
  have hdescent : baseEnd_4014940 < baseStart_4014940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4014943 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_4014943 : Nat := 118140960795 + 4014943 * 2 ^ 59
def prefixEnd_4014943 : Nat := 4983230072969 + 3 ^ 40 * 4014943 * 2
def baseEnd_4014943 : Nat := 2061595559404590250748119

theorem tailTrace_4014943 : CollatzResearch.WordTrace tailWord_4014943 prefixEnd_4014943 2061595559404590250748119 := by
  unfold tailWord_4014943
  simp only [CollatzResearch.WordTrace]
  refine ⟨146437001493554683518329483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97624667662369789012219655 146437001493554683518329483)
  ·
    refine ⟨219655502240332025277494225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146437001493554683518329483 219655502240332025277494225)
    ·
      refine ⟨164741626680249018958120669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219655502240332025277494225 164741626680249018958120669)
      ·
        refine ⟨61778110005093382109295251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164741626680249018958120669 61778110005093382109295251)
        ·
          refine ⟨92667165007640073163942877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61778110005093382109295251 92667165007640073163942877)
          ·
            refine ⟨34750186877865027436478579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92667165007640073163942877 34750186877865027436478579)
            ·
              refine ⟨52125280316797541154717869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34750186877865027436478579 52125280316797541154717869)
              ·
                refine ⟨19546980118799077933019201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52125280316797541154717869 19546980118799077933019201)
                ·
                  refine ⟨14660235089099308449764401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19546980118799077933019201 14660235089099308449764401)
                  ·
                    refine ⟨10995176316824481337323301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14660235089099308449764401 10995176316824481337323301)
                    ·
                      refine ⟨2061595559404590250748119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10995176316824481337323301 2061595559404590250748119)
                      ·
                        rfl

theorem cell23_4014943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_4014943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4014943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4014943 prefixEnd_4014943 := by exact prefixLift 4014943
  have htrace : WordTrace (prefixWord ++ tailWord_4014943) baseStart_4014943 baseEnd_4014943 := by
    simpa [prefixWord, tailWord_4014943, baseEnd_4014943] using wordTrace_append hprefix tailTrace_4014943
  have hstable : (prefixWord ++ tailWord_4014943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4014943).length < 2 ^ (prefixWord ++ tailWord_4014943).sum := by decide
  have hdescent : baseEnd_4014943 < baseStart_4014943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4014943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
